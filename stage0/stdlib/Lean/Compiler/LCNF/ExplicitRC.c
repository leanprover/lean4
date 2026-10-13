// Lean compiler output
// Module: Lean.Compiler.LCNF.ExplicitRC
// Imports: public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.PrettyPrinter
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
uint8_t l_Lean_Compiler_LCNF_CtorInfo_isRef(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
extern lean_object* l_Lean_instInhabitedFVarIdHashSet;
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(lean_object*);
uint8_t l_Lean_Compiler_LCNF_LetValue_isPersistent(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedSignature_default___redArg();
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___redArg();
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__2(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "_private.Lean.Compiler.LCNF.ExplicitRC.0.Lean.Compiler.LCNF.collectResetTargets.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Compiler.LCNF.ExplicitRC"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets(lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedVarInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedVarInfo_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedVarInfo_default = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedVarInfo = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedVarInfo_default___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__1_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__2_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__3_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__4_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__5_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__0_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__1_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__7_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__2_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__3_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__4_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__8_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__8_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__6_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__0, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__12_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__13_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__1, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__12_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__14 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_insertBorrow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_insertLive(lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedDerivedValInfo = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default___closed__1_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "getInternal"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "get!Internal"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uget"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2_spec__4(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Data.DTreeMap.Internal.Queries"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.DTreeMap.Internal.Impl.Const.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Key is not present in map"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Compiler.LCNF.ExplicitRC.0.Lean.Compiler.LCNF.useLetValue"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__0_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateLetImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ugetBorrowed"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "get!InternalBorrowed"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "getInternalBorrowed"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 205, 20, 178, 155, 84, 168)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Compiler.LCNF.ExplicitRC.0.Lean.Compiler.LCNF.LetDecl.explicitRc"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "_private.Lean.Compiler.LCNF.ExplicitRC.0.Lean.Compiler.LCNF.Code.explicitRc"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_explicitRc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "explicitRc"};
static const lean_object* l_Lean_Compiler_LCNF_explicitRc___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_explicitRc___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_explicitRc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_explicitRc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 173, 65, 140, 38, 197, 53, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_explicitRc___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_explicitRc___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_explicitRc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_explicitRc___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_explicitRc___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_explicitRc___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_explicitRc___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_explicitRc;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_explicitRc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 132, 102, 171, 122, 154, 149, 18)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ExplicitRC"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 164, 3, 212, 141, 65, 76, 246)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(234, 211, 142, 143, 107, 33, 215, 207)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 250, 223, 192, 104, 128, 184, 149)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 253, 97, 148, 179, 46, 109, 198)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(184, 97, 91, 211, 31, 209, 125, 32)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 202, 70, 178, 192, 164, 153, 156)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 238, 44, 6, 75, 144, 17, 52)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 123, 124, 125, 95, 169, 195, 145)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 99, 255, 139, 23, 91, 187, 231)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 146, 98, 9, 226, 177, 155, 125)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 80, 138, 101, 161, 95, 63, 48)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__2(lean_object* v_msg_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = l_Lean_instInhabitedFVarIdHashSet;
v___x_3_ = lean_panic_fn_borrowed(v___x_2_, v_msg_1_);
return v___x_3_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(lean_object* v_a_4_, lean_object* v_x_5_){
_start:
{
if (lean_obj_tag(v_x_5_) == 0)
{
uint8_t v___x_6_; 
v___x_6_ = 0;
return v___x_6_;
}
else
{
lean_object* v_key_7_; lean_object* v_tail_8_; uint8_t v___x_9_; 
v_key_7_ = lean_ctor_get(v_x_5_, 0);
v_tail_8_ = lean_ctor_get(v_x_5_, 2);
v___x_9_ = l_Lean_instBEqFVarId_beq(v_key_7_, v_a_4_);
if (v___x_9_ == 0)
{
v_x_5_ = v_tail_8_;
goto _start;
}
else
{
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_11_, lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_11_, v_x_12_);
lean_dec(v_x_12_);
lean_dec(v_a_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
return v_x_15_;
}
else
{
lean_object* v_key_17_; lean_object* v_value_18_; lean_object* v_tail_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_42_; 
v_key_17_ = lean_ctor_get(v_x_16_, 0);
v_value_18_ = lean_ctor_get(v_x_16_, 1);
v_tail_19_ = lean_ctor_get(v_x_16_, 2);
v_isSharedCheck_42_ = !lean_is_exclusive(v_x_16_);
if (v_isSharedCheck_42_ == 0)
{
v___x_21_ = v_x_16_;
v_isShared_22_ = v_isSharedCheck_42_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_tail_19_);
lean_inc(v_value_18_);
lean_inc(v_key_17_);
lean_dec(v_x_16_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_42_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; uint64_t v___x_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v_fold_27_; uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; size_t v___x_31_; size_t v___x_32_; size_t v___x_33_; size_t v___x_34_; size_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_23_ = lean_array_get_size(v_x_15_);
v___x_24_ = l_Lean_instHashableFVarId_hash(v_key_17_);
v___x_25_ = 32ULL;
v___x_26_ = lean_uint64_shift_right(v___x_24_, v___x_25_);
v_fold_27_ = lean_uint64_xor(v___x_24_, v___x_26_);
v___x_28_ = 16ULL;
v___x_29_ = lean_uint64_shift_right(v_fold_27_, v___x_28_);
v___x_30_ = lean_uint64_xor(v_fold_27_, v___x_29_);
v___x_31_ = lean_uint64_to_usize(v___x_30_);
v___x_32_ = lean_usize_of_nat(v___x_23_);
v___x_33_ = ((size_t)1ULL);
v___x_34_ = lean_usize_sub(v___x_32_, v___x_33_);
v___x_35_ = lean_usize_land(v___x_31_, v___x_34_);
v___x_36_ = lean_array_uget_borrowed(v_x_15_, v___x_35_);
lean_inc(v___x_36_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 2, v___x_36_);
v___x_38_ = v___x_21_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_key_17_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v_value_18_);
lean_ctor_set(v_reuseFailAlloc_41_, 2, v___x_36_);
v___x_38_ = v_reuseFailAlloc_41_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; 
v___x_39_ = lean_array_uset(v_x_15_, v___x_35_, v___x_38_);
v_x_15_ = v___x_39_;
v_x_16_ = v_tail_19_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3___redArg(lean_object* v_i_43_, lean_object* v_source_44_, lean_object* v_target_45_){
_start:
{
lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_46_ = lean_array_get_size(v_source_44_);
v___x_47_ = lean_nat_dec_lt(v_i_43_, v___x_46_);
if (v___x_47_ == 0)
{
lean_dec_ref(v_source_44_);
lean_dec(v_i_43_);
return v_target_45_;
}
else
{
lean_object* v_es_48_; lean_object* v___x_49_; lean_object* v_source_50_; lean_object* v_target_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_es_48_ = lean_array_fget(v_source_44_, v_i_43_);
v___x_49_ = lean_box(0);
v_source_50_ = lean_array_fset(v_source_44_, v_i_43_, v___x_49_);
v_target_51_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5___redArg(v_target_45_, v_es_48_);
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_53_ = lean_nat_add(v_i_43_, v___x_52_);
lean_dec(v_i_43_);
v_i_43_ = v___x_53_;
v_source_44_ = v_source_50_;
v_target_45_ = v_target_51_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(lean_object* v_data_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v_nbuckets_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_56_ = lean_array_get_size(v_data_55_);
v___x_57_ = lean_unsigned_to_nat(2u);
v_nbuckets_58_ = lean_nat_mul(v___x_56_, v___x_57_);
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = lean_box(0);
v___x_61_ = lean_mk_array(v_nbuckets_58_, v___x_60_);
v___x_62_ = lean_array_propagate_mark(v_data_55_, v___x_61_);
v___x_63_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3___redArg(v___x_59_, v_data_55_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(lean_object* v_m_64_, lean_object* v_a_65_, lean_object* v_b_66_){
_start:
{
lean_object* v_size_67_; lean_object* v_buckets_68_; lean_object* v___x_69_; uint64_t v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v_fold_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; size_t v___x_77_; size_t v___x_78_; size_t v___x_79_; size_t v___x_80_; size_t v___x_81_; lean_object* v_bkt_82_; uint8_t v___x_83_; 
v_size_67_ = lean_ctor_get(v_m_64_, 0);
v_buckets_68_ = lean_ctor_get(v_m_64_, 1);
v___x_69_ = lean_array_get_size(v_buckets_68_);
v___x_70_ = l_Lean_instHashableFVarId_hash(v_a_65_);
v___x_71_ = 32ULL;
v___x_72_ = lean_uint64_shift_right(v___x_70_, v___x_71_);
v_fold_73_ = lean_uint64_xor(v___x_70_, v___x_72_);
v___x_74_ = 16ULL;
v___x_75_ = lean_uint64_shift_right(v_fold_73_, v___x_74_);
v___x_76_ = lean_uint64_xor(v_fold_73_, v___x_75_);
v___x_77_ = lean_uint64_to_usize(v___x_76_);
v___x_78_ = lean_usize_of_nat(v___x_69_);
v___x_79_ = ((size_t)1ULL);
v___x_80_ = lean_usize_sub(v___x_78_, v___x_79_);
v___x_81_ = lean_usize_land(v___x_77_, v___x_80_);
v_bkt_82_ = lean_array_uget_borrowed(v_buckets_68_, v___x_81_);
v___x_83_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_65_, v_bkt_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_104_; 
lean_inc_ref(v_buckets_68_);
lean_inc(v_size_67_);
v_isSharedCheck_104_ = !lean_is_exclusive(v_m_64_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; lean_object* v_unused_106_; 
v_unused_105_ = lean_ctor_get(v_m_64_, 1);
lean_dec(v_unused_105_);
v_unused_106_ = lean_ctor_get(v_m_64_, 0);
lean_dec(v_unused_106_);
v___x_85_ = v_m_64_;
v_isShared_86_ = v_isSharedCheck_104_;
goto v_resetjp_84_;
}
else
{
lean_dec(v_m_64_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_104_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v_size_x27_88_; lean_object* v___x_89_; lean_object* v_buckets_x27_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_87_ = lean_unsigned_to_nat(1u);
v_size_x27_88_ = lean_nat_add(v_size_67_, v___x_87_);
lean_dec(v_size_67_);
lean_inc(v_bkt_82_);
v___x_89_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_89_, 0, v_a_65_);
lean_ctor_set(v___x_89_, 1, v_b_66_);
lean_ctor_set(v___x_89_, 2, v_bkt_82_);
v_buckets_x27_90_ = lean_array_uset(v_buckets_68_, v___x_81_, v___x_89_);
v___x_91_ = lean_unsigned_to_nat(4u);
v___x_92_ = lean_nat_mul(v_size_x27_88_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(3u);
v___x_94_ = lean_nat_div(v___x_92_, v___x_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_array_get_size(v_buckets_x27_90_);
v___x_96_ = lean_nat_dec_le(v___x_94_, v___x_95_);
lean_dec(v___x_94_);
if (v___x_96_ == 0)
{
lean_object* v_val_97_; lean_object* v___x_99_; 
v_val_97_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(v_buckets_x27_90_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v_val_97_);
lean_ctor_set(v___x_85_, 0, v_size_x27_88_);
v___x_99_ = v___x_85_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_size_x27_88_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_val_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
else
{
lean_object* v___x_102_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v_buckets_x27_90_);
lean_ctor_set(v___x_85_, 0, v_size_x27_88_);
v___x_102_ = v___x_85_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_size_x27_88_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_buckets_x27_90_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
else
{
lean_dec(v_b_66_);
lean_dec(v_a_65_);
return v_m_64_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_110_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_111_ = lean_unsigned_to_nat(61u);
v___x_112_ = lean_unsigned_to_nat(49u);
v___x_113_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__1));
v___x_114_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_115_ = l_mkPanicMessageWithDecl(v___x_114_, v___x_113_, v___x_112_, v___x_111_, v___x_110_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(lean_object* v_code_116_, lean_object* v_s_117_){
_start:
{
switch(lean_obj_tag(v_code_116_))
{
case 0:
{
lean_object* v_decl_118_; lean_object* v_value_119_; 
v_decl_118_ = lean_ctor_get(v_code_116_, 0);
v_value_119_ = lean_ctor_get(v_decl_118_, 3);
if (lean_obj_tag(v_value_119_) == 11)
{
lean_object* v_k_120_; lean_object* v_var_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
lean_inc_ref(v_value_119_);
v_k_120_ = lean_ctor_get(v_code_116_, 1);
lean_inc_ref(v_k_120_);
lean_dec_ref_known(v_code_116_, 2);
v_var_121_ = lean_ctor_get(v_value_119_, 1);
lean_inc(v_var_121_);
lean_dec_ref_known(v_value_119_, 2);
v___x_122_ = lean_box(0);
v___x_123_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_s_117_, v_var_121_, v___x_122_);
v_code_116_ = v_k_120_;
v_s_117_ = v___x_123_;
goto _start;
}
else
{
lean_object* v_k_125_; 
v_k_125_ = lean_ctor_get(v_code_116_, 1);
lean_inc_ref(v_k_125_);
lean_dec_ref_known(v_code_116_, 2);
v_code_116_ = v_k_125_;
goto _start;
}
}
case 2:
{
lean_object* v_decl_127_; lean_object* v_k_128_; lean_object* v_value_129_; lean_object* v___x_130_; 
v_decl_127_ = lean_ctor_get(v_code_116_, 0);
lean_inc_ref(v_decl_127_);
v_k_128_ = lean_ctor_get(v_code_116_, 1);
lean_inc_ref(v_k_128_);
lean_dec_ref_known(v_code_116_, 2);
v_value_129_ = lean_ctor_get(v_decl_127_, 4);
lean_inc_ref(v_value_129_);
lean_dec_ref(v_decl_127_);
v___x_130_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(v_value_129_, v_s_117_);
v_code_116_ = v_k_128_;
v_s_117_ = v___x_130_;
goto _start;
}
case 3:
{
lean_dec_ref_known(v_code_116_, 2);
return v_s_117_;
}
case 4:
{
lean_object* v_cases_132_; lean_object* v_alts_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_cases_132_ = lean_ctor_get(v_code_116_, 0);
lean_inc_ref(v_cases_132_);
lean_dec_ref_known(v_code_116_, 1);
v_alts_133_ = lean_ctor_get(v_cases_132_, 3);
lean_inc_ref(v_alts_133_);
lean_dec_ref(v_cases_132_);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_array_get_size(v_alts_133_);
v___x_136_ = lean_nat_dec_lt(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
lean_dec_ref(v_alts_133_);
return v_s_117_;
}
else
{
uint8_t v___x_137_; 
v___x_137_ = lean_nat_dec_le(v___x_135_, v___x_135_);
if (v___x_137_ == 0)
{
if (v___x_136_ == 0)
{
lean_dec_ref(v_alts_133_);
return v_s_117_;
}
else
{
size_t v___x_138_; size_t v___x_139_; lean_object* v___x_140_; 
v___x_138_ = ((size_t)0ULL);
v___x_139_ = lean_usize_of_nat(v___x_135_);
v___x_140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(v_alts_133_, v___x_138_, v___x_139_, v_s_117_);
lean_dec_ref(v_alts_133_);
return v___x_140_;
}
}
else
{
size_t v___x_141_; size_t v___x_142_; lean_object* v___x_143_; 
v___x_141_ = ((size_t)0ULL);
v___x_142_ = lean_usize_of_nat(v___x_135_);
v___x_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(v_alts_133_, v___x_141_, v___x_142_, v_s_117_);
lean_dec_ref(v_alts_133_);
return v___x_143_;
}
}
}
case 5:
{
lean_dec_ref_known(v_code_116_, 1);
return v_s_117_;
}
case 6:
{
lean_dec_ref_known(v_code_116_, 1);
return v_s_117_;
}
case 8:
{
lean_object* v_k_144_; 
v_k_144_ = lean_ctor_get(v_code_116_, 3);
lean_inc_ref(v_k_144_);
lean_dec_ref_known(v_code_116_, 4);
v_code_116_ = v_k_144_;
goto _start;
}
case 9:
{
lean_object* v_k_146_; 
v_k_146_ = lean_ctor_get(v_code_116_, 5);
lean_inc_ref(v_k_146_);
lean_dec_ref_known(v_code_116_, 6);
v_code_116_ = v_k_146_;
goto _start;
}
default: 
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec_ref(v_s_117_);
lean_dec_ref(v_code_116_);
v___x_148_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3);
v___x_149_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__2(v___x_148_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(lean_object* v_as_150_, size_t v_i_151_, size_t v_stop_152_, lean_object* v_b_153_){
_start:
{
lean_object* v___y_155_; uint8_t v___x_160_; 
v___x_160_ = lean_usize_dec_eq(v_i_151_, v_stop_152_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
v___x_161_ = lean_array_uget_borrowed(v_as_150_, v_i_151_);
switch(lean_obj_tag(v___x_161_))
{
case 0:
{
lean_object* v_code_162_; 
v_code_162_ = lean_ctor_get(v___x_161_, 2);
lean_inc_ref(v_code_162_);
v___y_155_ = v_code_162_;
goto v___jp_154_;
}
case 1:
{
lean_object* v_code_163_; 
v_code_163_ = lean_ctor_get(v___x_161_, 1);
lean_inc_ref(v_code_163_);
v___y_155_ = v_code_163_;
goto v___jp_154_;
}
default: 
{
lean_object* v_code_164_; 
v_code_164_ = lean_ctor_get(v___x_161_, 0);
lean_inc_ref(v_code_164_);
v___y_155_ = v_code_164_;
goto v___jp_154_;
}
}
}
else
{
return v_b_153_;
}
v___jp_154_:
{
lean_object* v___x_156_; size_t v___x_157_; size_t v___x_158_; 
v___x_156_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(v___y_155_, v_b_153_);
v___x_157_ = ((size_t)1ULL);
v___x_158_ = lean_usize_add(v_i_151_, v___x_157_);
v_i_151_ = v___x_158_;
v_b_153_ = v___x_156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1___boxed(lean_object* v_as_165_, lean_object* v_i_166_, lean_object* v_stop_167_, lean_object* v_b_168_){
_start:
{
size_t v_i_boxed_169_; size_t v_stop_boxed_170_; lean_object* v_res_171_; 
v_i_boxed_169_ = lean_unbox_usize(v_i_166_);
lean_dec(v_i_166_);
v_stop_boxed_170_ = lean_unbox_usize(v_stop_167_);
lean_dec(v_stop_167_);
v_res_171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(v_as_165_, v_i_boxed_169_, v_stop_boxed_170_, v_b_168_);
lean_dec_ref(v_as_165_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0(lean_object* v_00_u03b2_172_, lean_object* v_m_173_, lean_object* v_a_174_, lean_object* v_b_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_m_173_, v_a_174_, v_b_175_);
return v___x_176_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0(lean_object* v_00_u03b2_177_, lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_178_, v_x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_181_, lean_object* v_a_182_, lean_object* v_x_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0(v_00_u03b2_181_, v_a_182_, v_x_183_);
lean_dec(v_x_183_);
lean_dec(v_a_182_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1(lean_object* v_00_u03b2_186_, lean_object* v_data_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(v_data_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_189_, lean_object* v_i_190_, lean_object* v_source_191_, lean_object* v_target_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3___redArg(v_i_190_, v_source_191_, v_target_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5___redArg(v_x_195_, v_x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets(lean_object* v_code_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_200_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(v_code_198_, v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_box(0);
v___x_208_ = lean_unsigned_to_nat(16u);
v___x_209_ = lean_mk_array(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
return v___x_215_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars(void){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__0(lean_object* v___x_217_, lean_object* v___x_218_, lean_object* v_a_219_, lean_object* v_b_220_, lean_object* v_acc_221_){
_start:
{
lean_object* v_r_222_; lean_object* v___x_223_; 
v_r_222_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_217_, v___x_218_, v_acc_221_, v_a_219_, v_b_220_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v_r_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__1(lean_object* v___x_224_, lean_object* v___f_225_, lean_object* v_a_226_, lean_object* v_x_227_, lean_object* v___y_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_224_, v___f_225_, v_a_226_, v___y_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union(lean_object* v_liveVars1_259_, lean_object* v_liveVars2_260_){
_start:
{
lean_object* v_vars_261_; lean_object* v_borrows_262_; lean_object* v_vars_263_; lean_object* v_borrows_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_299_; 
v_vars_261_ = lean_ctor_get(v_liveVars1_259_, 0);
lean_inc_ref(v_vars_261_);
v_borrows_262_ = lean_ctor_get(v_liveVars1_259_, 1);
lean_inc_ref(v_borrows_262_);
lean_dec_ref(v_liveVars1_259_);
v_vars_263_ = lean_ctor_get(v_liveVars2_260_, 0);
v_borrows_264_ = lean_ctor_get(v_liveVars2_260_, 1);
v_isSharedCheck_299_ = !lean_is_exclusive(v_liveVars2_260_);
if (v_isSharedCheck_299_ == 0)
{
v___x_266_ = v_liveVars2_260_;
v_isShared_267_ = v_isSharedCheck_299_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_borrows_264_);
lean_inc(v_vars_263_);
lean_dec(v_liveVars2_260_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_299_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v_size_269_; lean_object* v_buckets_270_; lean_object* v_size_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___y_275_; uint8_t v___x_292_; 
v___x_268_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v_size_269_ = lean_ctor_get(v_vars_261_, 0);
v_buckets_270_ = lean_ctor_get(v_vars_261_, 1);
v_size_271_ = lean_ctor_get(v_vars_263_, 0);
v___x_272_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_273_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_292_ = lean_nat_dec_le(v_size_269_, v_size_271_);
if (v___x_292_ == 0)
{
lean_object* v___f_293_; lean_object* v___x_294_; 
v___f_293_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__13));
v___x_294_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_293_, v___x_272_, v___x_273_, v_vars_261_, v_vars_263_);
v___y_275_ = v___x_294_;
goto v___jp_274_;
}
else
{
lean_object* v___f_295_; size_t v_sz_296_; size_t v___x_297_; lean_object* v___x_298_; 
lean_inc_ref(v_buckets_270_);
lean_dec_ref(v_vars_261_);
v___f_295_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__14));
v_sz_296_ = lean_array_size(v_buckets_270_);
v___x_297_ = ((size_t)0ULL);
v___x_298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_268_, v_buckets_270_, v___f_295_, v_sz_296_, v___x_297_, v_vars_263_);
v___y_275_ = v___x_298_;
goto v___jp_274_;
}
v___jp_274_:
{
lean_object* v_size_276_; lean_object* v_buckets_277_; lean_object* v_size_278_; uint8_t v___x_279_; 
v_size_276_ = lean_ctor_get(v_borrows_262_, 0);
v_buckets_277_ = lean_ctor_get(v_borrows_262_, 1);
v_size_278_ = lean_ctor_get(v_borrows_264_, 0);
v___x_279_ = lean_nat_dec_le(v_size_276_, v_size_278_);
if (v___x_279_ == 0)
{
lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v___f_280_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__13));
v___x_281_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_280_, v___x_272_, v___x_273_, v_borrows_262_, v_borrows_264_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v___x_281_);
lean_ctor_set(v___x_266_, 0, v___y_275_);
v___x_283_ = v___x_266_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___y_275_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
else
{
lean_object* v___f_285_; size_t v_sz_286_; size_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
lean_inc_ref(v_buckets_277_);
lean_dec_ref(v_borrows_262_);
v___f_285_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__14));
v_sz_286_ = lean_array_size(v_buckets_277_);
v___x_287_ = ((size_t)0ULL);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_268_, v_buckets_277_, v___f_285_, v_sz_286_, v___x_287_, v_borrows_264_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v___x_288_);
lean_ctor_set(v___x_266_, 0, v___y_275_);
v___x_290_ = v___x_266_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___y_275_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_erase(lean_object* v_liveVars_300_, lean_object* v_fvarId_301_){
_start:
{
lean_object* v_vars_302_; lean_object* v_borrows_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_314_; 
v_vars_302_ = lean_ctor_get(v_liveVars_300_, 0);
v_borrows_303_ = lean_ctor_get(v_liveVars_300_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_liveVars_300_);
if (v_isSharedCheck_314_ == 0)
{
v___x_305_ = v_liveVars_300_;
v_isShared_306_ = v_isSharedCheck_314_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_borrows_303_);
lean_inc(v_vars_302_);
lean_dec(v_liveVars_300_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_314_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v_vars_309_; lean_object* v_borrows_310_; lean_object* v___x_312_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_308_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
lean_inc(v_fvarId_301_);
v_vars_309_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_307_, v___x_308_, v_vars_302_, v_fvarId_301_);
v_borrows_310_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_307_, v___x_308_, v_borrows_303_, v_fvarId_301_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v_borrows_310_);
lean_ctor_set(v___x_305_, 0, v_vars_309_);
v___x_312_ = v___x_305_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_vars_309_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_borrows_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_insertBorrow(lean_object* v_liveVars_315_, lean_object* v_fvarId_316_){
_start:
{
lean_object* v_vars_317_; lean_object* v_borrows_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_329_; 
v_vars_317_ = lean_ctor_get(v_liveVars_315_, 0);
v_borrows_318_ = lean_ctor_get(v_liveVars_315_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_liveVars_315_);
if (v_isSharedCheck_329_ == 0)
{
v___x_320_ = v_liveVars_315_;
v_isShared_321_ = v_isSharedCheck_329_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_borrows_318_);
lean_inc(v_vars_317_);
lean_dec(v_liveVars_315_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_329_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_322_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_323_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_324_ = lean_box(0);
v___x_325_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_322_, v___x_323_, v_borrows_318_, v_fvarId_316_, v___x_324_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_325_);
v___x_327_ = v___x_320_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_vars_317_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_insertLive(lean_object* v_liveVars_330_, lean_object* v_fvarId_331_){
_start:
{
lean_object* v_vars_332_; lean_object* v_borrows_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_344_; 
v_vars_332_ = lean_ctor_get(v_liveVars_330_, 0);
v_borrows_333_ = lean_ctor_get(v_liveVars_330_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_liveVars_330_);
if (v_isSharedCheck_344_ == 0)
{
v___x_335_ = v_liveVars_330_;
v_isShared_336_ = v_isSharedCheck_344_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_borrows_333_);
lean_inc(v_vars_332_);
lean_dec(v_liveVars_330_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_344_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_337_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_338_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_339_ = lean_box(0);
v___x_340_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_337_, v___x_338_, v_vars_332_, v_fvarId_331_, v___x_339_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_340_);
v___x_342_ = v___x_335_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_borrows_333_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(lean_object* v_fvarId_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_varMap_356_; lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_varMap_356_ = lean_ctor_get(v_a_354_, 3);
v___f_357_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_358_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_varMap_356_);
v___x_359_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_357_, v___x_358_, v_varMap_356_, v_fvarId_353_);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___boxed(lean_object* v_fvarId_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(v_fvarId_361_, v_a_362_);
lean_dec_ref(v_a_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(lean_object* v_fvarId_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_varMap_373_; lean_object* v___f_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_varMap_373_ = lean_ctor_get(v_a_366_, 3);
v___f_374_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_375_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_varMap_373_);
v___x_376_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_374_, v___x_375_, v_varMap_373_, v_fvarId_365_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___boxed(lean_object* v_fvarId_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(v_fvarId_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(lean_object* v_fvarId_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_jpLiveVarMap_390_; lean_object* v___f_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_jpLiveVarMap_390_ = lean_ctor_get(v_a_388_, 4);
v___f_391_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_392_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
lean_inc(v_jpLiveVarMap_390_);
v___x_393_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_391_, v___x_392_, v_jpLiveVarMap_390_, v_fvarId_387_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg___boxed(lean_object* v_fvarId_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(v_fvarId_395_, v_a_396_);
lean_dec_ref(v_a_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(lean_object* v_fvarId_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_jpLiveVarMap_407_; lean_object* v___f_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_jpLiveVarMap_407_ = lean_ctor_get(v_a_400_, 4);
v___f_408_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_409_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
lean_inc(v_jpLiveVarMap_407_);
v___x_410_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_408_, v___x_409_, v_jpLiveVarMap_407_, v_fvarId_399_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___boxed(lean_object* v_fvarId_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(v_fvarId_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg(lean_object* v_fvarId_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_vars_427_; uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_424_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_425_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_426_ = lean_st_ref_get(v_a_422_);
v_vars_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc_ref(v_vars_427_);
lean_dec(v___x_426_);
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_424_, v___x_425_, v_vars_427_, v_fvarId_421_);
lean_dec_ref(v_vars_427_);
v___x_429_ = lean_box(v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg___boxed(lean_object* v_fvarId_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg(v_fvarId_431_, v_a_432_);
lean_dec(v_a_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(lean_object* v_fvarId_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_vars_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_443_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_444_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_445_ = lean_st_ref_get(v_a_437_);
v_vars_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc_ref(v_vars_446_);
lean_dec(v___x_445_);
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_443_, v___x_444_, v_vars_446_, v_fvarId_435_);
lean_dec_ref(v_vars_446_);
v___x_448_ = lean_box(v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___boxed(lean_object* v_fvarId_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(v_fvarId_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(lean_object* v_fvarId_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_borrows_465_; uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_462_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_463_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_464_ = lean_st_ref_get(v_a_460_);
v_borrows_465_ = lean_ctor_get(v___x_464_, 1);
lean_inc_ref(v_borrows_465_);
lean_dec(v___x_464_);
v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_462_, v___x_463_, v_borrows_465_, v_fvarId_459_);
lean_dec_ref(v_borrows_465_);
v___x_467_ = lean_box(v___x_466_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg___boxed(lean_object* v_fvarId_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(v_fvarId_469_, v_a_470_);
lean_dec(v_a_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(lean_object* v_fvarId_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v_borrows_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_482_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_483_ = lean_st_ref_get(v_a_475_);
v_borrows_484_ = lean_ctor_get(v___x_483_, 1);
lean_inc_ref(v_borrows_484_);
lean_dec(v___x_483_);
v___x_485_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_481_, v___x_482_, v_borrows_484_, v_fvarId_473_);
lean_dec_ref(v_borrows_484_);
v___x_486_ = lean_box(v___x_485_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___boxed(lean_object* v_fvarId_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(v_fvarId_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(lean_object* v_f_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_500_ = lean_st_ref_take(v_a_498_);
v___x_501_ = lean_box(0);
v___x_502_ = lean_apply_1(v_f_497_, v___x_500_);
v___x_503_ = lean_st_ref_put(v_a_498_, v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_501_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg___boxed(lean_object* v_f_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(v_f_505_, v_a_506_);
lean_dec(v_a_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(lean_object* v_f_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_517_ = lean_st_ref_take(v_a_511_);
v___x_518_ = lean_box(0);
v___x_519_ = lean_apply_1(v_f_509_, v___x_517_);
v___x_520_ = lean_st_ref_put(v_a_511_, v___x_519_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_518_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___boxed(lean_object* v_f_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(v_f_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(lean_object* v_child_531_, lean_object* v_k_532_, lean_object* v_t_533_){
_start:
{
if (lean_obj_tag(v_t_533_) == 0)
{
lean_object* v_size_534_; lean_object* v_k_535_; lean_object* v_v_536_; lean_object* v_l_537_; lean_object* v_r_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_564_; 
v_size_534_ = lean_ctor_get(v_t_533_, 0);
v_k_535_ = lean_ctor_get(v_t_533_, 1);
v_v_536_ = lean_ctor_get(v_t_533_, 2);
v_l_537_ = lean_ctor_get(v_t_533_, 3);
v_r_538_ = lean_ctor_get(v_t_533_, 4);
v_isSharedCheck_564_ = !lean_is_exclusive(v_t_533_);
if (v_isSharedCheck_564_ == 0)
{
v___x_540_ = v_t_533_;
v_isShared_541_ = v_isSharedCheck_564_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_r_538_);
lean_inc(v_l_537_);
lean_inc(v_v_536_);
lean_inc(v_k_535_);
lean_inc(v_size_534_);
lean_dec(v_t_533_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_564_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
uint8_t v___x_542_; 
v___x_542_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_532_, v_k_535_);
switch(v___x_542_)
{
case 0:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(v_child_531_, v_k_532_, v_l_537_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 3, v___x_543_);
v___x_545_ = v___x_540_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_size_534_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_k_535_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_v_536_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_r_538_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
case 1:
{
lean_object* v_parents_547_; lean_object* v_children_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_559_; 
lean_dec(v_k_535_);
v_parents_547_ = lean_ctor_get(v_v_536_, 0);
v_children_548_ = lean_ctor_get(v_v_536_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_v_536_);
if (v_isSharedCheck_559_ == 0)
{
v___x_550_ = v_v_536_;
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_children_548_);
lean_inc(v_parents_547_);
lean_dec(v_v_536_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_552_, 0, v_child_531_);
lean_ctor_set(v___x_552_, 1, v_children_548_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_552_);
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_parents_547_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_552_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 2, v___x_554_);
lean_ctor_set(v___x_540_, 1, v_k_532_);
v___x_556_ = v___x_540_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_size_534_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_k_532_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_l_537_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_r_538_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
default: 
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(v_child_531_, v_k_532_, v_r_538_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 4, v___x_560_);
v___x_562_ = v___x_540_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_size_534_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_k_535_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_v_536_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_l_537_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
else
{
lean_dec(v_k_532_);
lean_dec(v_child_531_);
return v_t_533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(lean_object* v_child_565_, lean_object* v_as_566_, size_t v_i_567_, size_t v_stop_568_, lean_object* v_b_569_){
_start:
{
uint8_t v___x_570_; 
v___x_570_ = lean_usize_dec_eq(v_i_567_, v_stop_568_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; size_t v___x_573_; size_t v___x_574_; 
v___x_571_ = lean_array_uget_borrowed(v_as_566_, v_i_567_);
lean_inc(v___x_571_);
lean_inc(v_child_565_);
v___x_572_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(v_child_565_, v___x_571_, v_b_569_);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_567_, v___x_573_);
v_i_567_ = v___x_574_;
v_b_569_ = v___x_572_;
goto _start;
}
else
{
lean_dec(v_child_565_);
return v_b_569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3___boxed(lean_object* v_child_576_, lean_object* v_as_577_, lean_object* v_i_578_, lean_object* v_stop_579_, lean_object* v_b_580_){
_start:
{
size_t v_i_boxed_581_; size_t v_stop_boxed_582_; lean_object* v_res_583_; 
v_i_boxed_581_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_stop_boxed_582_ = lean_unbox_usize(v_stop_579_);
lean_dec(v_stop_579_);
v_res_583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(v_child_576_, v_as_577_, v_i_boxed_581_, v_stop_boxed_582_, v_b_580_);
lean_dec_ref(v_as_577_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(lean_object* v_k_584_, lean_object* v_v_585_, lean_object* v_t_586_){
_start:
{
if (lean_obj_tag(v_t_586_) == 0)
{
lean_object* v_size_587_; lean_object* v_k_588_; lean_object* v_v_589_; lean_object* v_l_590_; lean_object* v_r_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_871_; 
v_size_587_ = lean_ctor_get(v_t_586_, 0);
v_k_588_ = lean_ctor_get(v_t_586_, 1);
v_v_589_ = lean_ctor_get(v_t_586_, 2);
v_l_590_ = lean_ctor_get(v_t_586_, 3);
v_r_591_ = lean_ctor_get(v_t_586_, 4);
v_isSharedCheck_871_ = !lean_is_exclusive(v_t_586_);
if (v_isSharedCheck_871_ == 0)
{
v___x_593_ = v_t_586_;
v_isShared_594_ = v_isSharedCheck_871_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_r_591_);
lean_inc(v_l_590_);
lean_inc(v_v_589_);
lean_inc(v_k_588_);
lean_inc(v_size_587_);
lean_dec(v_t_586_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_871_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v___x_595_; 
v___x_595_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_584_, v_k_588_);
switch(v___x_595_)
{
case 0:
{
lean_object* v_impl_596_; lean_object* v___x_597_; 
lean_dec(v_size_587_);
v_impl_596_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_k_584_, v_v_585_, v_l_590_);
v___x_597_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_591_) == 0)
{
lean_object* v_size_598_; lean_object* v_size_599_; lean_object* v_k_600_; lean_object* v_v_601_; lean_object* v_l_602_; lean_object* v_r_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_size_598_ = lean_ctor_get(v_r_591_, 0);
v_size_599_ = lean_ctor_get(v_impl_596_, 0);
v_k_600_ = lean_ctor_get(v_impl_596_, 1);
v_v_601_ = lean_ctor_get(v_impl_596_, 2);
v_l_602_ = lean_ctor_get(v_impl_596_, 3);
v_r_603_ = lean_ctor_get(v_impl_596_, 4);
lean_inc(v_r_603_);
v___x_604_ = lean_unsigned_to_nat(3u);
v___x_605_ = lean_nat_mul(v___x_604_, v_size_598_);
v___x_606_ = lean_nat_dec_lt(v___x_605_, v_size_599_);
lean_dec(v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
lean_dec(v_r_603_);
v___x_607_ = lean_nat_add(v___x_597_, v_size_599_);
v___x_608_ = lean_nat_add(v___x_607_, v_size_598_);
lean_dec(v___x_607_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 3, v_impl_596_);
lean_ctor_set(v___x_593_, 0, v___x_608_);
v___x_610_ = v___x_593_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_impl_596_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_r_591_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
else
{
lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_677_; 
lean_inc(v_l_602_);
lean_inc(v_v_601_);
lean_inc(v_k_600_);
lean_inc(v_size_599_);
v_isSharedCheck_677_ = !lean_is_exclusive(v_impl_596_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; lean_object* v_unused_679_; lean_object* v_unused_680_; lean_object* v_unused_681_; lean_object* v_unused_682_; 
v_unused_678_ = lean_ctor_get(v_impl_596_, 4);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v_impl_596_, 3);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_impl_596_, 2);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_impl_596_, 1);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_impl_596_, 0);
lean_dec(v_unused_682_);
v___x_613_ = v_impl_596_;
v_isShared_614_ = v_isSharedCheck_677_;
goto v_resetjp_612_;
}
else
{
lean_dec(v_impl_596_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_677_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_size_615_; lean_object* v_size_616_; lean_object* v_k_617_; lean_object* v_v_618_; lean_object* v_l_619_; lean_object* v_r_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v_size_615_ = lean_ctor_get(v_l_602_, 0);
v_size_616_ = lean_ctor_get(v_r_603_, 0);
v_k_617_ = lean_ctor_get(v_r_603_, 1);
v_v_618_ = lean_ctor_get(v_r_603_, 2);
v_l_619_ = lean_ctor_get(v_r_603_, 3);
v_r_620_ = lean_ctor_get(v_r_603_, 4);
v___x_621_ = lean_unsigned_to_nat(2u);
v___x_622_ = lean_nat_mul(v___x_621_, v_size_615_);
v___x_623_ = lean_nat_dec_lt(v_size_616_, v___x_622_);
lean_dec(v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_652_; 
lean_inc(v_r_620_);
lean_inc(v_l_619_);
lean_inc(v_v_618_);
lean_inc(v_k_617_);
v_isSharedCheck_652_ = !lean_is_exclusive(v_r_603_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; lean_object* v_unused_654_; lean_object* v_unused_655_; lean_object* v_unused_656_; lean_object* v_unused_657_; 
v_unused_653_ = lean_ctor_get(v_r_603_, 4);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_r_603_, 3);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_r_603_, 2);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_r_603_, 1);
lean_dec(v_unused_656_);
v_unused_657_ = lean_ctor_get(v_r_603_, 0);
lean_dec(v_unused_657_);
v___x_625_ = v_r_603_;
v_isShared_626_ = v_isSharedCheck_652_;
goto v_resetjp_624_;
}
else
{
lean_dec(v_r_603_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_652_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___x_640_; lean_object* v___y_642_; 
v___x_627_ = lean_nat_add(v___x_597_, v_size_599_);
lean_dec(v_size_599_);
v___x_628_ = lean_nat_add(v___x_627_, v_size_598_);
lean_dec(v___x_627_);
v___x_640_ = lean_nat_add(v___x_597_, v_size_615_);
if (lean_obj_tag(v_l_619_) == 0)
{
lean_object* v_size_650_; 
v_size_650_ = lean_ctor_get(v_l_619_, 0);
lean_inc(v_size_650_);
v___y_642_ = v_size_650_;
goto v___jp_641_;
}
else
{
lean_object* v___x_651_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___y_642_ = v___x_651_;
goto v___jp_641_;
}
v___jp_629_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_nat_add(v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec(v___y_631_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v_r_591_);
lean_ctor_set(v___x_625_, 3, v_r_620_);
lean_ctor_set(v___x_625_, 2, v_v_589_);
lean_ctor_set(v___x_625_, 1, v_k_588_);
lean_ctor_set(v___x_625_, 0, v___x_633_);
v___x_635_ = v___x_625_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_r_620_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v_r_591_);
v___x_635_ = v_reuseFailAlloc_639_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 4, v___x_635_);
lean_ctor_set(v___x_613_, 3, v___y_630_);
lean_ctor_set(v___x_613_, 2, v_v_618_);
lean_ctor_set(v___x_613_, 1, v_k_617_);
lean_ctor_set(v___x_613_, 0, v___x_628_);
v___x_637_ = v___x_613_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v___y_630_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = lean_nat_add(v___x_640_, v___y_642_);
lean_dec(v___y_642_);
lean_dec(v___x_640_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 4, v_l_619_);
lean_ctor_set(v___x_593_, 3, v_l_602_);
lean_ctor_set(v___x_593_, 2, v_v_601_);
lean_ctor_set(v___x_593_, 1, v_k_600_);
lean_ctor_set(v___x_593_, 0, v___x_643_);
v___x_645_ = v___x_593_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_k_600_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_v_601_);
lean_ctor_set(v_reuseFailAlloc_649_, 3, v_l_602_);
lean_ctor_set(v_reuseFailAlloc_649_, 4, v_l_619_);
v___x_645_ = v_reuseFailAlloc_649_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; 
v___x_646_ = lean_nat_add(v___x_597_, v_size_598_);
if (lean_obj_tag(v_r_620_) == 0)
{
lean_object* v_size_647_; 
v_size_647_ = lean_ctor_get(v_r_620_, 0);
lean_inc(v_size_647_);
v___y_630_ = v___x_645_;
v___y_631_ = v___x_646_;
v___y_632_ = v_size_647_;
goto v___jp_629_;
}
else
{
lean_object* v___x_648_; 
v___x_648_ = lean_unsigned_to_nat(0u);
v___y_630_ = v___x_645_;
v___y_631_ = v___x_646_;
v___y_632_ = v___x_648_;
goto v___jp_629_;
}
}
}
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
lean_del_object(v___x_593_);
v___x_658_ = lean_nat_add(v___x_597_, v_size_599_);
lean_dec(v_size_599_);
v___x_659_ = lean_nat_add(v___x_658_, v_size_598_);
lean_dec(v___x_658_);
v___x_660_ = lean_nat_add(v___x_597_, v_size_598_);
v___x_661_ = lean_nat_add(v___x_660_, v_size_616_);
lean_dec(v___x_660_);
lean_inc_ref(v_r_591_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 4, v_r_591_);
lean_ctor_set(v___x_613_, 3, v_r_603_);
lean_ctor_set(v___x_613_, 2, v_v_589_);
lean_ctor_set(v___x_613_, 1, v_k_588_);
lean_ctor_set(v___x_613_, 0, v___x_661_);
v___x_663_ = v___x_613_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_r_603_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v_r_591_);
v___x_663_ = v_reuseFailAlloc_676_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
v_isSharedCheck_670_ = !lean_is_exclusive(v_r_591_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; lean_object* v_unused_672_; lean_object* v_unused_673_; lean_object* v_unused_674_; lean_object* v_unused_675_; 
v_unused_671_ = lean_ctor_get(v_r_591_, 4);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_r_591_, 3);
lean_dec(v_unused_672_);
v_unused_673_ = lean_ctor_get(v_r_591_, 2);
lean_dec(v_unused_673_);
v_unused_674_ = lean_ctor_get(v_r_591_, 1);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v_r_591_, 0);
lean_dec(v_unused_675_);
v___x_665_ = v_r_591_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_dec(v_r_591_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 4, v___x_663_);
lean_ctor_set(v___x_665_, 3, v_l_602_);
lean_ctor_set(v___x_665_, 2, v_v_601_);
lean_ctor_set(v___x_665_, 1, v_k_600_);
lean_ctor_set(v___x_665_, 0, v___x_659_);
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_k_600_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_v_601_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v_l_602_);
lean_ctor_set(v_reuseFailAlloc_669_, 4, v___x_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_683_; 
v_l_683_ = lean_ctor_get(v_impl_596_, 3);
if (lean_obj_tag(v_l_683_) == 0)
{
lean_object* v_r_684_; lean_object* v_k_685_; lean_object* v_v_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_697_; 
lean_inc_ref(v_l_683_);
v_r_684_ = lean_ctor_get(v_impl_596_, 4);
v_k_685_ = lean_ctor_get(v_impl_596_, 1);
v_v_686_ = lean_ctor_get(v_impl_596_, 2);
v_isSharedCheck_697_ = !lean_is_exclusive(v_impl_596_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; lean_object* v_unused_699_; 
v_unused_698_ = lean_ctor_get(v_impl_596_, 3);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_impl_596_, 0);
lean_dec(v_unused_699_);
v___x_688_ = v_impl_596_;
v_isShared_689_ = v_isSharedCheck_697_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_r_684_);
lean_inc(v_v_686_);
lean_inc(v_k_685_);
lean_dec(v_impl_596_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_697_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_684_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 3, v_r_684_);
lean_ctor_set(v___x_688_, 2, v_v_589_);
lean_ctor_set(v___x_688_, 1, v_k_588_);
lean_ctor_set(v___x_688_, 0, v___x_597_);
v___x_692_ = v___x_688_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_r_684_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v_r_684_);
v___x_692_ = v_reuseFailAlloc_696_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 4, v___x_692_);
lean_ctor_set(v___x_593_, 3, v_l_683_);
lean_ctor_set(v___x_593_, 2, v_v_686_);
lean_ctor_set(v___x_593_, 1, v_k_685_);
lean_ctor_set(v___x_593_, 0, v___x_690_);
v___x_694_ = v___x_593_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_k_685_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_v_686_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_l_683_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
else
{
lean_object* v_r_700_; 
v_r_700_ = lean_ctor_get(v_impl_596_, 4);
lean_inc(v_r_700_);
if (lean_obj_tag(v_r_700_) == 0)
{
lean_object* v_k_701_; lean_object* v_v_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_725_; 
lean_inc(v_l_683_);
v_k_701_ = lean_ctor_get(v_impl_596_, 1);
v_v_702_ = lean_ctor_get(v_impl_596_, 2);
v_isSharedCheck_725_ = !lean_is_exclusive(v_impl_596_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; lean_object* v_unused_727_; lean_object* v_unused_728_; 
v_unused_726_ = lean_ctor_get(v_impl_596_, 4);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_impl_596_, 3);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_impl_596_, 0);
lean_dec(v_unused_728_);
v___x_704_ = v_impl_596_;
v_isShared_705_ = v_isSharedCheck_725_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_v_702_);
lean_inc(v_k_701_);
lean_dec(v_impl_596_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_725_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_k_706_; lean_object* v_v_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_721_; 
v_k_706_ = lean_ctor_get(v_r_700_, 1);
v_v_707_ = lean_ctor_get(v_r_700_, 2);
v_isSharedCheck_721_ = !lean_is_exclusive(v_r_700_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; 
v_unused_722_ = lean_ctor_get(v_r_700_, 4);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_r_700_, 3);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_r_700_, 0);
lean_dec(v_unused_724_);
v___x_709_ = v_r_700_;
v_isShared_710_ = v_isSharedCheck_721_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_v_707_);
lean_inc(v_k_706_);
lean_dec(v_r_700_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_721_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = lean_unsigned_to_nat(3u);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 4, v_l_683_);
lean_ctor_set(v___x_709_, 3, v_l_683_);
lean_ctor_set(v___x_709_, 2, v_v_702_);
lean_ctor_set(v___x_709_, 1, v_k_701_);
lean_ctor_set(v___x_709_, 0, v___x_597_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_k_701_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_v_702_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_l_683_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v_l_683_);
v___x_713_ = v_reuseFailAlloc_720_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 4, v_l_683_);
lean_ctor_set(v___x_704_, 2, v_v_589_);
lean_ctor_set(v___x_704_, 1, v_k_588_);
lean_ctor_set(v___x_704_, 0, v___x_597_);
v___x_715_ = v___x_704_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_l_683_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_l_683_);
v___x_715_ = v_reuseFailAlloc_719_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 4, v___x_715_);
lean_ctor_set(v___x_593_, 3, v___x_713_);
lean_ctor_set(v___x_593_, 2, v_v_707_);
lean_ctor_set(v___x_593_, 1, v_k_706_);
lean_ctor_set(v___x_593_, 0, v___x_711_);
v___x_717_ = v___x_593_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_k_706_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_v_707_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
}
else
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_unsigned_to_nat(2u);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 4, v_r_700_);
lean_ctor_set(v___x_593_, 3, v_impl_596_);
lean_ctor_set(v___x_593_, 0, v___x_729_);
v___x_731_ = v___x_593_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v_impl_596_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v_r_700_);
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
case 1:
{
lean_object* v___x_734_; 
lean_dec(v_v_589_);
lean_dec(v_k_588_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 2, v_v_585_);
lean_ctor_set(v___x_593_, 1, v_k_584_);
v___x_734_ = v___x_593_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_size_587_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_735_, 3, v_l_590_);
lean_ctor_set(v_reuseFailAlloc_735_, 4, v_r_591_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
default: 
{
lean_object* v_impl_736_; lean_object* v___x_737_; 
lean_dec(v_size_587_);
v_impl_736_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_k_584_, v_v_585_, v_r_591_);
v___x_737_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_590_) == 0)
{
lean_object* v_size_738_; lean_object* v_size_739_; lean_object* v_k_740_; lean_object* v_v_741_; lean_object* v_l_742_; lean_object* v_r_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_size_738_ = lean_ctor_get(v_l_590_, 0);
v_size_739_ = lean_ctor_get(v_impl_736_, 0);
v_k_740_ = lean_ctor_get(v_impl_736_, 1);
v_v_741_ = lean_ctor_get(v_impl_736_, 2);
v_l_742_ = lean_ctor_get(v_impl_736_, 3);
lean_inc(v_l_742_);
v_r_743_ = lean_ctor_get(v_impl_736_, 4);
v___x_744_ = lean_unsigned_to_nat(3u);
v___x_745_ = lean_nat_mul(v___x_744_, v_size_738_);
v___x_746_ = lean_nat_dec_lt(v___x_745_, v_size_739_);
lean_dec(v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
lean_dec(v_l_742_);
v___x_747_ = lean_nat_add(v___x_737_, v_size_738_);
v___x_748_ = lean_nat_add(v___x_747_, v_size_739_);
lean_dec(v___x_747_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 4, v_impl_736_);
lean_ctor_set(v___x_593_, 0, v___x_748_);
v___x_750_ = v___x_593_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_l_590_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v_impl_736_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_815_; 
lean_inc(v_r_743_);
lean_inc(v_v_741_);
lean_inc(v_k_740_);
lean_inc(v_size_739_);
v_isSharedCheck_815_ = !lean_is_exclusive(v_impl_736_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; lean_object* v_unused_817_; lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; 
v_unused_816_ = lean_ctor_get(v_impl_736_, 4);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_impl_736_, 3);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_impl_736_, 2);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_impl_736_, 1);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_impl_736_, 0);
lean_dec(v_unused_820_);
v___x_753_ = v_impl_736_;
v_isShared_754_ = v_isSharedCheck_815_;
goto v_resetjp_752_;
}
else
{
lean_dec(v_impl_736_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_815_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v_size_755_; lean_object* v_k_756_; lean_object* v_v_757_; lean_object* v_l_758_; lean_object* v_r_759_; lean_object* v_size_760_; lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_size_755_ = lean_ctor_get(v_l_742_, 0);
v_k_756_ = lean_ctor_get(v_l_742_, 1);
v_v_757_ = lean_ctor_get(v_l_742_, 2);
v_l_758_ = lean_ctor_get(v_l_742_, 3);
v_r_759_ = lean_ctor_get(v_l_742_, 4);
v_size_760_ = lean_ctor_get(v_r_743_, 0);
v___x_761_ = lean_unsigned_to_nat(2u);
v___x_762_ = lean_nat_mul(v___x_761_, v_size_760_);
v___x_763_ = lean_nat_dec_lt(v_size_755_, v___x_762_);
lean_dec(v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_791_; 
lean_inc(v_r_759_);
lean_inc(v_l_758_);
lean_inc(v_v_757_);
lean_inc(v_k_756_);
v_isSharedCheck_791_ = !lean_is_exclusive(v_l_742_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; lean_object* v_unused_793_; lean_object* v_unused_794_; lean_object* v_unused_795_; lean_object* v_unused_796_; 
v_unused_792_ = lean_ctor_get(v_l_742_, 4);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_l_742_, 3);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_l_742_, 2);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_l_742_, 1);
lean_dec(v_unused_795_);
v_unused_796_ = lean_ctor_get(v_l_742_, 0);
lean_dec(v_unused_796_);
v___x_765_ = v_l_742_;
v_isShared_766_ = v_isSharedCheck_791_;
goto v_resetjp_764_;
}
else
{
lean_dec(v_l_742_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_791_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_781_; 
v___x_767_ = lean_nat_add(v___x_737_, v_size_738_);
v___x_768_ = lean_nat_add(v___x_767_, v_size_739_);
lean_dec(v_size_739_);
if (lean_obj_tag(v_l_758_) == 0)
{
lean_object* v_size_789_; 
v_size_789_ = lean_ctor_get(v_l_758_, 0);
lean_inc(v_size_789_);
v___y_781_ = v_size_789_;
goto v___jp_780_;
}
else
{
lean_object* v___x_790_; 
v___x_790_ = lean_unsigned_to_nat(0u);
v___y_781_ = v___x_790_;
goto v___jp_780_;
}
v___jp_769_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = lean_nat_add(v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec(v___y_771_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 4, v_r_743_);
lean_ctor_set(v___x_765_, 3, v_r_759_);
lean_ctor_set(v___x_765_, 2, v_v_741_);
lean_ctor_set(v___x_765_, 1, v_k_740_);
lean_ctor_set(v___x_765_, 0, v___x_773_);
v___x_775_ = v___x_765_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_k_740_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_v_741_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_r_759_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_r_743_);
v___x_775_ = v_reuseFailAlloc_779_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 4, v___x_775_);
lean_ctor_set(v___x_753_, 3, v___y_770_);
lean_ctor_set(v___x_753_, 2, v_v_757_);
lean_ctor_set(v___x_753_, 1, v_k_756_);
lean_ctor_set(v___x_753_, 0, v___x_768_);
v___x_777_ = v___x_753_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_k_756_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_v_757_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v___y_770_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
v___jp_780_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_nat_add(v___x_767_, v___y_781_);
lean_dec(v___y_781_);
lean_dec(v___x_767_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 4, v_l_758_);
lean_ctor_set(v___x_593_, 0, v___x_782_);
v___x_784_ = v___x_593_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v_l_590_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v_l_758_);
v___x_784_ = v_reuseFailAlloc_788_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; 
v___x_785_ = lean_nat_add(v___x_737_, v_size_760_);
if (lean_obj_tag(v_r_759_) == 0)
{
lean_object* v_size_786_; 
v_size_786_ = lean_ctor_get(v_r_759_, 0);
lean_inc(v_size_786_);
v___y_770_ = v___x_784_;
v___y_771_ = v___x_785_;
v___y_772_ = v_size_786_;
goto v___jp_769_;
}
else
{
lean_object* v___x_787_; 
v___x_787_ = lean_unsigned_to_nat(0u);
v___y_770_ = v___x_784_;
v___y_771_ = v___x_785_;
v___y_772_ = v___x_787_;
goto v___jp_769_;
}
}
}
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_801_; 
lean_del_object(v___x_593_);
v___x_797_ = lean_nat_add(v___x_737_, v_size_738_);
v___x_798_ = lean_nat_add(v___x_797_, v_size_739_);
lean_dec(v_size_739_);
v___x_799_ = lean_nat_add(v___x_797_, v_size_755_);
lean_dec(v___x_797_);
lean_inc_ref(v_l_590_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 4, v_l_742_);
lean_ctor_set(v___x_753_, 3, v_l_590_);
lean_ctor_set(v___x_753_, 2, v_v_589_);
lean_ctor_set(v___x_753_, 1, v_k_588_);
lean_ctor_set(v___x_753_, 0, v___x_799_);
v___x_801_ = v___x_753_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_l_590_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_l_742_);
v___x_801_ = v_reuseFailAlloc_814_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
v_isSharedCheck_808_ = !lean_is_exclusive(v_l_590_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; lean_object* v_unused_810_; lean_object* v_unused_811_; lean_object* v_unused_812_; lean_object* v_unused_813_; 
v_unused_809_ = lean_ctor_get(v_l_590_, 4);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_l_590_, 3);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_l_590_, 2);
lean_dec(v_unused_811_);
v_unused_812_ = lean_ctor_get(v_l_590_, 1);
lean_dec(v_unused_812_);
v_unused_813_ = lean_ctor_get(v_l_590_, 0);
lean_dec(v_unused_813_);
v___x_803_ = v_l_590_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_dec(v_l_590_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 4, v_r_743_);
lean_ctor_set(v___x_803_, 3, v___x_801_);
lean_ctor_set(v___x_803_, 2, v_v_741_);
lean_ctor_set(v___x_803_, 1, v_k_740_);
lean_ctor_set(v___x_803_, 0, v___x_798_);
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_k_740_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_v_741_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v_r_743_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_821_; 
v_l_821_ = lean_ctor_get(v_impl_736_, 3);
lean_inc(v_l_821_);
if (lean_obj_tag(v_l_821_) == 0)
{
lean_object* v_r_822_; lean_object* v_k_823_; lean_object* v_v_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_847_; 
v_r_822_ = lean_ctor_get(v_impl_736_, 4);
v_k_823_ = lean_ctor_get(v_impl_736_, 1);
v_v_824_ = lean_ctor_get(v_impl_736_, 2);
v_isSharedCheck_847_ = !lean_is_exclusive(v_impl_736_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; lean_object* v_unused_849_; 
v_unused_848_ = lean_ctor_get(v_impl_736_, 3);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_impl_736_, 0);
lean_dec(v_unused_849_);
v___x_826_ = v_impl_736_;
v_isShared_827_ = v_isSharedCheck_847_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_r_822_);
lean_inc(v_v_824_);
lean_inc(v_k_823_);
lean_dec(v_impl_736_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_847_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_k_828_; lean_object* v_v_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_843_; 
v_k_828_ = lean_ctor_get(v_l_821_, 1);
v_v_829_ = lean_ctor_get(v_l_821_, 2);
v_isSharedCheck_843_ = !lean_is_exclusive(v_l_821_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; lean_object* v_unused_845_; lean_object* v_unused_846_; 
v_unused_844_ = lean_ctor_get(v_l_821_, 4);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_l_821_, 3);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_l_821_, 0);
lean_dec(v_unused_846_);
v___x_831_ = v_l_821_;
v_isShared_832_ = v_isSharedCheck_843_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_v_829_);
lean_inc(v_k_828_);
lean_dec(v_l_821_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_843_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_822_, 2);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 4, v_r_822_);
lean_ctor_set(v___x_831_, 3, v_r_822_);
lean_ctor_set(v___x_831_, 2, v_v_589_);
lean_ctor_set(v___x_831_, 1, v_k_588_);
lean_ctor_set(v___x_831_, 0, v___x_737_);
v___x_835_ = v___x_831_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_r_822_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_r_822_);
v___x_835_ = v_reuseFailAlloc_842_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_837_; 
lean_inc(v_r_822_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 3, v_r_822_);
lean_ctor_set(v___x_826_, 0, v___x_737_);
v___x_837_ = v___x_826_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_k_823_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_v_824_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v_r_822_);
lean_ctor_set(v_reuseFailAlloc_841_, 4, v_r_822_);
v___x_837_ = v_reuseFailAlloc_841_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_839_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 4, v___x_837_);
lean_ctor_set(v___x_593_, 3, v___x_835_);
lean_ctor_set(v___x_593_, 2, v_v_829_);
lean_ctor_set(v___x_593_, 1, v_k_828_);
lean_ctor_set(v___x_593_, 0, v___x_833_);
v___x_839_ = v___x_593_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_k_828_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_v_829_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
}
else
{
lean_object* v_r_850_; 
v_r_850_ = lean_ctor_get(v_impl_736_, 4);
lean_inc(v_r_850_);
if (lean_obj_tag(v_r_850_) == 0)
{
lean_object* v_k_851_; lean_object* v_v_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_863_; 
v_k_851_ = lean_ctor_get(v_impl_736_, 1);
v_v_852_ = lean_ctor_get(v_impl_736_, 2);
v_isSharedCheck_863_ = !lean_is_exclusive(v_impl_736_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; lean_object* v_unused_865_; lean_object* v_unused_866_; 
v_unused_864_ = lean_ctor_get(v_impl_736_, 4);
lean_dec(v_unused_864_);
v_unused_865_ = lean_ctor_get(v_impl_736_, 3);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_impl_736_, 0);
lean_dec(v_unused_866_);
v___x_854_ = v_impl_736_;
v_isShared_855_ = v_isSharedCheck_863_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_v_852_);
lean_inc(v_k_851_);
lean_dec(v_impl_736_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_863_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_unsigned_to_nat(3u);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 4, v_l_821_);
lean_ctor_set(v___x_854_, 2, v_v_589_);
lean_ctor_set(v___x_854_, 1, v_k_588_);
lean_ctor_set(v___x_854_, 0, v___x_737_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_862_, 3, v_l_821_);
lean_ctor_set(v_reuseFailAlloc_862_, 4, v_l_821_);
v___x_858_ = v_reuseFailAlloc_862_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_860_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 4, v_r_850_);
lean_ctor_set(v___x_593_, 3, v___x_858_);
lean_ctor_set(v___x_593_, 2, v_v_852_);
lean_ctor_set(v___x_593_, 1, v_k_851_);
lean_ctor_set(v___x_593_, 0, v___x_856_);
v___x_860_ = v___x_593_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_k_851_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_v_852_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v_r_850_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_867_ = lean_unsigned_to_nat(2u);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 4, v_impl_736_);
lean_ctor_set(v___x_593_, 3, v_r_850_);
lean_ctor_set(v___x_593_, 0, v___x_867_);
v___x_869_ = v___x_593_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_r_850_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_impl_736_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
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
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v_k_584_);
lean_ctor_set(v___x_873_, 2, v_v_585_);
lean_ctor_set(v___x_873_, 3, v_t_586_);
lean_ctor_set(v___x_873_, 4, v_t_586_);
return v___x_873_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(lean_object* v_m_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_buckets_876_; lean_object* v___x_877_; uint64_t v___x_878_; uint64_t v___x_879_; uint64_t v___x_880_; uint64_t v_fold_881_; uint64_t v___x_882_; uint64_t v___x_883_; uint64_t v___x_884_; size_t v___x_885_; size_t v___x_886_; size_t v___x_887_; size_t v___x_888_; size_t v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v_buckets_876_ = lean_ctor_get(v_m_874_, 1);
v___x_877_ = lean_array_get_size(v_buckets_876_);
v___x_878_ = l_Lean_instHashableFVarId_hash(v_a_875_);
v___x_879_ = 32ULL;
v___x_880_ = lean_uint64_shift_right(v___x_878_, v___x_879_);
v_fold_881_ = lean_uint64_xor(v___x_878_, v___x_880_);
v___x_882_ = 16ULL;
v___x_883_ = lean_uint64_shift_right(v_fold_881_, v___x_882_);
v___x_884_ = lean_uint64_xor(v_fold_881_, v___x_883_);
v___x_885_ = lean_uint64_to_usize(v___x_884_);
v___x_886_ = lean_usize_of_nat(v___x_877_);
v___x_887_ = ((size_t)1ULL);
v___x_888_ = lean_usize_sub(v___x_886_, v___x_887_);
v___x_889_ = lean_usize_land(v___x_885_, v___x_888_);
v___x_890_ = lean_array_uget_borrowed(v_buckets_876_, v___x_889_);
v___x_891_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_875_, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg___boxed(lean_object* v_m_892_, lean_object* v_a_893_){
_start:
{
uint8_t v_res_894_; lean_object* v_r_895_; 
v_res_894_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_m_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec_ref(v_m_892_);
v_r_895_ = lean_box(v_res_894_);
return v_r_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(lean_object* v_ctx_896_, lean_object* v_parents_897_, lean_object* v_child_898_){
_start:
{
lean_object* v_resetTargets_899_; lean_object* v_unconditionalBorrows_900_; lean_object* v_derivedValMap_901_; lean_object* v_varMap_902_; lean_object* v_jpLiveVarMap_903_; lean_object* v_idx_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_937_; 
v_resetTargets_899_ = lean_ctor_get(v_ctx_896_, 0);
v_unconditionalBorrows_900_ = lean_ctor_get(v_ctx_896_, 1);
v_derivedValMap_901_ = lean_ctor_get(v_ctx_896_, 2);
v_varMap_902_ = lean_ctor_get(v_ctx_896_, 3);
v_jpLiveVarMap_903_ = lean_ctor_get(v_ctx_896_, 4);
v_idx_904_ = lean_ctor_get(v_ctx_896_, 5);
v_isSharedCheck_937_ = !lean_is_exclusive(v_ctx_896_);
if (v_isSharedCheck_937_ == 0)
{
v___x_906_ = v_ctx_896_;
v_isShared_907_ = v_isSharedCheck_937_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_idx_904_);
lean_inc(v_jpLiveVarMap_903_);
lean_inc(v_varMap_902_);
lean_inc(v_derivedValMap_901_);
lean_inc(v_unconditionalBorrows_900_);
lean_inc(v_resetTargets_899_);
lean_dec(v_ctx_896_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_937_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v_derivedValMap_910_; uint8_t v___x_911_; 
v___x_908_ = lean_box(0);
lean_inc_ref(v_parents_897_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v_parents_897_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
lean_inc(v_child_898_);
v_derivedValMap_910_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_child_898_, v___x_909_, v_derivedValMap_901_);
v___x_911_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_resetTargets_899_, v_child_898_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_array_get_size(v_parents_897_);
v___x_914_ = lean_nat_dec_lt(v___x_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_916_; 
lean_dec(v_child_898_);
lean_dec_ref(v_parents_897_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 2, v_derivedValMap_910_);
v___x_916_ = v___x_906_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_resetTargets_899_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_unconditionalBorrows_900_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_derivedValMap_910_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_varMap_902_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v_jpLiveVarMap_903_);
lean_ctor_set(v_reuseFailAlloc_917_, 5, v_idx_904_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
else
{
uint8_t v___x_918_; 
v___x_918_ = lean_nat_dec_le(v___x_913_, v___x_913_);
if (v___x_918_ == 0)
{
if (v___x_914_ == 0)
{
lean_object* v___x_920_; 
lean_dec(v_child_898_);
lean_dec_ref(v_parents_897_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 2, v_derivedValMap_910_);
v___x_920_ = v___x_906_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_resetTargets_899_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_unconditionalBorrows_900_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_derivedValMap_910_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_varMap_902_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_jpLiveVarMap_903_);
lean_ctor_set(v_reuseFailAlloc_921_, 5, v_idx_904_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
else
{
size_t v___x_922_; size_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_922_ = ((size_t)0ULL);
v___x_923_ = lean_usize_of_nat(v___x_913_);
v___x_924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(v_child_898_, v_parents_897_, v___x_922_, v___x_923_, v_derivedValMap_910_);
lean_dec_ref(v_parents_897_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 2, v___x_924_);
v___x_926_ = v___x_906_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_resetTargets_899_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_unconditionalBorrows_900_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_varMap_902_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v_jpLiveVarMap_903_);
lean_ctor_set(v_reuseFailAlloc_927_, 5, v_idx_904_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
else
{
size_t v___x_928_; size_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_928_ = ((size_t)0ULL);
v___x_929_ = lean_usize_of_nat(v___x_913_);
v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(v_child_898_, v_parents_897_, v___x_928_, v___x_929_, v_derivedValMap_910_);
lean_dec_ref(v_parents_897_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 2, v___x_930_);
v___x_932_ = v___x_906_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_resetTargets_899_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_unconditionalBorrows_900_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_varMap_902_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v_jpLiveVarMap_903_);
lean_ctor_set(v_reuseFailAlloc_933_, 5, v_idx_904_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v___x_935_; 
lean_dec(v_child_898_);
lean_dec_ref(v_parents_897_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 2, v_derivedValMap_910_);
v___x_935_ = v___x_906_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_resetTargets_899_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_unconditionalBorrows_900_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_derivedValMap_910_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v_varMap_902_);
lean_ctor_set(v_reuseFailAlloc_936_, 4, v_jpLiveVarMap_903_);
lean_ctor_set(v_reuseFailAlloc_936_, 5, v_idx_904_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1(lean_object* v_00_u03b2_938_, lean_object* v_k_939_, lean_object* v_v_940_, lean_object* v_t_941_, lean_object* v_hl_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_k_939_, v_v_940_, v_t_941_);
return v___x_943_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2(lean_object* v_00_u03b2_944_, lean_object* v_m_945_, lean_object* v_a_946_){
_start:
{
uint8_t v___x_947_; 
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_m_945_, v_a_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___boxed(lean_object* v_00_u03b2_948_, lean_object* v_m_949_, lean_object* v_a_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2(v_00_u03b2_948_, v_m_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_m_949_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(lean_object* v_ctx_953_, lean_object* v_fvarId_954_){
_start:
{
lean_object* v_resetTargets_955_; lean_object* v_unconditionalBorrows_956_; lean_object* v_derivedValMap_957_; lean_object* v_varMap_958_; lean_object* v_jpLiveVarMap_959_; lean_object* v_idx_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
v_resetTargets_955_ = lean_ctor_get(v_ctx_953_, 0);
v_unconditionalBorrows_956_ = lean_ctor_get(v_ctx_953_, 1);
v_derivedValMap_957_ = lean_ctor_get(v_ctx_953_, 2);
v_varMap_958_ = lean_ctor_get(v_ctx_953_, 3);
v_jpLiveVarMap_959_ = lean_ctor_get(v_ctx_953_, 4);
v_idx_960_ = lean_ctor_get(v_ctx_953_, 5);
v_isSharedCheck_968_ = !lean_is_exclusive(v_ctx_953_);
if (v_isSharedCheck_968_ == 0)
{
v___x_962_ = v_ctx_953_;
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_idx_960_);
lean_inc(v_jpLiveVarMap_959_);
lean_inc(v_varMap_958_);
lean_inc(v_derivedValMap_957_);
lean_inc(v_unconditionalBorrows_956_);
lean_inc(v_resetTargets_955_);
lean_dec(v_ctx_953_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_964_, 0, v_fvarId_954_);
lean_ctor_set(v___x_964_, 1, v_unconditionalBorrows_956_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_resetTargets_955_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_derivedValMap_957_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_varMap_958_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_jpLiveVarMap_959_);
lean_ctor_set(v_reuseFailAlloc_967_, 5, v_idx_960_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(lean_object* v_t_969_, lean_object* v_k_970_){
_start:
{
if (lean_obj_tag(v_t_969_) == 0)
{
lean_object* v_k_971_; lean_object* v_v_972_; lean_object* v_l_973_; lean_object* v_r_974_; uint8_t v___x_975_; 
v_k_971_ = lean_ctor_get(v_t_969_, 1);
v_v_972_ = lean_ctor_get(v_t_969_, 2);
v_l_973_ = lean_ctor_get(v_t_969_, 3);
v_r_974_ = lean_ctor_get(v_t_969_, 4);
v___x_975_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_970_, v_k_971_);
switch(v___x_975_)
{
case 0:
{
v_t_969_ = v_l_973_;
goto _start;
}
case 1:
{
lean_object* v___x_977_; 
lean_inc(v_v_972_);
v___x_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_977_, 0, v_v_972_);
return v___x_977_;
}
default: 
{
v_t_969_ = v_r_974_;
goto _start;
}
}
}
else
{
lean_object* v___x_979_; 
v___x_979_ = lean_box(0);
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg___boxed(lean_object* v_t_980_, lean_object* v_k_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_t_980_, v_k_981_);
lean_dec(v_k_981_);
lean_dec(v_t_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(lean_object* v_ctx_983_, lean_object* v_as_984_, size_t v_i_985_, size_t v_stop_986_, lean_object* v_b_987_){
_start:
{
lean_object* v___y_989_; uint8_t v___x_993_; 
v___x_993_ = lean_usize_dec_eq(v_i_985_, v_stop_986_);
if (v___x_993_ == 0)
{
lean_object* v_varMap_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_varMap_994_ = lean_ctor_get(v_ctx_983_, 3);
v___x_995_ = lean_array_uget_borrowed(v_as_984_, v_i_985_);
v___x_996_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_varMap_994_, v___x_995_);
if (lean_obj_tag(v___x_996_) == 0)
{
v___y_989_ = v_b_987_;
goto v___jp_988_;
}
else
{
lean_object* v_val_997_; uint8_t v_isPossibleRef_998_; 
v_val_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_val_997_);
lean_dec_ref_known(v___x_996_, 1);
v_isPossibleRef_998_ = lean_ctor_get_uint8(v_val_997_, sizeof(void*)*2);
lean_dec(v_val_997_);
if (v_isPossibleRef_998_ == 0)
{
v___y_989_ = v_b_987_;
goto v___jp_988_;
}
else
{
lean_object* v___x_999_; 
lean_inc(v___x_995_);
v___x_999_ = lean_array_push(v_b_987_, v___x_995_);
v___y_989_ = v___x_999_;
goto v___jp_988_;
}
}
}
else
{
return v_b_987_;
}
v___jp_988_:
{
size_t v___x_990_; size_t v___x_991_; 
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_add(v_i_985_, v___x_990_);
v_i_985_ = v___x_991_;
v_b_987_ = v___y_989_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1___boxed(lean_object* v_ctx_1000_, lean_object* v_as_1001_, lean_object* v_i_1002_, lean_object* v_stop_1003_, lean_object* v_b_1004_){
_start:
{
size_t v_i_boxed_1005_; size_t v_stop_boxed_1006_; lean_object* v_res_1007_; 
v_i_boxed_1005_ = lean_unbox_usize(v_i_1002_);
lean_dec(v_i_1002_);
v_stop_boxed_1006_ = lean_unbox_usize(v_stop_1003_);
lean_dec(v_stop_1003_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(v_ctx_1000_, v_as_1001_, v_i_boxed_1005_, v_stop_boxed_1006_, v_b_1004_);
lean_dec_ref(v_as_1001_);
lean_dec_ref(v_ctx_1000_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(lean_object* v_ctx_1010_, lean_object* v_parents_1011_, lean_object* v_decl_1012_){
_start:
{
lean_object* v_fvarId_1013_; lean_object* v_type_1014_; uint8_t v___x_1015_; 
v_fvarId_1013_ = lean_ctor_get(v_decl_1012_, 0);
lean_inc(v_fvarId_1013_);
v_type_1014_ = lean_ctor_get(v_decl_1012_, 2);
lean_inc_ref(v_type_1014_);
lean_dec_ref(v_decl_1012_);
v___x_1015_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1014_);
lean_dec_ref(v_type_1014_);
if (v___x_1015_ == 0)
{
lean_dec(v_fvarId_1013_);
return v_ctx_1010_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = lean_array_get_size(v_parents_1011_);
v___x_1018_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1019_ = lean_nat_dec_lt(v___x_1016_, v___x_1017_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
v___x_1020_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1010_, v___x_1018_, v_fvarId_1013_);
return v___x_1020_;
}
else
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_le(v___x_1017_, v___x_1017_);
if (v___x_1021_ == 0)
{
if (v___x_1019_ == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1010_, v___x_1018_, v_fvarId_1013_);
return v___x_1022_;
}
else
{
size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1023_ = ((size_t)0ULL);
v___x_1024_ = lean_usize_of_nat(v___x_1017_);
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(v_ctx_1010_, v_parents_1011_, v___x_1023_, v___x_1024_, v___x_1018_);
v___x_1026_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1010_, v___x_1025_, v_fvarId_1013_);
return v___x_1026_;
}
}
else
{
size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1027_ = ((size_t)0ULL);
v___x_1028_ = lean_usize_of_nat(v___x_1017_);
v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(v_ctx_1010_, v_parents_1011_, v___x_1027_, v___x_1028_, v___x_1018_);
v___x_1030_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1010_, v___x_1029_, v_fvarId_1013_);
return v___x_1030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___boxed(lean_object* v_ctx_1031_, lean_object* v_parents_1032_, lean_object* v_decl_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1031_, v_parents_1032_, v_decl_1033_);
lean_dec_ref(v_parents_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0(lean_object* v_00_u03b4_1035_, lean_object* v_t_1036_, lean_object* v_k_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_t_1036_, v_k_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___boxed(lean_object* v_00_u03b4_1039_, lean_object* v_t_1040_, lean_object* v_k_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0(v_00_u03b4_1039_, v_t_1040_, v_k_1041_);
lean_dec(v_k_1041_);
lean_dec(v_t_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(lean_object* v_as_1043_, size_t v_i_1044_, size_t v_stop_1045_, lean_object* v_b_1046_){
_start:
{
lean_object* v___y_1048_; uint8_t v___x_1052_; 
v___x_1052_ = lean_usize_dec_eq(v_i_1044_, v_stop_1045_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_array_uget_borrowed(v_as_1043_, v_i_1044_);
if (lean_obj_tag(v___x_1053_) == 0)
{
v___y_1048_ = v_b_1046_;
goto v___jp_1047_;
}
else
{
lean_object* v_fvarId_1054_; lean_object* v___x_1055_; 
v_fvarId_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_fvarId_1054_);
v___x_1055_ = lean_array_push(v_b_1046_, v_fvarId_1054_);
v___y_1048_ = v___x_1055_;
goto v___jp_1047_;
}
}
else
{
return v_b_1046_;
}
v___jp_1047_:
{
size_t v___x_1049_; size_t v___x_1050_; 
v___x_1049_ = ((size_t)1ULL);
v___x_1050_ = lean_usize_add(v_i_1044_, v___x_1049_);
v_i_1044_ = v___x_1050_;
v_b_1046_ = v___y_1048_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0___boxed(lean_object* v_as_1056_, lean_object* v_i_1057_, lean_object* v_stop_1058_, lean_object* v_b_1059_){
_start:
{
size_t v_i_boxed_1060_; size_t v_stop_boxed_1061_; lean_object* v_res_1062_; 
v_i_boxed_1060_ = lean_unbox_usize(v_i_1057_);
lean_dec(v_i_1057_);
v_stop_boxed_1061_ = lean_unbox_usize(v_stop_1058_);
lean_dec(v_stop_1058_);
v_res_1062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1056_, v_i_boxed_1060_, v_stop_boxed_1061_, v_b_1059_);
lean_dec_ref(v_as_1056_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(lean_object* v_as_1063_, lean_object* v_start_1064_, lean_object* v_stop_1065_){
_start:
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1067_ = lean_nat_dec_lt(v_start_1064_, v_stop_1065_);
if (v___x_1067_ == 0)
{
return v___x_1066_;
}
else
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = lean_array_get_size(v_as_1063_);
v___x_1069_ = lean_nat_dec_le(v_stop_1065_, v___x_1068_);
if (v___x_1069_ == 0)
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_nat_dec_lt(v_start_1064_, v___x_1068_);
if (v___x_1070_ == 0)
{
return v___x_1066_;
}
else
{
size_t v___x_1071_; size_t v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_usize_of_nat(v_start_1064_);
v___x_1072_ = lean_usize_of_nat(v___x_1068_);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1063_, v___x_1071_, v___x_1072_, v___x_1066_);
return v___x_1073_;
}
}
else
{
size_t v___x_1074_; size_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = lean_usize_of_nat(v_start_1064_);
v___x_1075_ = lean_usize_of_nat(v_stop_1065_);
v___x_1076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1063_, v___x_1074_, v___x_1075_, v___x_1066_);
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0___boxed(lean_object* v_as_1077_, lean_object* v_start_1078_, lean_object* v_stop_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(v_as_1077_, v_start_1078_, v_stop_1079_);
lean_dec(v_stop_1079_);
lean_dec(v_start_1078_);
lean_dec_ref(v_as_1077_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(lean_object* v_ctx_1085_, lean_object* v_decl_1086_){
_start:
{
lean_object* v_args_1088_; lean_object* v_fvarId_1099_; lean_object* v_value_1100_; 
v_fvarId_1099_ = lean_ctor_get(v_decl_1086_, 0);
v_value_1100_ = lean_ctor_get(v_decl_1086_, 3);
switch(lean_obj_tag(v_value_1100_))
{
case 6:
{
lean_object* v_var_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_var_1105_ = lean_ctor_get(v_value_1100_, 1);
v___x_1106_ = lean_unsigned_to_nat(1u);
v___x_1107_ = lean_mk_empty_array_with_capacity(v___x_1106_);
lean_inc(v_var_1105_);
v___x_1108_ = lean_array_push(v___x_1107_, v_var_1105_);
v___x_1109_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1085_, v___x_1108_, v_decl_1086_);
lean_dec_ref(v___x_1108_);
return v___x_1109_;
}
case 9:
{
lean_object* v_fn_1110_; 
v_fn_1110_ = lean_ctor_get(v_value_1100_, 0);
if (lean_obj_tag(v_fn_1110_) == 1)
{
lean_object* v_pre_1111_; 
v_pre_1111_ = lean_ctor_get(v_fn_1110_, 0);
if (lean_obj_tag(v_pre_1111_) == 1)
{
lean_object* v_pre_1112_; 
v_pre_1112_ = lean_ctor_get(v_pre_1111_, 0);
if (lean_obj_tag(v_pre_1112_) == 0)
{
lean_object* v_args_1113_; lean_object* v_str_1114_; lean_object* v_str_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_args_1113_ = lean_ctor_get(v_value_1100_, 1);
v_str_1114_ = lean_ctor_get(v_fn_1110_, 1);
v_str_1115_ = lean_ctor_get(v_pre_1111_, 1);
v___x_1116_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0));
v___x_1117_ = lean_string_dec_eq(v_str_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1118_ = lean_array_get_size(v_args_1113_);
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = lean_nat_dec_eq(v___x_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
goto v___jp_1096_;
}
else
{
lean_inc(v_fvarId_1099_);
goto v___jp_1101_;
}
}
else
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__1));
v___x_1122_ = lean_string_dec_eq(v_str_1114_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__2));
v___x_1124_ = lean_string_dec_eq(v_str_1114_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__3));
v___x_1126_ = lean_string_dec_eq(v_str_1114_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1127_ = lean_array_get_size(v_args_1113_);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_nat_dec_eq(v___x_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
goto v___jp_1096_;
}
else
{
lean_inc(v_fvarId_1099_);
goto v___jp_1101_;
}
}
else
{
lean_inc_ref(v_args_1113_);
v_args_1088_ = v_args_1113_;
goto v___jp_1087_;
}
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_parents_1140_; lean_object* v___x_1141_; 
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_array_get_borrowed(v___x_1130_, v_args_1113_, v___x_1131_);
v___x_1133_ = lean_unsigned_to_nat(2u);
v___x_1134_ = lean_array_get_borrowed(v___x_1130_, v_args_1113_, v___x_1133_);
v___x_1135_ = lean_mk_empty_array_with_capacity(v___x_1133_);
lean_inc(v___x_1132_);
v___x_1136_ = lean_array_push(v___x_1135_, v___x_1132_);
lean_inc(v___x_1134_);
v___x_1137_ = lean_array_push(v___x_1136_, v___x_1134_);
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_array_get_size(v___x_1137_);
v_parents_1140_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(v___x_1137_, v___x_1138_, v___x_1139_);
lean_dec_ref(v___x_1137_);
v___x_1141_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1085_, v_parents_1140_, v_decl_1086_);
lean_dec_ref(v_parents_1140_);
return v___x_1141_;
}
}
else
{
lean_inc_ref(v_args_1113_);
v_args_1088_ = v_args_1113_;
goto v___jp_1087_;
}
}
}
else
{
lean_object* v_args_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v_args_1142_ = lean_ctor_get(v_value_1100_, 1);
v___x_1143_ = lean_array_get_size(v_args_1142_);
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = lean_nat_dec_eq(v___x_1143_, v___x_1144_);
if (v___x_1145_ == 0)
{
goto v___jp_1096_;
}
else
{
lean_inc(v_fvarId_1099_);
goto v___jp_1101_;
}
}
}
else
{
lean_object* v_args_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v_args_1146_ = lean_ctor_get(v_value_1100_, 1);
v___x_1147_ = lean_array_get_size(v_args_1146_);
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_nat_dec_eq(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
goto v___jp_1096_;
}
else
{
lean_inc(v_fvarId_1099_);
goto v___jp_1101_;
}
}
}
else
{
lean_object* v_args_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_args_1150_ = lean_ctor_get(v_value_1100_, 1);
v___x_1151_ = lean_array_get_size(v_args_1150_);
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = lean_nat_dec_eq(v___x_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
goto v___jp_1096_;
}
else
{
lean_inc(v_fvarId_1099_);
goto v___jp_1101_;
}
}
}
case 5:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1155_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1085_, v___x_1154_, v_decl_1086_);
return v___x_1155_;
}
case 12:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1157_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1085_, v___x_1156_, v_decl_1086_);
return v___x_1157_;
}
default: 
{
lean_dec_ref(v_decl_1086_);
return v_ctx_1085_;
}
}
v___jp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = lean_unsigned_to_nat(1u);
v___x_1091_ = lean_array_get(v___x_1089_, v_args_1088_, v___x_1090_);
lean_dec_ref(v_args_1088_);
if (lean_obj_tag(v___x_1091_) == 1)
{
lean_object* v_fvarId_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_fvarId_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_fvarId_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v___x_1093_ = lean_mk_empty_array_with_capacity(v___x_1090_);
v___x_1094_ = lean_array_push(v___x_1093_, v_fvarId_1092_);
v___x_1095_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1085_, v___x_1094_, v_decl_1086_);
lean_dec_ref(v___x_1094_);
return v___x_1095_;
}
else
{
lean_dec(v___x_1091_);
lean_dec_ref(v_decl_1086_);
return v_ctx_1085_;
}
}
v___jp_1096_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1098_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1085_, v___x_1097_, v_decl_1086_);
return v___x_1098_;
}
v___jp_1101_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1103_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1085_, v___x_1102_, v_decl_1086_);
v___x_1104_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(v___x_1103_, v_fvarId_1099_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___lam__0(lean_object* v_x1_1158_, lean_object* v_x2_1159_){
_start:
{
lean_object* v_resetTargets_1160_; lean_object* v_unconditionalBorrows_1161_; lean_object* v_derivedValMap_1162_; lean_object* v_varMap_1163_; lean_object* v_jpLiveVarMap_1164_; lean_object* v_idx_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1186_; 
v_resetTargets_1160_ = lean_ctor_get(v_x1_1158_, 0);
v_unconditionalBorrows_1161_ = lean_ctor_get(v_x1_1158_, 1);
v_derivedValMap_1162_ = lean_ctor_get(v_x1_1158_, 2);
v_varMap_1163_ = lean_ctor_get(v_x1_1158_, 3);
v_jpLiveVarMap_1164_ = lean_ctor_get(v_x1_1158_, 4);
v_idx_1165_ = lean_ctor_get(v_x1_1158_, 5);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_x1_1158_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1167_ = v_x1_1158_;
v_isShared_1168_ = v_isSharedCheck_1186_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_idx_1165_);
lean_inc(v_jpLiveVarMap_1164_);
lean_inc(v_varMap_1163_);
lean_inc(v_derivedValMap_1162_);
lean_inc(v_unconditionalBorrows_1161_);
lean_inc(v_resetTargets_1160_);
lean_dec(v_x1_1158_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1186_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_fvarId_1169_; lean_object* v_type_1170_; uint8_t v_borrow_1171_; uint8_t v___x_1172_; uint8_t v___x_1173_; uint8_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_varMap_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_ctx_1181_; 
v_fvarId_1169_ = lean_ctor_get(v_x2_1159_, 0);
lean_inc_n(v_fvarId_1169_, 2);
v_type_1170_ = lean_ctor_get(v_x2_1159_, 2);
lean_inc_ref(v_type_1170_);
v_borrow_1171_ = lean_ctor_get_uint8(v_x2_1159_, sizeof(void*)*3);
lean_dec_ref(v_x2_1159_);
v___x_1172_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1170_);
v___x_1173_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1170_);
lean_dec_ref(v_type_1170_);
v___x_1174_ = 0;
v___x_1175_ = lean_box(0);
lean_inc(v_idx_1165_);
v___x_1176_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1176_, 0, v_idx_1165_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*2, v___x_1172_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*2 + 1, v___x_1173_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*2 + 2, v___x_1174_);
v_varMap_1177_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1169_, v___x_1176_, v_varMap_1163_);
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = lean_nat_add(v_idx_1165_, v___x_1178_);
lean_dec(v_idx_1165_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 5, v___x_1179_);
lean_ctor_set(v___x_1167_, 3, v_varMap_1177_);
v_ctx_1181_ = v___x_1167_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_resetTargets_1160_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_unconditionalBorrows_1161_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_derivedValMap_1162_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_varMap_1177_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v_jpLiveVarMap_1164_);
lean_ctor_set(v_reuseFailAlloc_1185_, 5, v___x_1179_);
v_ctx_1181_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v_ctx_1183_; 
v___x_1182_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
lean_inc(v_fvarId_1169_);
v_ctx_1183_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1181_, v___x_1182_, v_fvarId_1169_);
if (v_borrow_1171_ == 0)
{
lean_dec(v_fvarId_1169_);
return v_ctx_1183_;
}
else
{
if (v___x_1172_ == 0)
{
lean_dec(v_fvarId_1169_);
return v_ctx_1183_;
}
else
{
lean_object* v___x_1184_; 
v___x_1184_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(v_ctx_1183_, v_fvarId_1169_);
return v___x_1184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(lean_object* v_ps_1188_, lean_object* v_x_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_array_get_size(v_ps_1188_);
v___x_1199_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v___x_1200_ = lean_nat_dec_lt(v___x_1197_, v___x_1198_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
lean_dec_ref(v_ps_1188_);
lean_inc(v_a_1195_);
lean_inc_ref(v_a_1194_);
lean_inc(v_a_1193_);
lean_inc_ref(v_a_1192_);
lean_inc(v_a_1191_);
lean_inc_ref(v_a_1190_);
v___x_1201_ = lean_apply_7(v_x_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, lean_box(0));
return v___x_1201_;
}
else
{
lean_object* v___f_1202_; uint8_t v___x_1203_; 
v___f_1202_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___x_1203_ = lean_nat_dec_le(v___x_1198_, v___x_1198_);
if (v___x_1203_ == 0)
{
if (v___x_1200_ == 0)
{
lean_object* v___x_1204_; 
lean_dec_ref(v_ps_1188_);
lean_inc(v_a_1195_);
lean_inc_ref(v_a_1194_);
lean_inc(v_a_1193_);
lean_inc_ref(v_a_1192_);
lean_inc(v_a_1191_);
lean_inc_ref(v_a_1190_);
v___x_1204_ = lean_apply_7(v_x_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, lean_box(0));
return v___x_1204_;
}
else
{
size_t v___x_1205_; size_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1205_ = ((size_t)0ULL);
v___x_1206_ = lean_usize_of_nat(v___x_1198_);
lean_inc_ref(v_a_1190_);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1199_, v___f_1202_, v_ps_1188_, v___x_1205_, v___x_1206_, v_a_1190_);
lean_inc(v_a_1195_);
lean_inc_ref(v_a_1194_);
lean_inc(v_a_1193_);
lean_inc_ref(v_a_1192_);
lean_inc(v_a_1191_);
v___x_1208_ = lean_apply_7(v_x_1189_, v___x_1207_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, lean_box(0));
return v___x_1208_;
}
}
else
{
size_t v___x_1209_; size_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1209_ = ((size_t)0ULL);
v___x_1210_ = lean_usize_of_nat(v___x_1198_);
lean_inc_ref(v_a_1190_);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1199_, v___f_1202_, v_ps_1188_, v___x_1209_, v___x_1210_, v_a_1190_);
lean_inc(v_a_1195_);
lean_inc_ref(v_a_1194_);
lean_inc(v_a_1193_);
lean_inc_ref(v_a_1192_);
lean_inc(v_a_1191_);
v___x_1212_ = lean_apply_7(v_x_1189_, v___x_1211_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, lean_box(0));
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___boxed(lean_object* v_ps_1213_, lean_object* v_x_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(v_ps_1213_, v_x_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(lean_object* v_00_u03b1_1223_, lean_object* v_ps_1224_, lean_object* v_x_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = lean_array_get_size(v_ps_1224_);
v___x_1235_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v___x_1236_ = lean_nat_dec_lt(v___x_1233_, v___x_1234_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
lean_dec_ref(v_ps_1224_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
lean_inc_ref(v_a_1226_);
v___x_1237_ = lean_apply_7(v_x_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, lean_box(0));
return v___x_1237_;
}
else
{
lean_object* v___f_1238_; uint8_t v___x_1239_; 
v___f_1238_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___x_1239_ = lean_nat_dec_le(v___x_1234_, v___x_1234_);
if (v___x_1239_ == 0)
{
if (v___x_1236_ == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref(v_ps_1224_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
lean_inc_ref(v_a_1226_);
v___x_1240_ = lean_apply_7(v_x_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, lean_box(0));
return v___x_1240_;
}
else
{
size_t v___x_1241_; size_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1241_ = ((size_t)0ULL);
v___x_1242_ = lean_usize_of_nat(v___x_1234_);
lean_inc_ref(v_a_1226_);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1235_, v___f_1238_, v_ps_1224_, v___x_1241_, v___x_1242_, v_a_1226_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
v___x_1244_ = lean_apply_7(v_x_1225_, v___x_1243_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, lean_box(0));
return v___x_1244_;
}
}
else
{
size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1245_ = ((size_t)0ULL);
v___x_1246_ = lean_usize_of_nat(v___x_1234_);
lean_inc_ref(v_a_1226_);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1235_, v___f_1238_, v_ps_1224_, v___x_1245_, v___x_1246_, v_a_1226_);
lean_inc(v_a_1231_);
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc_ref(v_a_1228_);
lean_inc(v_a_1227_);
v___x_1248_ = lean_apply_7(v_x_1225_, v___x_1247_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, lean_box(0));
return v___x_1248_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_ps_1250_, lean_object* v_x_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(v_00_u03b1_1249_, v_ps_1250_, v_x_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(lean_object* v_decl_1260_, lean_object* v_x_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_fvarId_1269_; lean_object* v_type_1270_; lean_object* v_value_1271_; lean_object* v___y_1273_; 
v_fvarId_1269_ = lean_ctor_get(v_decl_1260_, 0);
v_type_1270_ = lean_ctor_get(v_decl_1260_, 2);
v_value_1271_ = lean_ctor_get(v_decl_1260_, 3);
if (lean_obj_tag(v_value_1271_) == 5)
{
lean_object* v_i_1290_; lean_object* v___x_1291_; 
v_i_1290_ = lean_ctor_get(v_value_1271_, 0);
lean_inc_ref(v_i_1290_);
v___x_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1291_, 0, v_i_1290_);
v___y_1273_ = v___x_1291_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_box(0);
v___y_1273_ = v___x_1292_;
goto v___jp_1272_;
}
v___jp_1272_:
{
lean_object* v_resetTargets_1274_; lean_object* v_unconditionalBorrows_1275_; lean_object* v_derivedValMap_1276_; lean_object* v_varMap_1277_; lean_object* v_jpLiveVarMap_1278_; lean_object* v_idx_1279_; uint8_t v___x_1280_; uint8_t v___x_1281_; uint8_t v___x_1282_; lean_object* v_varInfo_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v_ctx_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_resetTargets_1274_ = lean_ctor_get(v_a_1262_, 0);
v_unconditionalBorrows_1275_ = lean_ctor_get(v_a_1262_, 1);
v_derivedValMap_1276_ = lean_ctor_get(v_a_1262_, 2);
v_varMap_1277_ = lean_ctor_get(v_a_1262_, 3);
v_jpLiveVarMap_1278_ = lean_ctor_get(v_a_1262_, 4);
v_idx_1279_ = lean_ctor_get(v_a_1262_, 5);
v___x_1280_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1270_);
v___x_1281_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1270_);
v___x_1282_ = l_Lean_Compiler_LCNF_LetValue_isPersistent(v_value_1271_);
lean_inc(v_idx_1279_);
v_varInfo_1283_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_varInfo_1283_, 0, v_idx_1279_);
lean_ctor_set(v_varInfo_1283_, 1, v___y_1273_);
lean_ctor_set_uint8(v_varInfo_1283_, sizeof(void*)*2, v___x_1280_);
lean_ctor_set_uint8(v_varInfo_1283_, sizeof(void*)*2 + 1, v___x_1281_);
lean_ctor_set_uint8(v_varInfo_1283_, sizeof(void*)*2 + 2, v___x_1282_);
lean_inc(v_varMap_1277_);
lean_inc(v_fvarId_1269_);
v___x_1284_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1269_, v_varInfo_1283_, v_varMap_1277_);
v___x_1285_ = lean_unsigned_to_nat(1u);
v___x_1286_ = lean_nat_add(v_idx_1279_, v___x_1285_);
lean_inc(v_jpLiveVarMap_1278_);
lean_inc(v_derivedValMap_1276_);
lean_inc(v_unconditionalBorrows_1275_);
lean_inc_ref(v_resetTargets_1274_);
v_ctx_1287_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_ctx_1287_, 0, v_resetTargets_1274_);
lean_ctor_set(v_ctx_1287_, 1, v_unconditionalBorrows_1275_);
lean_ctor_set(v_ctx_1287_, 2, v_derivedValMap_1276_);
lean_ctor_set(v_ctx_1287_, 3, v___x_1284_);
lean_ctor_set(v_ctx_1287_, 4, v_jpLiveVarMap_1278_);
lean_ctor_set(v_ctx_1287_, 5, v___x_1286_);
v___x_1288_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(v_ctx_1287_, v_decl_1260_);
lean_inc(v_a_1267_);
lean_inc_ref(v_a_1266_);
lean_inc(v_a_1265_);
lean_inc_ref(v_a_1264_);
lean_inc(v_a_1263_);
v___x_1289_ = lean_apply_7(v_x_1261_, v___x_1288_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, lean_box(0));
return v___x_1289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg___boxed(lean_object* v_decl_1293_, lean_object* v_x_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(v_decl_1293_, v_x_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(lean_object* v_00_u03b1_1303_, lean_object* v_decl_1304_, lean_object* v_x_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_fvarId_1313_; lean_object* v_type_1314_; lean_object* v_value_1315_; lean_object* v___y_1317_; 
v_fvarId_1313_ = lean_ctor_get(v_decl_1304_, 0);
v_type_1314_ = lean_ctor_get(v_decl_1304_, 2);
v_value_1315_ = lean_ctor_get(v_decl_1304_, 3);
if (lean_obj_tag(v_value_1315_) == 5)
{
lean_object* v_i_1334_; lean_object* v___x_1335_; 
v_i_1334_ = lean_ctor_get(v_value_1315_, 0);
lean_inc_ref(v_i_1334_);
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_i_1334_);
v___y_1317_ = v___x_1335_;
goto v___jp_1316_;
}
else
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_box(0);
v___y_1317_ = v___x_1336_;
goto v___jp_1316_;
}
v___jp_1316_:
{
lean_object* v_resetTargets_1318_; lean_object* v_unconditionalBorrows_1319_; lean_object* v_derivedValMap_1320_; lean_object* v_varMap_1321_; lean_object* v_jpLiveVarMap_1322_; lean_object* v_idx_1323_; uint8_t v___x_1324_; uint8_t v___x_1325_; uint8_t v___x_1326_; lean_object* v_varInfo_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_ctx_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_resetTargets_1318_ = lean_ctor_get(v_a_1306_, 0);
v_unconditionalBorrows_1319_ = lean_ctor_get(v_a_1306_, 1);
v_derivedValMap_1320_ = lean_ctor_get(v_a_1306_, 2);
v_varMap_1321_ = lean_ctor_get(v_a_1306_, 3);
v_jpLiveVarMap_1322_ = lean_ctor_get(v_a_1306_, 4);
v_idx_1323_ = lean_ctor_get(v_a_1306_, 5);
v___x_1324_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1314_);
v___x_1325_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1314_);
v___x_1326_ = l_Lean_Compiler_LCNF_LetValue_isPersistent(v_value_1315_);
lean_inc(v_idx_1323_);
v_varInfo_1327_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_varInfo_1327_, 0, v_idx_1323_);
lean_ctor_set(v_varInfo_1327_, 1, v___y_1317_);
lean_ctor_set_uint8(v_varInfo_1327_, sizeof(void*)*2, v___x_1324_);
lean_ctor_set_uint8(v_varInfo_1327_, sizeof(void*)*2 + 1, v___x_1325_);
lean_ctor_set_uint8(v_varInfo_1327_, sizeof(void*)*2 + 2, v___x_1326_);
lean_inc(v_varMap_1321_);
lean_inc(v_fvarId_1313_);
v___x_1328_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1313_, v_varInfo_1327_, v_varMap_1321_);
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = lean_nat_add(v_idx_1323_, v___x_1329_);
lean_inc(v_jpLiveVarMap_1322_);
lean_inc(v_derivedValMap_1320_);
lean_inc(v_unconditionalBorrows_1319_);
lean_inc_ref(v_resetTargets_1318_);
v_ctx_1331_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_ctx_1331_, 0, v_resetTargets_1318_);
lean_ctor_set(v_ctx_1331_, 1, v_unconditionalBorrows_1319_);
lean_ctor_set(v_ctx_1331_, 2, v_derivedValMap_1320_);
lean_ctor_set(v_ctx_1331_, 3, v___x_1328_);
lean_ctor_set(v_ctx_1331_, 4, v_jpLiveVarMap_1322_);
lean_ctor_set(v_ctx_1331_, 5, v___x_1330_);
v___x_1332_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(v_ctx_1331_, v_decl_1304_);
lean_inc(v_a_1311_);
lean_inc_ref(v_a_1310_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
v___x_1333_ = lean_apply_7(v_x_1305_, v___x_1332_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, lean_box(0));
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_decl_1338_, lean_object* v_x_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(v_00_u03b1_1337_, v_decl_1338_, v_x_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(lean_object* v_discr_1348_, lean_object* v_c_1349_, lean_object* v_x_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_resetTargets_1358_; lean_object* v_unconditionalBorrows_1359_; lean_object* v_derivedValMap_1360_; lean_object* v_varMap_1361_; lean_object* v_jpLiveVarMap_1362_; lean_object* v_idx_1363_; lean_object* v___y_1365_; lean_object* v___f_1370_; lean_object* v___x_1371_; 
v_resetTargets_1358_ = lean_ctor_get(v_a_1351_, 0);
v_unconditionalBorrows_1359_ = lean_ctor_get(v_a_1351_, 1);
v_derivedValMap_1360_ = lean_ctor_get(v_a_1351_, 2);
v_varMap_1361_ = lean_ctor_get(v_a_1351_, 3);
v_jpLiveVarMap_1362_ = lean_ctor_get(v_a_1351_, 4);
v_idx_1363_ = lean_ctor_get(v_a_1351_, 5);
v___f_1370_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_discr_1348_);
lean_inc(v_varMap_1361_);
v___x_1371_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1370_, v_varMap_1361_, v_discr_1348_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_dec_ref(v_c_1349_);
lean_dec(v_discr_1348_);
lean_inc(v_varMap_1361_);
v___y_1365_ = v_varMap_1361_;
goto v___jp_1364_;
}
else
{
lean_object* v_val_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1393_; 
v_val_1372_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1374_ = v___x_1371_;
v_isShared_1375_ = v_isSharedCheck_1393_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_val_1372_);
lean_dec(v___x_1371_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1393_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
uint8_t v_persistent_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1390_; 
v_persistent_1376_ = lean_ctor_get_uint8(v_val_1372_, sizeof(void*)*2 + 2);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_val_1372_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; lean_object* v_unused_1392_; 
v_unused_1391_ = lean_ctor_get(v_val_1372_, 1);
lean_dec(v_unused_1391_);
v_unused_1392_ = lean_ctor_get(v_val_1372_, 0);
lean_dec(v_unused_1392_);
v___x_1378_ = v_val_1372_;
v_isShared_1379_ = v_isSharedCheck_1390_;
goto v_resetjp_1377_;
}
else
{
lean_dec(v_val_1372_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1390_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1380_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_c_1349_);
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_nat_add(v_idx_1363_, v___x_1381_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v_c_1349_);
v___x_1384_ = v___x_1374_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_c_1349_);
v___x_1384_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1386_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 1, v___x_1384_);
lean_ctor_set(v___x_1378_, 0, v___x_1382_);
v___x_1386_ = v___x_1378_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1384_);
lean_ctor_set_uint8(v_reuseFailAlloc_1388_, sizeof(void*)*2 + 2, v_persistent_1376_);
v___x_1386_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; 
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*2, v___x_1380_);
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*2 + 1, v___x_1380_);
lean_inc(v_varMap_1361_);
v___x_1387_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_1348_, v___x_1386_, v_varMap_1361_);
v___y_1365_ = v___x_1387_;
goto v___jp_1364_;
}
}
}
}
}
v___jp_1364_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1366_ = lean_unsigned_to_nat(1u);
v___x_1367_ = lean_nat_add(v_idx_1363_, v___x_1366_);
lean_inc(v_jpLiveVarMap_1362_);
lean_inc(v_derivedValMap_1360_);
lean_inc(v_unconditionalBorrows_1359_);
lean_inc_ref(v_resetTargets_1358_);
v___x_1368_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1368_, 0, v_resetTargets_1358_);
lean_ctor_set(v___x_1368_, 1, v_unconditionalBorrows_1359_);
lean_ctor_set(v___x_1368_, 2, v_derivedValMap_1360_);
lean_ctor_set(v___x_1368_, 3, v___y_1365_);
lean_ctor_set(v___x_1368_, 4, v_jpLiveVarMap_1362_);
lean_ctor_set(v___x_1368_, 5, v___x_1367_);
lean_inc(v_a_1356_);
lean_inc_ref(v_a_1355_);
lean_inc(v_a_1354_);
lean_inc_ref(v_a_1353_);
lean_inc(v_a_1352_);
v___x_1369_ = lean_apply_7(v_x_1350_, v___x_1368_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, lean_box(0));
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg___boxed(lean_object* v_discr_1394_, lean_object* v_c_1395_, lean_object* v_x_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(v_discr_1394_, v_c_1395_, v_x_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(lean_object* v_00_u03b1_1405_, lean_object* v_discr_1406_, lean_object* v_c_1407_, lean_object* v_x_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v_resetTargets_1416_; lean_object* v_unconditionalBorrows_1417_; lean_object* v_derivedValMap_1418_; lean_object* v_varMap_1419_; lean_object* v_jpLiveVarMap_1420_; lean_object* v_idx_1421_; lean_object* v___y_1423_; lean_object* v___f_1428_; lean_object* v___x_1429_; 
v_resetTargets_1416_ = lean_ctor_get(v_a_1409_, 0);
v_unconditionalBorrows_1417_ = lean_ctor_get(v_a_1409_, 1);
v_derivedValMap_1418_ = lean_ctor_get(v_a_1409_, 2);
v_varMap_1419_ = lean_ctor_get(v_a_1409_, 3);
v_jpLiveVarMap_1420_ = lean_ctor_get(v_a_1409_, 4);
v_idx_1421_ = lean_ctor_get(v_a_1409_, 5);
v___f_1428_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_discr_1406_);
lean_inc(v_varMap_1419_);
v___x_1429_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1428_, v_varMap_1419_, v_discr_1406_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_dec_ref(v_c_1407_);
lean_dec(v_discr_1406_);
lean_inc(v_varMap_1419_);
v___y_1423_ = v_varMap_1419_;
goto v___jp_1422_;
}
else
{
lean_object* v_val_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1451_; 
v_val_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1451_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_val_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1451_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
uint8_t v_persistent_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1448_; 
v_persistent_1434_ = lean_ctor_get_uint8(v_val_1430_, sizeof(void*)*2 + 2);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_val_1430_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; lean_object* v_unused_1450_; 
v_unused_1449_ = lean_ctor_get(v_val_1430_, 1);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_val_1430_, 0);
lean_dec(v_unused_1450_);
v___x_1436_ = v_val_1430_;
v_isShared_1437_ = v_isSharedCheck_1448_;
goto v_resetjp_1435_;
}
else
{
lean_dec(v_val_1430_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1448_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
uint8_t v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1438_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_c_1407_);
v___x_1439_ = lean_unsigned_to_nat(1u);
v___x_1440_ = lean_nat_add(v_idx_1421_, v___x_1439_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v_c_1407_);
v___x_1442_ = v___x_1432_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_c_1407_);
v___x_1442_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1442_);
lean_ctor_set(v___x_1436_, 0, v___x_1440_);
v___x_1444_ = v___x_1436_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, sizeof(void*)*2 + 2, v_persistent_1434_);
v___x_1444_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; 
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*2, v___x_1438_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*2 + 1, v___x_1438_);
lean_inc(v_varMap_1419_);
v___x_1445_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_1406_, v___x_1444_, v_varMap_1419_);
v___y_1423_ = v___x_1445_;
goto v___jp_1422_;
}
}
}
}
}
v___jp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1424_ = lean_unsigned_to_nat(1u);
v___x_1425_ = lean_nat_add(v_idx_1421_, v___x_1424_);
lean_inc(v_jpLiveVarMap_1420_);
lean_inc(v_derivedValMap_1418_);
lean_inc(v_unconditionalBorrows_1417_);
lean_inc_ref(v_resetTargets_1416_);
v___x_1426_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1426_, 0, v_resetTargets_1416_);
lean_ctor_set(v___x_1426_, 1, v_unconditionalBorrows_1417_);
lean_ctor_set(v___x_1426_, 2, v_derivedValMap_1418_);
lean_ctor_set(v___x_1426_, 3, v___y_1423_);
lean_ctor_set(v___x_1426_, 4, v_jpLiveVarMap_1420_);
lean_ctor_set(v___x_1426_, 5, v___x_1425_);
lean_inc(v_a_1414_);
lean_inc_ref(v_a_1413_);
lean_inc(v_a_1412_);
lean_inc_ref(v_a_1411_);
lean_inc(v_a_1410_);
v___x_1427_ = lean_apply_7(v_x_1408_, v___x_1426_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, lean_box(0));
return v___x_1427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___boxed(lean_object* v_00_u03b1_1452_, lean_object* v_discr_1453_, lean_object* v_c_1454_, lean_object* v_x_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(v_00_u03b1_1452_, v_discr_1453_, v_c_1454_, v_x_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(lean_object* v_x_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1472_ = lean_st_ref_get(v_a_1466_);
v___x_1473_ = lean_st_ref_take(v_a_1466_);
lean_dec(v___x_1473_);
v___x_1474_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_1475_ = lean_st_ref_put(v_a_1466_, v___x_1474_);
lean_inc(v_a_1470_);
lean_inc_ref(v_a_1469_);
lean_inc(v_a_1468_);
lean_inc_ref(v_a_1467_);
lean_inc(v_a_1466_);
lean_inc_ref(v_a_1465_);
v___x_1476_ = lean_apply_7(v_x_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, lean_box(0));
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1488_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1488_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1488_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1481_ = lean_st_ref_get(v_a_1466_);
v___x_1482_ = lean_st_ref_take(v_a_1466_);
lean_dec(v___x_1482_);
v___x_1483_ = lean_st_ref_put(v_a_1466_, v___x_1472_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_a_1477_);
lean_ctor_set(v___x_1484_, 1, v___x_1481_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1484_);
v___x_1486_ = v___x_1479_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v___x_1472_);
v_a_1489_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1476_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1476_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg___boxed(lean_object* v_x_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(v_x_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(lean_object* v_00_u03b1_1506_, lean_object* v_x_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1515_ = lean_st_ref_get(v_a_1509_);
v___x_1516_ = lean_st_ref_take(v_a_1509_);
lean_dec(v___x_1516_);
v___x_1517_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_1518_ = lean_st_ref_put(v_a_1509_, v___x_1517_);
lean_inc(v_a_1513_);
lean_inc_ref(v_a_1512_);
lean_inc(v_a_1511_);
lean_inc_ref(v_a_1510_);
lean_inc(v_a_1509_);
lean_inc_ref(v_a_1508_);
v___x_1519_ = lean_apply_7(v_x_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, lean_box(0));
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1531_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1531_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1531_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1524_ = lean_st_ref_get(v_a_1509_);
v___x_1525_ = lean_st_ref_take(v_a_1509_);
lean_dec(v___x_1525_);
v___x_1526_ = lean_st_ref_put(v_a_1509_, v___x_1515_);
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v_a_1520_);
lean_ctor_set(v___x_1527_, 1, v___x_1524_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1527_);
v___x_1529_ = v___x_1522_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v___x_1515_);
v_a_1532_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1519_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1519_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___boxed(lean_object* v_00_u03b1_1540_, lean_object* v_x_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(v_00_u03b1_1540_, v_x_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
return v_res_1549_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0(lean_object* v_liveVars_1550_, uint8_t v___x_1551_, lean_object* v___x_1552_, lean_object* v___x_1553_, lean_object* v_v_1554_){
_start:
{
uint8_t v___y_1556_; lean_object* v_vars_1558_; lean_object* v_borrows_1559_; uint8_t v___x_1560_; 
v_vars_1558_ = lean_ctor_get(v_liveVars_1550_, 0);
v_borrows_1559_ = lean_ctor_get(v_liveVars_1550_, 1);
lean_inc(v_v_1554_);
lean_inc_ref(v___x_1553_);
lean_inc_ref(v___x_1552_);
v___x_1560_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1552_, v___x_1553_, v_vars_1558_, v_v_1554_);
if (v___x_1560_ == 0)
{
uint8_t v___x_1561_; 
v___x_1561_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1552_, v___x_1553_, v_borrows_1559_, v_v_1554_);
v___y_1556_ = v___x_1561_;
goto v___jp_1555_;
}
else
{
lean_dec(v_v_1554_);
lean_dec_ref(v___x_1553_);
lean_dec_ref(v___x_1552_);
v___y_1556_ = v___x_1560_;
goto v___jp_1555_;
}
v___jp_1555_:
{
if (v___y_1556_ == 0)
{
return v___x_1551_;
}
else
{
uint8_t v___x_1557_; 
v___x_1557_ = 0;
return v___x_1557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0___boxed(lean_object* v_liveVars_1562_, lean_object* v___x_1563_, lean_object* v___x_1564_, lean_object* v___x_1565_, lean_object* v_v_1566_){
_start:
{
uint8_t v___x_362__boxed_1567_; uint8_t v_res_1568_; lean_object* v_r_1569_; 
v___x_362__boxed_1567_ = lean_unbox(v___x_1563_);
v_res_1568_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0(v_liveVars_1562_, v___x_362__boxed_1567_, v___x_1564_, v___x_1565_, v_v_1566_);
lean_dec_ref(v_liveVars_1562_);
v_r_1569_ = lean_box(v_res_1568_);
return v_r_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1(lean_object* v___f_1570_, lean_object* v___x_1571_, lean_object* v_derivedValMap_1572_, lean_object* v_shouldAdd_1573_, lean_object* v___x_1574_, lean_object* v___x_1575_, lean_object* v_liveVars_1576_, lean_object* v_child_1577_){
_start:
{
lean_object* v_cinfo_1594_; lean_object* v_parents_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
lean_inc(v_child_1577_);
lean_inc(v_derivedValMap_1572_);
v_cinfo_1594_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_1570_, v___x_1571_, v_derivedValMap_1572_, v_child_1577_);
v_parents_1595_ = lean_ctor_get(v_cinfo_1594_, 0);
lean_inc_ref(v_parents_1595_);
lean_dec(v_cinfo_1594_);
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = lean_array_get_size(v_parents_1595_);
v___x_1598_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v___x_1599_ = lean_nat_dec_lt(v___x_1596_, v___x_1597_);
if (v___x_1599_ == 0)
{
lean_dec_ref(v_parents_1595_);
goto v___jp_1578_;
}
else
{
if (v___x_1599_ == 0)
{
lean_dec_ref(v_parents_1595_);
goto v___jp_1578_;
}
else
{
lean_object* v___x_1600_; lean_object* v___f_1601_; size_t v___x_1602_; size_t v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1600_ = lean_box(v___x_1599_);
lean_inc_ref(v___x_1575_);
lean_inc_ref(v___x_1574_);
lean_inc_ref(v_liveVars_1576_);
v___f_1601_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1601_, 0, v_liveVars_1576_);
lean_closure_set(v___f_1601_, 1, v___x_1600_);
lean_closure_set(v___f_1601_, 2, v___x_1574_);
lean_closure_set(v___f_1601_, 3, v___x_1575_);
v___x_1602_ = ((size_t)0ULL);
v___x_1603_ = lean_usize_of_nat(v___x_1597_);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1598_, v___f_1601_, v_parents_1595_, v___x_1602_, v___x_1603_);
v___x_1605_ = lean_unbox(v___x_1604_);
lean_dec(v___x_1604_);
if (v___x_1605_ == 0)
{
goto v___jp_1578_;
}
else
{
lean_object* v___x_1606_; 
lean_dec_ref(v___x_1575_);
lean_dec_ref(v___x_1574_);
v___x_1606_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_child_1577_, v_derivedValMap_1572_, v_liveVars_1576_, v_shouldAdd_1573_);
return v___x_1606_;
}
}
}
v___jp_1578_:
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
lean_inc_ref(v_shouldAdd_1573_);
lean_inc(v_child_1577_);
v___x_1579_ = lean_apply_1(v_shouldAdd_1573_, v_child_1577_);
v___x_1580_ = lean_unbox(v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_dec_ref(v___x_1575_);
lean_dec_ref(v___x_1574_);
v___x_1581_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_child_1577_, v_derivedValMap_1572_, v_liveVars_1576_, v_shouldAdd_1573_);
return v___x_1581_;
}
else
{
lean_object* v_vars_1582_; lean_object* v_borrows_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1593_; 
v_vars_1582_ = lean_ctor_get(v_liveVars_1576_, 0);
v_borrows_1583_ = lean_ctor_get(v_liveVars_1576_, 1);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_liveVars_1576_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1585_ = v_liveVars_1576_;
v_isShared_1586_ = v_isSharedCheck_1593_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_borrows_1583_);
lean_inc(v_vars_1582_);
lean_dec(v_liveVars_1576_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1593_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1587_ = lean_box(0);
lean_inc(v_child_1577_);
v___x_1588_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1574_, v___x_1575_, v_borrows_1583_, v_child_1577_, v___x_1587_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 1, v___x_1588_);
v___x_1590_ = v___x_1585_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_vars_1582_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; 
v___x_1591_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_child_1577_, v_derivedValMap_1572_, v___x_1590_, v_shouldAdd_1573_);
return v___x_1591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1___boxed(lean_object* v___f_1607_, lean_object* v___x_1608_, lean_object* v_derivedValMap_1609_, lean_object* v_shouldAdd_1610_, lean_object* v___x_1611_, lean_object* v___x_1612_, lean_object* v_liveVars_1613_, lean_object* v_child_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1(v___f_1607_, v___x_1608_, v_derivedValMap_1609_, v_shouldAdd_1610_, v___x_1611_, v___x_1612_, v_liveVars_1613_, v_child_1614_);
lean_dec_ref(v___x_1608_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(lean_object* v_fvarId_1616_, lean_object* v_derivedValMap_1617_, lean_object* v_liveVars_1618_, lean_object* v_shouldAdd_1619_){
_start:
{
lean_object* v___f_1620_; lean_object* v___x_1621_; 
v___f_1620_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_derivedValMap_1617_);
v___x_1621_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1620_, v_derivedValMap_1617_, v_fvarId_1616_);
if (lean_obj_tag(v___x_1621_) == 1)
{
lean_object* v_val_1622_; lean_object* v_children_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___f_1627_; lean_object* v___x_1628_; 
v_val_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_val_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v_children_1623_ = lean_ctor_get(v_val_1622_, 1);
lean_inc(v_children_1623_);
lean_dec(v_val_1622_);
v___x_1624_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default));
v___x_1625_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_1626_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___f_1627_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1___boxed), 8, 6);
lean_closure_set(v___f_1627_, 0, v___f_1620_);
lean_closure_set(v___f_1627_, 1, v___x_1624_);
lean_closure_set(v___f_1627_, 2, v_derivedValMap_1617_);
lean_closure_set(v___f_1627_, 3, v_shouldAdd_1619_);
lean_closure_set(v___f_1627_, 4, v___x_1625_);
lean_closure_set(v___f_1627_, 5, v___x_1626_);
v___x_1628_ = l_List_foldl___redArg(v___f_1627_, v_liveVars_1618_, v_children_1623_);
return v___x_1628_;
}
else
{
lean_dec(v___x_1621_);
lean_dec_ref(v_shouldAdd_1619_);
lean_dec(v_derivedValMap_1617_);
return v_liveVars_1618_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0(lean_object* v_val_1629_, lean_object* v___x_1630_, lean_object* v___x_1631_, lean_object* v_shouldBorrow_1632_, uint8_t v___x_1633_, lean_object* v_y_1634_){
_start:
{
lean_object* v_vars_1635_; uint8_t v___x_1636_; 
v_vars_1635_ = lean_ctor_get(v_val_1629_, 0);
lean_inc(v_y_1634_);
v___x_1636_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1630_, v___x_1631_, v_vars_1635_, v_y_1634_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = lean_apply_1(v_shouldBorrow_1632_, v_y_1634_);
v___x_1638_ = lean_unbox(v___x_1637_);
return v___x_1638_;
}
else
{
lean_dec(v_y_1634_);
lean_dec_ref(v_shouldBorrow_1632_);
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0___boxed(lean_object* v_val_1639_, lean_object* v___x_1640_, lean_object* v___x_1641_, lean_object* v_shouldBorrow_1642_, lean_object* v___x_1643_, lean_object* v_y_1644_){
_start:
{
uint8_t v___x_1972__boxed_1645_; uint8_t v_res_1646_; lean_object* v_r_1647_; 
v___x_1972__boxed_1645_ = lean_unbox(v___x_1643_);
v_res_1646_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0(v_val_1639_, v___x_1640_, v___x_1641_, v_shouldBorrow_1642_, v___x_1972__boxed_1645_, v_y_1644_);
lean_dec_ref(v_val_1639_);
v_r_1647_ = lean_box(v_res_1646_);
return v_r_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(lean_object* v_fvarId_1648_, lean_object* v_shouldBorrow_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v_vars_1656_; uint8_t v___x_1657_; 
v___x_1653_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_1654_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_1655_ = lean_st_ref_get(v_a_1651_);
v_vars_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc_ref(v_vars_1656_);
lean_dec(v___x_1655_);
lean_inc(v_fvarId_1648_);
v___x_1657_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1653_, v___x_1654_, v_vars_1656_, v_fvarId_1648_);
lean_dec_ref(v_vars_1656_);
if (v___x_1657_ == 0)
{
lean_object* v_derivedValMap_1658_; lean_object* v___x_1659_; lean_object* v_vars_1660_; lean_object* v_borrows_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1677_; 
v_derivedValMap_1658_ = lean_ctor_get(v_a_1650_, 2);
v___x_1659_ = lean_st_ref_take(v_a_1651_);
v_vars_1660_ = lean_ctor_get(v___x_1659_, 0);
v_borrows_1661_ = lean_ctor_get(v___x_1659_, 1);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1663_ = v___x_1659_;
v_isShared_1664_ = v_isSharedCheck_1677_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_borrows_1661_);
lean_inc(v_vars_1660_);
lean_dec(v___x_1659_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1677_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1665_ = lean_box(0);
lean_inc(v_fvarId_1648_);
v___x_1666_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1653_, v___x_1654_, v_vars_1660_, v_fvarId_1648_, v___x_1665_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1666_);
v___x_1668_ = v___x_1663_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_borrows_1661_);
v___x_1668_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___f_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1669_ = lean_st_ref_put(v_a_1651_, v___x_1668_);
v___x_1670_ = lean_st_ref_take(v_a_1651_);
v___x_1671_ = lean_box(v___x_1657_);
lean_inc(v___x_1670_);
v___f_1672_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1672_, 0, v___x_1670_);
lean_closure_set(v___f_1672_, 1, v___x_1653_);
lean_closure_set(v___f_1672_, 2, v___x_1654_);
lean_closure_set(v___f_1672_, 3, v_shouldBorrow_1649_);
lean_closure_set(v___f_1672_, 4, v___x_1671_);
lean_inc(v_derivedValMap_1658_);
v___x_1673_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_fvarId_1648_, v_derivedValMap_1658_, v___x_1670_, v___f_1672_);
v___x_1674_ = lean_st_ref_put(v_a_1651_, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1665_);
return v___x_1675_;
}
}
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec_ref(v_shouldBorrow_1649_);
lean_dec(v_fvarId_1648_);
v___x_1678_ = lean_box(0);
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
return v___x_1679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___boxed(lean_object* v_fvarId_1680_, lean_object* v_shouldBorrow_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_1680_, v_shouldBorrow_1681_, v_a_1682_, v_a_1683_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(lean_object* v_fvarId_1686_, lean_object* v_shouldBorrow_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_1686_, v_shouldBorrow_1687_, v_a_1688_, v_a_1689_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___boxed(lean_object* v_fvarId_1696_, lean_object* v_shouldBorrow_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(v_fvarId_1696_, v_shouldBorrow_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
return v_res_1705_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(lean_object* v_liveVars_1706_, lean_object* v_as_1707_, size_t v_i_1708_, size_t v_stop_1709_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_usize_dec_eq(v_i_1708_, v_stop_1709_);
if (v___x_1710_ == 0)
{
lean_object* v_vars_1711_; lean_object* v_borrows_1712_; uint8_t v___x_1713_; uint8_t v___y_1715_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
v_vars_1711_ = lean_ctor_get(v_liveVars_1706_, 0);
v_borrows_1712_ = lean_ctor_get(v_liveVars_1706_, 1);
v___x_1713_ = 1;
v___x_1719_ = lean_array_uget_borrowed(v_as_1707_, v_i_1708_);
v___x_1720_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1711_, v___x_1719_);
if (v___x_1720_ == 0)
{
uint8_t v___x_1721_; 
v___x_1721_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_1712_, v___x_1719_);
v___y_1715_ = v___x_1721_;
goto v___jp_1714_;
}
else
{
v___y_1715_ = v___x_1720_;
goto v___jp_1714_;
}
v___jp_1714_:
{
if (v___y_1715_ == 0)
{
return v___x_1713_;
}
else
{
size_t v___x_1716_; size_t v___x_1717_; 
v___x_1716_ = ((size_t)1ULL);
v___x_1717_ = lean_usize_add(v_i_1708_, v___x_1716_);
v_i_1708_ = v___x_1717_;
goto _start;
}
}
}
else
{
uint8_t v___x_1722_; 
v___x_1722_ = 0;
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3___boxed(lean_object* v_liveVars_1723_, lean_object* v_as_1724_, lean_object* v_i_1725_, lean_object* v_stop_1726_){
_start:
{
size_t v_i_boxed_1727_; size_t v_stop_boxed_1728_; uint8_t v_res_1729_; lean_object* v_r_1730_; 
v_i_boxed_1727_ = lean_unbox_usize(v_i_1725_);
lean_dec(v_i_1725_);
v_stop_boxed_1728_ = lean_unbox_usize(v_stop_1726_);
lean_dec(v_stop_1726_);
v_res_1729_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_liveVars_1723_, v_as_1724_, v_i_boxed_1727_, v_stop_boxed_1728_);
lean_dec_ref(v_as_1724_);
lean_dec_ref(v_liveVars_1723_);
v_r_1730_ = lean_box(v_res_1729_);
return v_r_1730_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(lean_object* v_y_1731_, lean_object* v_as_1732_, size_t v_i_1733_, size_t v_stop_1734_){
_start:
{
uint8_t v___x_1739_; 
v___x_1739_ = lean_usize_dec_eq(v_i_1733_, v_stop_1734_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_array_uget_borrowed(v_as_1732_, v_i_1733_);
if (lean_obj_tag(v___x_1740_) == 0)
{
goto v___jp_1735_;
}
else
{
lean_object* v_fvarId_1741_; uint8_t v___x_1742_; 
v_fvarId_1741_ = lean_ctor_get(v___x_1740_, 0);
v___x_1742_ = l_Lean_instBEqFVarId_beq(v_y_1731_, v_fvarId_1741_);
if (v___x_1742_ == 0)
{
goto v___jp_1735_;
}
else
{
return v___x_1742_;
}
}
}
else
{
uint8_t v___x_1743_; 
v___x_1743_ = 0;
return v___x_1743_;
}
v___jp_1735_:
{
size_t v___x_1736_; size_t v___x_1737_; 
v___x_1736_ = ((size_t)1ULL);
v___x_1737_ = lean_usize_add(v_i_1733_, v___x_1736_);
v_i_1733_ = v___x_1737_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0___boxed(lean_object* v_y_1744_, lean_object* v_as_1745_, lean_object* v_i_1746_, lean_object* v_stop_1747_){
_start:
{
size_t v_i_boxed_1748_; size_t v_stop_boxed_1749_; uint8_t v_res_1750_; lean_object* v_r_1751_; 
v_i_boxed_1748_ = lean_unbox_usize(v_i_1746_);
lean_dec(v_i_1746_);
v_stop_boxed_1749_ = lean_unbox_usize(v_stop_1747_);
lean_dec(v_stop_1747_);
v_res_1750_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_y_1744_, v_as_1745_, v_i_boxed_1748_, v_stop_boxed_1749_);
lean_dec_ref(v_as_1745_);
lean_dec(v_y_1744_);
v_r_1751_ = lean_box(v_res_1750_);
return v_r_1751_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2_spec__4(lean_object* v_msg_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default));
v___x_1754_ = lean_panic_fn_borrowed(v___x_1753_, v_msg_1752_);
return v___x_1754_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1758_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__2));
v___x_1759_ = lean_unsigned_to_nat(13u);
v___x_1760_ = lean_unsigned_to_nat(227u);
v___x_1761_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__1));
v___x_1762_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__0));
v___x_1763_ = l_mkPanicMessageWithDecl(v___x_1762_, v___x_1761_, v___x_1760_, v___x_1759_, v___x_1758_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(lean_object* v_t_1764_, lean_object* v_k_1765_){
_start:
{
if (lean_obj_tag(v_t_1764_) == 0)
{
lean_object* v_k_1766_; lean_object* v_v_1767_; lean_object* v_l_1768_; lean_object* v_r_1769_; uint8_t v___x_1770_; 
v_k_1766_ = lean_ctor_get(v_t_1764_, 1);
v_v_1767_ = lean_ctor_get(v_t_1764_, 2);
v_l_1768_ = lean_ctor_get(v_t_1764_, 3);
v_r_1769_ = lean_ctor_get(v_t_1764_, 4);
v___x_1770_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1765_, v_k_1766_);
switch(v___x_1770_)
{
case 0:
{
v_t_1764_ = v_l_1768_;
goto _start;
}
case 1:
{
lean_inc(v_v_1767_);
return v_v_1767_;
}
default: 
{
v_t_1764_ = v_r_1769_;
goto _start;
}
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3);
v___x_1774_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2_spec__4(v___x_1773_);
return v___x_1774_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___boxed(lean_object* v_t_1775_, lean_object* v_k_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_t_1775_, v_k_1776_);
lean_dec(v_k_1776_);
lean_dec(v_t_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(lean_object* v___x_1778_, lean_object* v_args_1779_, uint8_t v___x_1780_, lean_object* v_derivedValMap_1781_, lean_object* v_x_1782_, lean_object* v_x_1783_){
_start:
{
if (lean_obj_tag(v_x_1783_) == 0)
{
return v_x_1782_;
}
else
{
lean_object* v_head_1784_; lean_object* v_tail_1785_; uint8_t v___y_1801_; lean_object* v_cinfo_1813_; lean_object* v_parents_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v_head_1784_ = lean_ctor_get(v_x_1783_, 0);
lean_inc(v_head_1784_);
v_tail_1785_ = lean_ctor_get(v_x_1783_, 1);
lean_inc(v_tail_1785_);
lean_dec_ref_known(v_x_1783_, 2);
v_cinfo_1813_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_1781_, v_head_1784_);
v_parents_1814_ = lean_ctor_get(v_cinfo_1813_, 0);
lean_inc_ref(v_parents_1814_);
lean_dec_ref(v_cinfo_1813_);
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = lean_array_get_size(v_parents_1814_);
v___x_1817_ = lean_nat_dec_lt(v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_dec_ref(v_parents_1814_);
goto v___jp_1804_;
}
else
{
if (v___x_1817_ == 0)
{
lean_dec_ref(v_parents_1814_);
goto v___jp_1804_;
}
else
{
size_t v___x_1818_; size_t v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = ((size_t)0ULL);
v___x_1819_ = lean_usize_of_nat(v___x_1816_);
v___x_1820_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_1782_, v_parents_1814_, v___x_1818_, v___x_1819_);
lean_dec_ref(v_parents_1814_);
if (v___x_1820_ == 0)
{
goto v___jp_1804_;
}
else
{
lean_object* v___x_1821_; 
v___x_1821_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1778_, v_args_1779_, v___x_1780_, v_head_1784_, v_derivedValMap_1781_, v_x_1782_);
lean_dec(v_head_1784_);
v_x_1782_ = v___x_1821_;
v_x_1783_ = v_tail_1785_;
goto _start;
}
}
}
v___jp_1786_:
{
lean_object* v_vars_1787_; lean_object* v_borrows_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1799_; 
v_vars_1787_ = lean_ctor_get(v_x_1782_, 0);
v_borrows_1788_ = lean_ctor_get(v_x_1782_, 1);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_x_1782_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1790_ = v_x_1782_;
v_isShared_1791_ = v_isSharedCheck_1799_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_borrows_1788_);
lean_inc(v_vars_1787_);
lean_dec(v_x_1782_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1799_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1792_ = lean_box(0);
lean_inc(v_head_1784_);
v___x_1793_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_1788_, v_head_1784_, v___x_1792_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 1, v___x_1793_);
v___x_1795_ = v___x_1790_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_vars_1787_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1796_; 
v___x_1796_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1778_, v_args_1779_, v___x_1780_, v_head_1784_, v_derivedValMap_1781_, v___x_1795_);
lean_dec(v_head_1784_);
v_x_1782_ = v___x_1796_;
v_x_1783_ = v_tail_1785_;
goto _start;
}
}
}
v___jp_1800_:
{
if (v___y_1801_ == 0)
{
lean_object* v___x_1802_; 
v___x_1802_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1778_, v_args_1779_, v___x_1780_, v_head_1784_, v_derivedValMap_1781_, v_x_1782_);
lean_dec(v_head_1784_);
v_x_1782_ = v___x_1802_;
v_x_1783_ = v_tail_1785_;
goto _start;
}
else
{
goto v___jp_1786_;
}
}
v___jp_1804_:
{
lean_object* v_vars_1805_; uint8_t v___x_1806_; 
v_vars_1805_ = lean_ctor_get(v___x_1778_, 0);
v___x_1806_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1805_, v_head_1784_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_array_get_size(v_args_1779_);
v___x_1809_ = lean_nat_dec_lt(v___x_1807_, v___x_1808_);
if (v___x_1809_ == 0)
{
goto v___jp_1786_;
}
else
{
if (v___x_1809_ == 0)
{
goto v___jp_1786_;
}
else
{
size_t v___x_1810_; size_t v___x_1811_; uint8_t v___x_1812_; 
v___x_1810_ = ((size_t)0ULL);
v___x_1811_ = lean_usize_of_nat(v___x_1808_);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_head_1784_, v_args_1779_, v___x_1810_, v___x_1811_);
if (v___x_1812_ == 0)
{
goto v___jp_1786_;
}
else
{
v___y_1801_ = v___x_1806_;
goto v___jp_1800_;
}
}
}
}
else
{
v___y_1801_ = v___x_1780_;
goto v___jp_1800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(lean_object* v___x_1823_, lean_object* v_args_1824_, uint8_t v___x_1825_, lean_object* v_derivedValMap_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_){
_start:
{
if (lean_obj_tag(v_x_1828_) == 0)
{
return v_x_1827_;
}
else
{
lean_object* v_head_1829_; lean_object* v_tail_1830_; uint8_t v___y_1846_; lean_object* v_cinfo_1858_; lean_object* v_parents_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v_head_1829_ = lean_ctor_get(v_x_1828_, 0);
lean_inc(v_head_1829_);
v_tail_1830_ = lean_ctor_get(v_x_1828_, 1);
lean_inc(v_tail_1830_);
lean_dec_ref_known(v_x_1828_, 2);
v_cinfo_1858_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_1826_, v_head_1829_);
v_parents_1859_ = lean_ctor_get(v_cinfo_1858_, 0);
lean_inc_ref(v_parents_1859_);
lean_dec_ref(v_cinfo_1858_);
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = lean_array_get_size(v_parents_1859_);
v___x_1862_ = lean_nat_dec_lt(v___x_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_dec_ref(v_parents_1859_);
goto v___jp_1849_;
}
else
{
if (v___x_1862_ == 0)
{
lean_dec_ref(v_parents_1859_);
goto v___jp_1849_;
}
else
{
size_t v___x_1863_; size_t v___x_1864_; uint8_t v___x_1865_; 
v___x_1863_ = ((size_t)0ULL);
v___x_1864_ = lean_usize_of_nat(v___x_1861_);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_1827_, v_parents_1859_, v___x_1863_, v___x_1864_);
lean_dec_ref(v_parents_1859_);
if (v___x_1865_ == 0)
{
goto v___jp_1849_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1823_, v_args_1824_, v___x_1825_, v_head_1829_, v_derivedValMap_1826_, v_x_1827_);
lean_dec(v_head_1829_);
v___x_1867_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1823_, v_args_1824_, v___x_1825_, v_derivedValMap_1826_, v___x_1866_, v_tail_1830_);
return v___x_1867_;
}
}
}
v___jp_1831_:
{
lean_object* v_vars_1832_; lean_object* v_borrows_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1844_; 
v_vars_1832_ = lean_ctor_get(v_x_1827_, 0);
v_borrows_1833_ = lean_ctor_get(v_x_1827_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_x_1827_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1835_ = v_x_1827_;
v_isShared_1836_ = v_isSharedCheck_1844_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_borrows_1833_);
lean_inc(v_vars_1832_);
lean_dec(v_x_1827_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1844_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1837_ = lean_box(0);
lean_inc(v_head_1829_);
v___x_1838_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_1833_, v_head_1829_, v___x_1837_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 1, v___x_1838_);
v___x_1840_ = v___x_1835_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_vars_1832_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1823_, v_args_1824_, v___x_1825_, v_head_1829_, v_derivedValMap_1826_, v___x_1840_);
lean_dec(v_head_1829_);
v___x_1842_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1823_, v_args_1824_, v___x_1825_, v_derivedValMap_1826_, v___x_1841_, v_tail_1830_);
return v___x_1842_;
}
}
}
v___jp_1845_:
{
if (v___y_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1823_, v_args_1824_, v___x_1825_, v_head_1829_, v_derivedValMap_1826_, v_x_1827_);
lean_dec(v_head_1829_);
v___x_1848_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1823_, v_args_1824_, v___x_1825_, v_derivedValMap_1826_, v___x_1847_, v_tail_1830_);
return v___x_1848_;
}
else
{
goto v___jp_1831_;
}
}
v___jp_1849_:
{
lean_object* v_vars_1850_; uint8_t v___x_1851_; 
v_vars_1850_ = lean_ctor_get(v___x_1823_, 0);
v___x_1851_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1850_, v_head_1829_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = lean_unsigned_to_nat(0u);
v___x_1853_ = lean_array_get_size(v_args_1824_);
v___x_1854_ = lean_nat_dec_lt(v___x_1852_, v___x_1853_);
if (v___x_1854_ == 0)
{
goto v___jp_1831_;
}
else
{
if (v___x_1854_ == 0)
{
goto v___jp_1831_;
}
else
{
size_t v___x_1855_; size_t v___x_1856_; uint8_t v___x_1857_; 
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = lean_usize_of_nat(v___x_1853_);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_head_1829_, v_args_1824_, v___x_1855_, v___x_1856_);
if (v___x_1857_ == 0)
{
goto v___jp_1831_;
}
else
{
v___y_1846_ = v___x_1851_;
goto v___jp_1845_;
}
}
}
}
else
{
v___y_1846_ = v___x_1825_;
goto v___jp_1845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(lean_object* v___x_1868_, lean_object* v_args_1869_, uint8_t v___x_1870_, lean_object* v_fvarId_1871_, lean_object* v_derivedValMap_1872_, lean_object* v_liveVars_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_derivedValMap_1872_, v_fvarId_1871_);
if (lean_obj_tag(v___x_1874_) == 1)
{
lean_object* v_val_1875_; lean_object* v_children_1876_; lean_object* v___x_1877_; 
v_val_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_val_1875_);
lean_dec_ref_known(v___x_1874_, 1);
v_children_1876_ = lean_ctor_get(v_val_1875_, 1);
lean_inc(v_children_1876_);
lean_dec(v_val_1875_);
v___x_1877_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(v___x_1868_, v_args_1869_, v___x_1870_, v_derivedValMap_1872_, v_liveVars_1873_, v_children_1876_);
return v___x_1877_;
}
else
{
lean_dec(v___x_1874_);
return v_liveVars_1873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1___boxed(lean_object* v___x_1878_, lean_object* v_args_1879_, lean_object* v___x_1880_, lean_object* v_fvarId_1881_, lean_object* v_derivedValMap_1882_, lean_object* v_liveVars_1883_){
_start:
{
uint8_t v___x_2270__boxed_1884_; lean_object* v_res_1885_; 
v___x_2270__boxed_1884_ = lean_unbox(v___x_1880_);
v_res_1885_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1878_, v_args_1879_, v___x_2270__boxed_1884_, v_fvarId_1881_, v_derivedValMap_1882_, v_liveVars_1883_);
lean_dec(v_derivedValMap_1882_);
lean_dec(v_fvarId_1881_);
lean_dec_ref(v_args_1879_);
lean_dec_ref(v___x_1878_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v___x_1886_, lean_object* v_args_1887_, lean_object* v___x_1888_, lean_object* v_derivedValMap_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
uint8_t v___x_2275__boxed_1892_; lean_object* v_res_1893_; 
v___x_2275__boxed_1892_ = lean_unbox(v___x_1888_);
v_res_1893_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1886_, v_args_1887_, v___x_2275__boxed_1892_, v_derivedValMap_1889_, v_x_1890_, v_x_1891_);
lean_dec(v_derivedValMap_1889_);
lean_dec_ref(v_args_1887_);
lean_dec_ref(v___x_1886_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4___boxed(lean_object* v___x_1894_, lean_object* v_args_1895_, lean_object* v___x_1896_, lean_object* v_derivedValMap_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
uint8_t v___x_2307__boxed_1900_; lean_object* v_res_1901_; 
v___x_2307__boxed_1900_ = lean_unbox(v___x_1896_);
v_res_1901_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(v___x_1894_, v_args_1895_, v___x_2307__boxed_1900_, v_derivedValMap_1897_, v_x_1898_, v_x_1899_);
lean_dec(v_derivedValMap_1897_);
lean_dec_ref(v_args_1895_);
lean_dec_ref(v___x_1894_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(lean_object* v_args_1902_, lean_object* v_fvarId_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v___x_1907_; lean_object* v_vars_1908_; uint8_t v___x_1909_; 
v___x_1907_ = lean_st_ref_get(v_a_1905_);
v_vars_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc_ref(v_vars_1908_);
lean_dec(v___x_1907_);
v___x_1909_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1908_, v_fvarId_1903_);
lean_dec_ref(v_vars_1908_);
if (v___x_1909_ == 0)
{
lean_object* v_derivedValMap_1910_; lean_object* v___x_1911_; lean_object* v_vars_1912_; lean_object* v_borrows_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1927_; 
v_derivedValMap_1910_ = lean_ctor_get(v_a_1904_, 2);
v___x_1911_ = lean_st_ref_take(v_a_1905_);
v_vars_1912_ = lean_ctor_get(v___x_1911_, 0);
v_borrows_1913_ = lean_ctor_get(v___x_1911_, 1);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1915_ = v___x_1911_;
v_isShared_1916_ = v_isSharedCheck_1927_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_borrows_1913_);
lean_inc(v_vars_1912_);
lean_dec(v___x_1911_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1927_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1917_ = lean_box(0);
lean_inc(v_fvarId_1903_);
v___x_1918_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_vars_1912_, v_fvarId_1903_, v___x_1917_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1918_);
v___x_1920_ = v___x_1915_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_borrows_1913_);
v___x_1920_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1921_ = lean_st_ref_put(v_a_1905_, v___x_1920_);
v___x_1922_ = lean_st_ref_take(v_a_1905_);
lean_inc(v___x_1922_);
v___x_1923_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1922_, v_args_1902_, v___x_1909_, v_fvarId_1903_, v_derivedValMap_1910_, v___x_1922_);
lean_dec(v_fvarId_1903_);
lean_dec(v___x_1922_);
v___x_1924_ = lean_st_ref_put(v_a_1905_, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1917_);
return v___x_1925_;
}
}
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec(v_fvarId_1903_);
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg___boxed(lean_object* v_args_1930_, lean_object* v_fvarId_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_1930_, v_fvarId_1931_, v_a_1932_, v_a_1933_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec_ref(v_args_1930_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(lean_object* v_args_1936_, lean_object* v_as_1937_, size_t v_i_1938_, size_t v_stop_1939_, lean_object* v_b_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_a_1949_; uint8_t v___x_1953_; 
v___x_1953_ = lean_usize_dec_eq(v_i_1938_, v_stop_1939_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_array_uget_borrowed(v_as_1937_, v_i_1938_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v___x_1955_; 
v___x_1955_ = lean_box(0);
v_a_1949_ = v___x_1955_;
goto v___jp_1948_;
}
else
{
lean_object* v_fvarId_1956_; lean_object* v___x_1957_; 
v_fvarId_1956_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_fvarId_1956_);
v___x_1957_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_1936_, v_fvarId_1956_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v_a_1949_ = v_a_1958_;
goto v___jp_1948_;
}
else
{
return v___x_1957_;
}
}
}
else
{
lean_object* v___x_1959_; 
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_b_1940_);
return v___x_1959_;
}
v___jp_1948_:
{
size_t v___x_1950_; size_t v___x_1951_; 
v___x_1950_ = ((size_t)1ULL);
v___x_1951_ = lean_usize_add(v_i_1938_, v___x_1950_);
v_i_1938_ = v___x_1951_;
v_b_1940_ = v_a_1949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2___boxed(lean_object* v_args_1960_, lean_object* v_as_1961_, lean_object* v_i_1962_, lean_object* v_stop_1963_, lean_object* v_b_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
size_t v_i_boxed_1972_; size_t v_stop_boxed_1973_; lean_object* v_res_1974_; 
v_i_boxed_1972_ = lean_unbox_usize(v_i_1962_);
lean_dec(v_i_1962_);
v_stop_boxed_1973_ = lean_unbox_usize(v_stop_1963_);
lean_dec(v_stop_1963_);
v_res_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(v_args_1960_, v_as_1961_, v_i_boxed_1972_, v_stop_boxed_1973_, v_b_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec_ref(v_as_1961_);
lean_dec_ref(v_args_1960_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(lean_object* v_args_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = lean_array_get_size(v_args_1975_);
v___x_1985_ = lean_box(0);
v___x_1986_ = lean_nat_dec_lt(v___x_1983_, v___x_1984_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
return v___x_1987_;
}
else
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_nat_dec_le(v___x_1984_, v___x_1984_);
if (v___x_1988_ == 0)
{
if (v___x_1986_ == 0)
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1985_);
return v___x_1989_;
}
else
{
size_t v___x_1990_; size_t v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = ((size_t)0ULL);
v___x_1991_ = lean_usize_of_nat(v___x_1984_);
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(v_args_1975_, v_args_1975_, v___x_1990_, v___x_1991_, v___x_1985_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
return v___x_1992_;
}
}
else
{
size_t v___x_1993_; size_t v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = ((size_t)0ULL);
v___x_1994_ = lean_usize_of_nat(v___x_1984_);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(v_args_1975_, v_args_1975_, v___x_1993_, v___x_1994_, v___x_1985_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
return v___x_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs___boxed(lean_object* v_args_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec_ref(v_args_1996_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(lean_object* v_args_2005_, lean_object* v_fvarId_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_2005_, v_fvarId_2006_, v_a_2007_, v_a_2008_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___boxed(lean_object* v_args_2015_, lean_object* v_fvarId_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(v_args_2015_, v_fvarId_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
lean_dec_ref(v_args_2015_);
return v_res_2024_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_instMonadEIO___redArg();
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(lean_object* v_msg_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v_toApplicative_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2103_; 
v___x_2038_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0);
v___x_2039_ = l_StateRefT_x27_instMonad___redArg(v___x_2038_);
v_toApplicative_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v___x_2039_, 1);
lean_dec(v_unused_2104_);
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2103_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_toApplicative_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2103_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v_toFunctor_2044_; lean_object* v_toSeq_2045_; lean_object* v_toSeqLeft_2046_; lean_object* v_toSeqRight_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2101_; 
v_toFunctor_2044_ = lean_ctor_get(v_toApplicative_2040_, 0);
v_toSeq_2045_ = lean_ctor_get(v_toApplicative_2040_, 2);
v_toSeqLeft_2046_ = lean_ctor_get(v_toApplicative_2040_, 3);
v_toSeqRight_2047_ = lean_ctor_get(v_toApplicative_2040_, 4);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_toApplicative_2040_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; 
v_unused_2102_ = lean_ctor_get(v_toApplicative_2040_, 1);
lean_dec(v_unused_2102_);
v___x_2049_ = v_toApplicative_2040_;
v_isShared_2050_ = v_isSharedCheck_2101_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_toSeqRight_2047_);
lean_inc(v_toSeqLeft_2046_);
lean_inc(v_toSeq_2045_);
lean_inc(v_toFunctor_2044_);
lean_dec(v_toApplicative_2040_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2101_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___f_2051_; lean_object* v___f_2052_; lean_object* v___f_2053_; lean_object* v___f_2054_; lean_object* v___x_2055_; lean_object* v___f_2056_; lean_object* v___f_2057_; lean_object* v___f_2058_; lean_object* v___x_2060_; 
v___f_2051_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__1));
v___f_2052_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2044_);
v___f_2053_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2053_, 0, v_toFunctor_2044_);
v___f_2054_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2054_, 0, v_toFunctor_2044_);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___f_2053_);
lean_ctor_set(v___x_2055_, 1, v___f_2054_);
v___f_2056_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2056_, 0, v_toSeqRight_2047_);
v___f_2057_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2057_, 0, v_toSeqLeft_2046_);
v___f_2058_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2058_, 0, v_toSeq_2045_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 4, v___f_2056_);
lean_ctor_set(v___x_2049_, 3, v___f_2057_);
lean_ctor_set(v___x_2049_, 2, v___f_2058_);
lean_ctor_set(v___x_2049_, 1, v___f_2051_);
lean_ctor_set(v___x_2049_, 0, v___x_2055_);
v___x_2060_ = v___x_2049_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___f_2051_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v___f_2058_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v___f_2057_);
lean_ctor_set(v_reuseFailAlloc_2100_, 4, v___f_2056_);
v___x_2060_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2062_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 1, v___f_2052_);
lean_ctor_set(v___x_2042_, 0, v___x_2060_);
v___x_2062_ = v___x_2042_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v___f_2052_);
v___x_2062_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2063_; lean_object* v_toApplicative_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2097_; 
v___x_2063_ = l_StateRefT_x27_instMonad___redArg(v___x_2062_);
v_toApplicative_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; 
v_unused_2098_ = lean_ctor_get(v___x_2063_, 1);
lean_dec(v_unused_2098_);
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2097_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_toApplicative_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2097_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v_toFunctor_2068_; lean_object* v_toSeq_2069_; lean_object* v_toSeqLeft_2070_; lean_object* v_toSeqRight_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2095_; 
v_toFunctor_2068_ = lean_ctor_get(v_toApplicative_2064_, 0);
v_toSeq_2069_ = lean_ctor_get(v_toApplicative_2064_, 2);
v_toSeqLeft_2070_ = lean_ctor_get(v_toApplicative_2064_, 3);
v_toSeqRight_2071_ = lean_ctor_get(v_toApplicative_2064_, 4);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_toApplicative_2064_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; 
v_unused_2096_ = lean_ctor_get(v_toApplicative_2064_, 1);
lean_dec(v_unused_2096_);
v___x_2073_ = v_toApplicative_2064_;
v_isShared_2074_ = v_isSharedCheck_2095_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_toSeqRight_2071_);
lean_inc(v_toSeqLeft_2070_);
lean_inc(v_toSeq_2069_);
lean_inc(v_toFunctor_2068_);
lean_dec(v_toApplicative_2064_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2095_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___f_2075_; lean_object* v___f_2076_; lean_object* v___f_2077_; lean_object* v___f_2078_; lean_object* v___x_2079_; lean_object* v___f_2080_; lean_object* v___f_2081_; lean_object* v___f_2082_; lean_object* v___x_2084_; 
v___f_2075_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__3));
v___f_2076_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2068_);
v___f_2077_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2077_, 0, v_toFunctor_2068_);
v___f_2078_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2078_, 0, v_toFunctor_2068_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___f_2077_);
lean_ctor_set(v___x_2079_, 1, v___f_2078_);
v___f_2080_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2080_, 0, v_toSeqRight_2071_);
v___f_2081_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2081_, 0, v_toSeqLeft_2070_);
v___f_2082_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2082_, 0, v_toSeq_2069_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v___f_2080_);
lean_ctor_set(v___x_2073_, 3, v___f_2081_);
lean_ctor_set(v___x_2073_, 2, v___f_2082_);
lean_ctor_set(v___x_2073_, 1, v___f_2075_);
lean_ctor_set(v___x_2073_, 0, v___x_2079_);
v___x_2084_ = v___x_2073_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___f_2075_);
lean_ctor_set(v_reuseFailAlloc_2094_, 2, v___f_2082_);
lean_ctor_set(v_reuseFailAlloc_2094_, 3, v___f_2081_);
lean_ctor_set(v_reuseFailAlloc_2094_, 4, v___f_2080_);
v___x_2084_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2086_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 1, v___f_2076_);
lean_ctor_set(v___x_2066_, 0, v___x_2084_);
v___x_2086_ = v___x_2066_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___f_2076_);
v___x_2086_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___f_2090_; lean_object* v___x_1110__overap_2091_; lean_object* v___x_2092_; 
v___x_2087_ = l_StateRefT_x27_instMonad___redArg(v___x_2086_);
v___x_2088_ = lean_box(0);
v___x_2089_ = l_instInhabitedOfMonad___redArg(v___x_2087_, v___x_2088_);
v___f_2090_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2090_, 0, v___x_2089_);
v___x_1110__overap_2091_ = lean_panic_fn_borrowed(v___f_2090_, v_msg_2030_);
lean_dec_ref(v___f_2090_);
lean_inc(v___y_2036_);
lean_inc_ref(v___y_2035_);
lean_inc(v___y_2034_);
lean_inc_ref(v___y_2033_);
lean_inc(v___y_2032_);
lean_inc_ref(v___y_2031_);
v___x_2092_ = lean_apply_7(v___x_1110__overap_2091_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, lean_box(0));
return v___x_2092_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___boxed(lean_object* v_msg_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(v_msg_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_2114_, uint8_t v___x_2115_, lean_object* v_derivedValMap_2116_, lean_object* v_x_2117_, lean_object* v_x_2118_){
_start:
{
if (lean_obj_tag(v_x_2118_) == 0)
{
return v_x_2117_;
}
else
{
lean_object* v_head_2119_; lean_object* v_tail_2120_; lean_object* v_cinfo_2140_; lean_object* v_parents_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v_head_2119_ = lean_ctor_get(v_x_2118_, 0);
lean_inc(v_head_2119_);
v_tail_2120_ = lean_ctor_get(v_x_2118_, 1);
lean_inc(v_tail_2120_);
lean_dec_ref_known(v_x_2118_, 2);
v_cinfo_2140_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2116_, v_head_2119_);
v_parents_2141_ = lean_ctor_get(v_cinfo_2140_, 0);
lean_inc_ref(v_parents_2141_);
lean_dec_ref(v_cinfo_2140_);
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = lean_array_get_size(v_parents_2141_);
v___x_2144_ = lean_nat_dec_lt(v___x_2142_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_dec_ref(v_parents_2141_);
goto v___jp_2135_;
}
else
{
if (v___x_2144_ == 0)
{
lean_dec_ref(v_parents_2141_);
goto v___jp_2135_;
}
else
{
size_t v___x_2145_; size_t v___x_2146_; uint8_t v___x_2147_; 
v___x_2145_ = ((size_t)0ULL);
v___x_2146_ = lean_usize_of_nat(v___x_2143_);
v___x_2147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2117_, v_parents_2141_, v___x_2145_, v___x_2146_);
lean_dec_ref(v_parents_2141_);
if (v___x_2147_ == 0)
{
goto v___jp_2135_;
}
else
{
lean_object* v___x_2148_; 
v___x_2148_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2114_, v___x_2115_, v_head_2119_, v_derivedValMap_2116_, v_x_2117_);
lean_dec(v_head_2119_);
v_x_2117_ = v___x_2148_;
v_x_2118_ = v_tail_2120_;
goto _start;
}
}
}
v___jp_2121_:
{
lean_object* v_vars_2122_; lean_object* v_borrows_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2134_; 
v_vars_2122_ = lean_ctor_get(v_x_2117_, 0);
v_borrows_2123_ = lean_ctor_get(v_x_2117_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_x_2117_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2125_ = v_x_2117_;
v_isShared_2126_ = v_isSharedCheck_2134_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_borrows_2123_);
lean_inc(v_vars_2122_);
lean_dec(v_x_2117_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2134_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2127_ = lean_box(0);
lean_inc(v_head_2119_);
v___x_2128_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2123_, v_head_2119_, v___x_2127_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 1, v___x_2128_);
v___x_2130_ = v___x_2125_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_vars_2122_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; 
v___x_2131_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2114_, v___x_2115_, v_head_2119_, v_derivedValMap_2116_, v___x_2130_);
lean_dec(v_head_2119_);
v_x_2117_ = v___x_2131_;
v_x_2118_ = v_tail_2120_;
goto _start;
}
}
}
v___jp_2135_:
{
lean_object* v_vars_2136_; uint8_t v___x_2137_; 
v_vars_2136_ = lean_ctor_get(v___x_2114_, 0);
v___x_2137_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2136_, v_head_2119_);
if (v___x_2137_ == 0)
{
goto v___jp_2121_;
}
else
{
if (v___x_2115_ == 0)
{
lean_object* v___x_2138_; 
v___x_2138_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2114_, v___x_2115_, v_head_2119_, v_derivedValMap_2116_, v_x_2117_);
lean_dec(v_head_2119_);
v_x_2117_ = v___x_2138_;
v_x_2118_ = v_tail_2120_;
goto _start;
}
else
{
goto v___jp_2121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(lean_object* v___x_2150_, uint8_t v___x_2151_, lean_object* v_derivedValMap_2152_, lean_object* v_x_2153_, lean_object* v_x_2154_){
_start:
{
if (lean_obj_tag(v_x_2154_) == 0)
{
return v_x_2153_;
}
else
{
lean_object* v_head_2155_; lean_object* v_tail_2156_; lean_object* v_cinfo_2176_; lean_object* v_parents_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v_head_2155_ = lean_ctor_get(v_x_2154_, 0);
lean_inc(v_head_2155_);
v_tail_2156_ = lean_ctor_get(v_x_2154_, 1);
lean_inc(v_tail_2156_);
lean_dec_ref_known(v_x_2154_, 2);
v_cinfo_2176_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2152_, v_head_2155_);
v_parents_2177_ = lean_ctor_get(v_cinfo_2176_, 0);
lean_inc_ref(v_parents_2177_);
lean_dec_ref(v_cinfo_2176_);
v___x_2178_ = lean_unsigned_to_nat(0u);
v___x_2179_ = lean_array_get_size(v_parents_2177_);
v___x_2180_ = lean_nat_dec_lt(v___x_2178_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_dec_ref(v_parents_2177_);
goto v___jp_2171_;
}
else
{
if (v___x_2180_ == 0)
{
lean_dec_ref(v_parents_2177_);
goto v___jp_2171_;
}
else
{
size_t v___x_2181_; size_t v___x_2182_; uint8_t v___x_2183_; 
v___x_2181_ = ((size_t)0ULL);
v___x_2182_ = lean_usize_of_nat(v___x_2179_);
v___x_2183_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2153_, v_parents_2177_, v___x_2181_, v___x_2182_);
lean_dec_ref(v_parents_2177_);
if (v___x_2183_ == 0)
{
goto v___jp_2171_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2150_, v___x_2151_, v_head_2155_, v_derivedValMap_2152_, v_x_2153_);
lean_dec(v_head_2155_);
v___x_2185_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2150_, v___x_2151_, v_derivedValMap_2152_, v___x_2184_, v_tail_2156_);
return v___x_2185_;
}
}
}
v___jp_2157_:
{
lean_object* v_vars_2158_; lean_object* v_borrows_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2170_; 
v_vars_2158_ = lean_ctor_get(v_x_2153_, 0);
v_borrows_2159_ = lean_ctor_get(v_x_2153_, 1);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_x_2153_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2161_ = v_x_2153_;
v_isShared_2162_ = v_isSharedCheck_2170_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_borrows_2159_);
lean_inc(v_vars_2158_);
lean_dec(v_x_2153_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2170_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2163_ = lean_box(0);
lean_inc(v_head_2155_);
v___x_2164_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2159_, v_head_2155_, v___x_2163_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v___x_2164_);
v___x_2166_ = v___x_2161_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_vars_2158_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2150_, v___x_2151_, v_head_2155_, v_derivedValMap_2152_, v___x_2166_);
lean_dec(v_head_2155_);
v___x_2168_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2150_, v___x_2151_, v_derivedValMap_2152_, v___x_2167_, v_tail_2156_);
return v___x_2168_;
}
}
}
v___jp_2171_:
{
lean_object* v_vars_2172_; uint8_t v___x_2173_; 
v_vars_2172_ = lean_ctor_get(v___x_2150_, 0);
v___x_2173_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2172_, v_head_2155_);
if (v___x_2173_ == 0)
{
goto v___jp_2157_;
}
else
{
if (v___x_2151_ == 0)
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2150_, v___x_2151_, v_head_2155_, v_derivedValMap_2152_, v_x_2153_);
lean_dec(v_head_2155_);
v___x_2175_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2150_, v___x_2151_, v_derivedValMap_2152_, v___x_2174_, v_tail_2156_);
return v___x_2175_;
}
else
{
goto v___jp_2157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(lean_object* v___x_2186_, uint8_t v___x_2187_, lean_object* v_fvarId_2188_, lean_object* v_derivedValMap_2189_, lean_object* v_liveVars_2190_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_derivedValMap_2189_, v_fvarId_2188_);
if (lean_obj_tag(v___x_2191_) == 1)
{
lean_object* v_val_2192_; lean_object* v_children_2193_; lean_object* v___x_2194_; 
v_val_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_val_2192_);
lean_dec_ref_known(v___x_2191_, 1);
v_children_2193_ = lean_ctor_get(v_val_2192_, 1);
lean_inc(v_children_2193_);
lean_dec(v_val_2192_);
v___x_2194_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(v___x_2186_, v___x_2187_, v_derivedValMap_2189_, v_liveVars_2190_, v_children_2193_);
return v___x_2194_;
}
else
{
lean_dec(v___x_2191_);
return v_liveVars_2190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0___boxed(lean_object* v___x_2195_, lean_object* v___x_2196_, lean_object* v_fvarId_2197_, lean_object* v_derivedValMap_2198_, lean_object* v_liveVars_2199_){
_start:
{
uint8_t v___x_1727__boxed_2200_; lean_object* v_res_2201_; 
v___x_1727__boxed_2200_ = lean_unbox(v___x_2196_);
v_res_2201_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2195_, v___x_1727__boxed_2200_, v_fvarId_2197_, v_derivedValMap_2198_, v_liveVars_2199_);
lean_dec(v_derivedValMap_2198_);
lean_dec(v_fvarId_2197_);
lean_dec_ref(v___x_2195_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v___x_2202_, lean_object* v___x_2203_, lean_object* v_derivedValMap_2204_, lean_object* v_x_2205_, lean_object* v_x_2206_){
_start:
{
uint8_t v___x_1732__boxed_2207_; lean_object* v_res_2208_; 
v___x_1732__boxed_2207_ = lean_unbox(v___x_2203_);
v_res_2208_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2202_, v___x_1732__boxed_2207_, v_derivedValMap_2204_, v_x_2205_, v_x_2206_);
lean_dec(v_derivedValMap_2204_);
lean_dec_ref(v___x_2202_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2___boxed(lean_object* v___x_2209_, lean_object* v___x_2210_, lean_object* v_derivedValMap_2211_, lean_object* v_x_2212_, lean_object* v_x_2213_){
_start:
{
uint8_t v___x_1756__boxed_2214_; lean_object* v_res_2215_; 
v___x_1756__boxed_2214_ = lean_unbox(v___x_2210_);
v_res_2215_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(v___x_2209_, v___x_1756__boxed_2214_, v_derivedValMap_2211_, v_x_2212_, v_x_2213_);
lean_dec(v_derivedValMap_2211_);
lean_dec_ref(v___x_2209_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(lean_object* v_fvarId_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v___x_2220_; lean_object* v_vars_2221_; uint8_t v___x_2222_; 
v___x_2220_ = lean_st_ref_get(v_a_2218_);
v_vars_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc_ref(v_vars_2221_);
lean_dec(v___x_2220_);
v___x_2222_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2221_, v_fvarId_2216_);
lean_dec_ref(v_vars_2221_);
if (v___x_2222_ == 0)
{
lean_object* v_derivedValMap_2223_; lean_object* v___x_2224_; lean_object* v_vars_2225_; lean_object* v_borrows_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2240_; 
v_derivedValMap_2223_ = lean_ctor_get(v_a_2217_, 2);
v___x_2224_ = lean_st_ref_take(v_a_2218_);
v_vars_2225_ = lean_ctor_get(v___x_2224_, 0);
v_borrows_2226_ = lean_ctor_get(v___x_2224_, 1);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2228_ = v___x_2224_;
v_isShared_2229_ = v_isSharedCheck_2240_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_borrows_2226_);
lean_inc(v_vars_2225_);
lean_dec(v___x_2224_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2240_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2230_ = lean_box(0);
lean_inc(v_fvarId_2216_);
v___x_2231_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_vars_2225_, v_fvarId_2216_, v___x_2230_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2231_);
v___x_2233_ = v___x_2228_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_borrows_2226_);
v___x_2233_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2234_ = lean_st_ref_put(v_a_2218_, v___x_2233_);
v___x_2235_ = lean_st_ref_take(v_a_2218_);
lean_inc(v___x_2235_);
v___x_2236_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2235_, v___x_2222_, v_fvarId_2216_, v_derivedValMap_2223_, v___x_2235_);
lean_dec(v_fvarId_2216_);
lean_dec(v___x_2235_);
v___x_2237_ = lean_st_ref_put(v_a_2218_, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2230_);
return v___x_2238_;
}
}
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_dec(v_fvarId_2216_);
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
return v___x_2242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg___boxed(lean_object* v_fvarId_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2243_, v_a_2244_, v_a_2245_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
return v_res_2247_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_2250_ = lean_unsigned_to_nat(20u);
v___x_2251_ = lean_unsigned_to_nat(343u);
v___x_2252_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__0));
v___x_2253_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_2254_ = l_mkPanicMessageWithDecl(v___x_2253_, v___x_2252_, v___x_2251_, v___x_2250_, v___x_2249_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(lean_object* v_value_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
switch(lean_obj_tag(v_value_2255_))
{
case 4:
{
lean_object* v_fvarId_2263_; lean_object* v_args_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_fvarId_2263_ = lean_ctor_get(v_value_2255_, 0);
lean_inc(v_fvarId_2263_);
v_args_2264_ = lean_ctor_get(v_value_2255_, 1);
lean_inc_ref(v_args_2264_);
lean_dec_ref_known(v_value_2255_, 2);
v___x_2265_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2263_, v_a_2256_, v_a_2257_);
lean_dec_ref(v___x_2265_);
v___x_2266_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2264_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec_ref(v_args_2264_);
return v___x_2266_;
}
case 5:
{
lean_object* v_args_2267_; lean_object* v___x_2268_; 
v_args_2267_ = lean_ctor_get(v_value_2255_, 1);
lean_inc_ref(v_args_2267_);
lean_dec_ref_known(v_value_2255_, 2);
v___x_2268_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2267_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec_ref(v_args_2267_);
return v___x_2268_;
}
case 6:
{
lean_object* v_var_2269_; lean_object* v___x_2270_; 
v_var_2269_ = lean_ctor_get(v_value_2255_, 1);
lean_inc(v_var_2269_);
lean_dec_ref_known(v_value_2255_, 2);
v___x_2270_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2269_, v_a_2256_, v_a_2257_);
return v___x_2270_;
}
case 7:
{
lean_object* v_var_2271_; lean_object* v___x_2272_; 
v_var_2271_ = lean_ctor_get(v_value_2255_, 1);
lean_inc(v_var_2271_);
lean_dec_ref_known(v_value_2255_, 2);
v___x_2272_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2271_, v_a_2256_, v_a_2257_);
return v___x_2272_;
}
case 8:
{
lean_object* v_var_2273_; lean_object* v___x_2274_; 
v_var_2273_ = lean_ctor_get(v_value_2255_, 2);
lean_inc(v_var_2273_);
lean_dec_ref_known(v_value_2255_, 3);
v___x_2274_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2273_, v_a_2256_, v_a_2257_);
return v___x_2274_;
}
case 9:
{
lean_object* v_args_2275_; lean_object* v___x_2276_; 
v_args_2275_ = lean_ctor_get(v_value_2255_, 1);
lean_inc_ref(v_args_2275_);
lean_dec_ref_known(v_value_2255_, 2);
v___x_2276_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2275_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec_ref(v_args_2275_);
return v___x_2276_;
}
case 10:
{
lean_object* v_args_2277_; lean_object* v___x_2278_; 
v_args_2277_ = lean_ctor_get(v_value_2255_, 1);
lean_inc_ref(v_args_2277_);
lean_dec_ref_known(v_value_2255_, 2);
v___x_2278_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2277_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec_ref(v_args_2277_);
return v___x_2278_;
}
case 11:
{
lean_object* v_var_2279_; lean_object* v___x_2280_; 
v_var_2279_ = lean_ctor_get(v_value_2255_, 1);
lean_inc(v_var_2279_);
lean_dec_ref_known(v_value_2255_, 2);
v___x_2280_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2279_, v_a_2256_, v_a_2257_);
return v___x_2280_;
}
case 12:
{
lean_object* v_var_2281_; lean_object* v_args_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v_var_2281_ = lean_ctor_get(v_value_2255_, 0);
lean_inc(v_var_2281_);
v_args_2282_ = lean_ctor_get(v_value_2255_, 2);
lean_inc_ref(v_args_2282_);
lean_dec_ref_known(v_value_2255_, 3);
v___x_2283_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2281_, v_a_2256_, v_a_2257_);
lean_dec_ref(v___x_2283_);
v___x_2284_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2282_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec_ref(v_args_2282_);
return v___x_2284_;
}
case 13:
{
lean_object* v_fvarId_2285_; lean_object* v___x_2286_; 
v_fvarId_2285_ = lean_ctor_get(v_value_2255_, 1);
lean_inc(v_fvarId_2285_);
lean_dec_ref_known(v_value_2255_, 2);
v___x_2286_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2285_, v_a_2256_, v_a_2257_);
return v___x_2286_;
}
case 14:
{
lean_object* v_fvarId_2287_; lean_object* v___x_2288_; 
v_fvarId_2287_ = lean_ctor_get(v_value_2255_, 0);
lean_inc(v_fvarId_2287_);
lean_dec_ref_known(v_value_2255_, 1);
v___x_2288_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2287_, v_a_2256_, v_a_2257_);
return v___x_2288_;
}
case 15:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_dec_ref_known(v_value_2255_, 1);
v___x_2289_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1);
v___x_2290_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(v___x_2289_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
return v___x_2290_;
}
default: 
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec(v_value_2255_);
v___x_2291_ = lean_box(0);
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
return v___x_2292_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___boxed(lean_object* v_value_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(v_value_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(lean_object* v_fvarId_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2302_, v_a_2303_, v_a_2304_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___boxed(lean_object* v_fvarId_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(v_fvarId_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(lean_object* v_fvarId_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___x_2323_; lean_object* v_vars_2324_; lean_object* v_borrows_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2339_; 
v___x_2323_ = lean_st_ref_take(v_a_2321_);
v_vars_2324_ = lean_ctor_get(v___x_2323_, 0);
v_borrows_2325_ = lean_ctor_get(v___x_2323_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2327_ = v___x_2323_;
v_isShared_2328_ = v_isSharedCheck_2339_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_borrows_2325_);
lean_inc(v_vars_2324_);
lean_dec(v___x_2323_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2339_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v_vars_2332_; lean_object* v_borrows_2333_; lean_object* v___x_2335_; 
v___x_2329_ = lean_box(0);
v___x_2330_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_2331_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
lean_inc(v_fvarId_2320_);
v_vars_2332_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2330_, v___x_2331_, v_vars_2324_, v_fvarId_2320_);
v_borrows_2333_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2330_, v___x_2331_, v_borrows_2325_, v_fvarId_2320_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 1, v_borrows_2333_);
lean_ctor_set(v___x_2327_, 0, v_vars_2332_);
v___x_2335_ = v___x_2327_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_vars_2332_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_borrows_2333_);
v___x_2335_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = lean_st_ref_put(v_a_2321_, v___x_2335_);
v___x_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2329_);
return v___x_2337_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg___boxed(lean_object* v_fvarId_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(v_fvarId_2340_, v_a_2341_);
lean_dec(v_a_2341_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(lean_object* v_fvarId_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v_vars_2353_; lean_object* v_borrows_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2368_; 
v___x_2352_ = lean_st_ref_take(v_a_2346_);
v_vars_2353_ = lean_ctor_get(v___x_2352_, 0);
v_borrows_2354_ = lean_ctor_get(v___x_2352_, 1);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2356_ = v___x_2352_;
v_isShared_2357_ = v_isSharedCheck_2368_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_borrows_2354_);
lean_inc(v_vars_2353_);
lean_dec(v___x_2352_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2368_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v_vars_2361_; lean_object* v_borrows_2362_; lean_object* v___x_2364_; 
v___x_2358_ = lean_box(0);
v___x_2359_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_2360_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
lean_inc(v_fvarId_2344_);
v_vars_2361_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2359_, v___x_2360_, v_vars_2353_, v_fvarId_2344_);
v_borrows_2362_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2359_, v___x_2360_, v_borrows_2354_, v_fvarId_2344_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 1, v_borrows_2362_);
lean_ctor_set(v___x_2356_, 0, v_vars_2361_);
v___x_2364_ = v___x_2356_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_vars_2361_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_borrows_2362_);
v___x_2364_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_st_ref_put(v_a_2346_, v___x_2364_);
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2358_);
return v___x_2366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___boxed(lean_object* v_fvarId_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(v_fvarId_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(lean_object* v_liveVars_2378_, lean_object* v_derivedValMap_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_){
_start:
{
if (lean_obj_tag(v_x_2381_) == 0)
{
return v_x_2380_;
}
else
{
lean_object* v_head_2382_; lean_object* v_tail_2383_; lean_object* v_cinfo_2402_; lean_object* v_parents_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v_head_2382_ = lean_ctor_get(v_x_2381_, 0);
lean_inc(v_head_2382_);
v_tail_2383_ = lean_ctor_get(v_x_2381_, 1);
lean_inc(v_tail_2383_);
lean_dec_ref_known(v_x_2381_, 2);
v_cinfo_2402_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2379_, v_head_2382_);
v_parents_2403_ = lean_ctor_get(v_cinfo_2402_, 0);
lean_inc_ref(v_parents_2403_);
lean_dec_ref(v_cinfo_2402_);
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = lean_array_get_size(v_parents_2403_);
v___x_2406_ = lean_nat_dec_lt(v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_dec_ref(v_parents_2403_);
goto v___jp_2384_;
}
else
{
if (v___x_2406_ == 0)
{
lean_dec_ref(v_parents_2403_);
goto v___jp_2384_;
}
else
{
size_t v___x_2407_; size_t v___x_2408_; uint8_t v___x_2409_; 
v___x_2407_ = ((size_t)0ULL);
v___x_2408_ = lean_usize_of_nat(v___x_2405_);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2380_, v_parents_2403_, v___x_2407_, v___x_2408_);
lean_dec_ref(v_parents_2403_);
if (v___x_2409_ == 0)
{
goto v___jp_2384_;
}
else
{
lean_object* v___x_2410_; 
v___x_2410_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2378_, v_head_2382_, v_derivedValMap_2379_, v_x_2380_);
lean_dec(v_head_2382_);
v_x_2380_ = v___x_2410_;
v_x_2381_ = v_tail_2383_;
goto _start;
}
}
}
v___jp_2384_:
{
lean_object* v_vars_2385_; uint8_t v___x_2386_; 
v_vars_2385_ = lean_ctor_get(v_liveVars_2378_, 0);
v___x_2386_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2385_, v_head_2382_);
if (v___x_2386_ == 0)
{
lean_object* v_vars_2387_; lean_object* v_borrows_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2399_; 
v_vars_2387_ = lean_ctor_get(v_x_2380_, 0);
v_borrows_2388_ = lean_ctor_get(v_x_2380_, 1);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_x_2380_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2390_ = v_x_2380_;
v_isShared_2391_ = v_isSharedCheck_2399_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_borrows_2388_);
lean_inc(v_vars_2387_);
lean_dec(v_x_2380_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2399_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2392_ = lean_box(0);
lean_inc(v_head_2382_);
v___x_2393_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2388_, v_head_2382_, v___x_2392_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v___x_2393_);
v___x_2395_ = v___x_2390_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_vars_2387_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; 
v___x_2396_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2378_, v_head_2382_, v_derivedValMap_2379_, v___x_2395_);
lean_dec(v_head_2382_);
v_x_2380_ = v___x_2396_;
v_x_2381_ = v_tail_2383_;
goto _start;
}
}
}
else
{
lean_object* v___x_2400_; 
v___x_2400_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2378_, v_head_2382_, v_derivedValMap_2379_, v_x_2380_);
lean_dec(v_head_2382_);
v_x_2380_ = v___x_2400_;
v_x_2381_ = v_tail_2383_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(lean_object* v_liveVars_2412_, lean_object* v_derivedValMap_2413_, lean_object* v_x_2414_, lean_object* v_x_2415_){
_start:
{
if (lean_obj_tag(v_x_2415_) == 0)
{
return v_x_2414_;
}
else
{
lean_object* v_head_2416_; lean_object* v_tail_2417_; lean_object* v_cinfo_2436_; lean_object* v_parents_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v_head_2416_ = lean_ctor_get(v_x_2415_, 0);
lean_inc(v_head_2416_);
v_tail_2417_ = lean_ctor_get(v_x_2415_, 1);
lean_inc(v_tail_2417_);
lean_dec_ref_known(v_x_2415_, 2);
v_cinfo_2436_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2413_, v_head_2416_);
v_parents_2437_ = lean_ctor_get(v_cinfo_2436_, 0);
lean_inc_ref(v_parents_2437_);
lean_dec_ref(v_cinfo_2436_);
v___x_2438_ = lean_unsigned_to_nat(0u);
v___x_2439_ = lean_array_get_size(v_parents_2437_);
v___x_2440_ = lean_nat_dec_lt(v___x_2438_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_dec_ref(v_parents_2437_);
goto v___jp_2418_;
}
else
{
if (v___x_2440_ == 0)
{
lean_dec_ref(v_parents_2437_);
goto v___jp_2418_;
}
else
{
size_t v___x_2441_; size_t v___x_2442_; uint8_t v___x_2443_; 
v___x_2441_ = ((size_t)0ULL);
v___x_2442_ = lean_usize_of_nat(v___x_2439_);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2414_, v_parents_2437_, v___x_2441_, v___x_2442_);
lean_dec_ref(v_parents_2437_);
if (v___x_2443_ == 0)
{
goto v___jp_2418_;
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2412_, v_head_2416_, v_derivedValMap_2413_, v_x_2414_);
lean_dec(v_head_2416_);
v___x_2445_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2412_, v_derivedValMap_2413_, v___x_2444_, v_tail_2417_);
return v___x_2445_;
}
}
}
v___jp_2418_:
{
lean_object* v_vars_2419_; uint8_t v___x_2420_; 
v_vars_2419_ = lean_ctor_get(v_liveVars_2412_, 0);
v___x_2420_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2419_, v_head_2416_);
if (v___x_2420_ == 0)
{
lean_object* v_vars_2421_; lean_object* v_borrows_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2433_; 
v_vars_2421_ = lean_ctor_get(v_x_2414_, 0);
v_borrows_2422_ = lean_ctor_get(v_x_2414_, 1);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_x_2414_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2424_ = v_x_2414_;
v_isShared_2425_ = v_isSharedCheck_2433_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_borrows_2422_);
lean_inc(v_vars_2421_);
lean_dec(v_x_2414_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2433_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2426_ = lean_box(0);
lean_inc(v_head_2416_);
v___x_2427_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2422_, v_head_2416_, v___x_2426_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 1, v___x_2427_);
v___x_2429_ = v___x_2424_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_vars_2421_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2412_, v_head_2416_, v_derivedValMap_2413_, v___x_2429_);
lean_dec(v_head_2416_);
v___x_2431_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2412_, v_derivedValMap_2413_, v___x_2430_, v_tail_2417_);
return v___x_2431_;
}
}
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2412_, v_head_2416_, v_derivedValMap_2413_, v_x_2414_);
lean_dec(v_head_2416_);
v___x_2435_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2412_, v_derivedValMap_2413_, v___x_2434_, v_tail_2417_);
return v___x_2435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(lean_object* v_liveVars_2446_, lean_object* v_fvarId_2447_, lean_object* v_derivedValMap_2448_, lean_object* v_liveVars_2449_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_derivedValMap_2448_, v_fvarId_2447_);
if (lean_obj_tag(v___x_2450_) == 1)
{
lean_object* v_val_2451_; lean_object* v_children_2452_; lean_object* v___x_2453_; 
v_val_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_val_2451_);
lean_dec_ref_known(v___x_2450_, 1);
v_children_2452_ = lean_ctor_get(v_val_2451_, 1);
lean_inc(v_children_2452_);
lean_dec(v_val_2451_);
v___x_2453_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(v_liveVars_2446_, v_derivedValMap_2448_, v_liveVars_2449_, v_children_2452_);
return v___x_2453_;
}
else
{
lean_dec(v___x_2450_);
return v_liveVars_2449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0___boxed(lean_object* v_liveVars_2454_, lean_object* v_fvarId_2455_, lean_object* v_derivedValMap_2456_, lean_object* v_liveVars_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2454_, v_fvarId_2455_, v_derivedValMap_2456_, v_liveVars_2457_);
lean_dec(v_derivedValMap_2456_);
lean_dec(v_fvarId_2455_);
lean_dec_ref(v_liveVars_2454_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1___boxed(lean_object* v_liveVars_2459_, lean_object* v_derivedValMap_2460_, lean_object* v_x_2461_, lean_object* v_x_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2459_, v_derivedValMap_2460_, v_x_2461_, v_x_2462_);
lean_dec(v_derivedValMap_2460_);
lean_dec_ref(v_liveVars_2459_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0___boxed(lean_object* v_liveVars_2464_, lean_object* v_derivedValMap_2465_, lean_object* v_x_2466_, lean_object* v_x_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(v_liveVars_2464_, v_derivedValMap_2465_, v_x_2466_, v_x_2467_);
lean_dec(v_derivedValMap_2465_);
lean_dec_ref(v_liveVars_2464_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(lean_object* v_a_2469_, lean_object* v_liveVars_2470_, lean_object* v_x_2471_, lean_object* v_x_2472_){
_start:
{
if (lean_obj_tag(v_x_2472_) == 0)
{
return v_x_2471_;
}
else
{
lean_object* v_key_2473_; lean_object* v_tail_2474_; lean_object* v_derivedValMap_2475_; lean_object* v___x_2476_; 
v_key_2473_ = lean_ctor_get(v_x_2472_, 0);
v_tail_2474_ = lean_ctor_get(v_x_2472_, 2);
v_derivedValMap_2475_ = lean_ctor_get(v_a_2469_, 2);
v___x_2476_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2470_, v_key_2473_, v_derivedValMap_2475_, v_x_2471_);
v_x_2471_ = v___x_2476_;
v_x_2472_ = v_tail_2474_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2___boxed(lean_object* v_a_2478_, lean_object* v_liveVars_2479_, lean_object* v_x_2480_, lean_object* v_x_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(v_a_2478_, v_liveVars_2479_, v_x_2480_, v_x_2481_);
lean_dec(v_x_2481_);
lean_dec_ref(v_liveVars_2479_);
lean_dec_ref(v_a_2478_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(lean_object* v_a_2483_, lean_object* v_liveVars_2484_, lean_object* v_x_2485_, lean_object* v_x_2486_){
_start:
{
if (lean_obj_tag(v_x_2486_) == 0)
{
return v_x_2485_;
}
else
{
lean_object* v_key_2487_; lean_object* v_tail_2488_; lean_object* v_derivedValMap_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_key_2487_ = lean_ctor_get(v_x_2486_, 0);
v_tail_2488_ = lean_ctor_get(v_x_2486_, 2);
v_derivedValMap_2489_ = lean_ctor_get(v_a_2483_, 2);
v___x_2490_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2484_, v_key_2487_, v_derivedValMap_2489_, v_x_2485_);
v___x_2491_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(v_a_2483_, v_liveVars_2484_, v___x_2490_, v_tail_2488_);
return v___x_2491_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1___boxed(lean_object* v_a_2492_, lean_object* v_liveVars_2493_, lean_object* v_x_2494_, lean_object* v_x_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(v_a_2492_, v_liveVars_2493_, v_x_2494_, v_x_2495_);
lean_dec(v_x_2495_);
lean_dec_ref(v_liveVars_2493_);
lean_dec_ref(v_a_2492_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(lean_object* v_a_2497_, lean_object* v_liveVars_2498_, lean_object* v_as_2499_, size_t v_i_2500_, size_t v_stop_2501_, lean_object* v_b_2502_){
_start:
{
uint8_t v___x_2503_; 
v___x_2503_ = lean_usize_dec_eq(v_i_2500_, v_stop_2501_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; size_t v___x_2506_; size_t v___x_2507_; 
v___x_2504_ = lean_array_uget_borrowed(v_as_2499_, v_i_2500_);
v___x_2505_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(v_a_2497_, v_liveVars_2498_, v_b_2502_, v___x_2504_);
v___x_2506_ = ((size_t)1ULL);
v___x_2507_ = lean_usize_add(v_i_2500_, v___x_2506_);
v_i_2500_ = v___x_2507_;
v_b_2502_ = v___x_2505_;
goto _start;
}
else
{
return v_b_2502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2___boxed(lean_object* v_a_2509_, lean_object* v_liveVars_2510_, lean_object* v_as_2511_, lean_object* v_i_2512_, lean_object* v_stop_2513_, lean_object* v_b_2514_){
_start:
{
size_t v_i_boxed_2515_; size_t v_stop_boxed_2516_; lean_object* v_res_2517_; 
v_i_boxed_2515_ = lean_unbox_usize(v_i_2512_);
lean_dec(v_i_2512_);
v_stop_boxed_2516_ = lean_unbox_usize(v_stop_2513_);
lean_dec(v_stop_2513_);
v_res_2517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2509_, v_liveVars_2510_, v_as_2511_, v_i_boxed_2515_, v_stop_boxed_2516_, v_b_2514_);
lean_dec_ref(v_as_2511_);
lean_dec_ref(v_liveVars_2510_);
lean_dec_ref(v_a_2509_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(lean_object* v_a_2518_, lean_object* v_liveVars_2519_, lean_object* v_x_2520_, lean_object* v_x_2521_){
_start:
{
if (lean_obj_tag(v_x_2521_) == 0)
{
return v_x_2520_;
}
else
{
lean_object* v_head_2522_; lean_object* v_tail_2523_; lean_object* v_derivedValMap_2524_; lean_object* v_vars_2525_; lean_object* v_borrows_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2537_; 
v_head_2522_ = lean_ctor_get(v_x_2521_, 0);
lean_inc(v_head_2522_);
v_tail_2523_ = lean_ctor_get(v_x_2521_, 1);
lean_inc(v_tail_2523_);
lean_dec_ref_known(v_x_2521_, 2);
v_derivedValMap_2524_ = lean_ctor_get(v_a_2518_, 2);
v_vars_2525_ = lean_ctor_get(v_x_2520_, 0);
v_borrows_2526_ = lean_ctor_get(v_x_2520_, 1);
v_isSharedCheck_2537_ = !lean_is_exclusive(v_x_2520_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2528_ = v_x_2520_;
v_isShared_2529_ = v_isSharedCheck_2537_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_borrows_2526_);
lean_inc(v_vars_2525_);
lean_dec(v_x_2520_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2537_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2530_ = lean_box(0);
lean_inc(v_head_2522_);
v___x_2531_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2526_, v_head_2522_, v___x_2530_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v___x_2531_);
v___x_2533_ = v___x_2528_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_vars_2525_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2534_; 
v___x_2534_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2519_, v_head_2522_, v_derivedValMap_2524_, v___x_2533_);
lean_dec(v_head_2522_);
v_x_2520_ = v___x_2534_;
v_x_2521_ = v_tail_2523_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3___boxed(lean_object* v_a_2538_, lean_object* v_liveVars_2539_, lean_object* v_x_2540_, lean_object* v_x_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(v_a_2538_, v_liveVars_2539_, v_x_2540_, v_x_2541_);
lean_dec_ref(v_liveVars_2539_);
lean_dec_ref(v_a_2538_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(lean_object* v_liveVars_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v___y_2547_; lean_object* v_unconditionalBorrows_2558_; lean_object* v___x_2559_; lean_object* v_vars_2560_; lean_object* v_buckets_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v_unconditionalBorrows_2558_ = lean_ctor_get(v_a_2544_, 1);
lean_inc(v_unconditionalBorrows_2558_);
lean_inc_ref(v_liveVars_2543_);
v___x_2559_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(v_a_2544_, v_liveVars_2543_, v_liveVars_2543_, v_unconditionalBorrows_2558_);
v_vars_2560_ = lean_ctor_get(v_liveVars_2543_, 0);
v_buckets_2561_ = lean_ctor_get(v_vars_2560_, 1);
v___x_2562_ = lean_unsigned_to_nat(0u);
v___x_2563_ = lean_array_get_size(v_buckets_2561_);
v___x_2564_ = lean_nat_dec_lt(v___x_2562_, v___x_2563_);
if (v___x_2564_ == 0)
{
v___y_2547_ = v___x_2559_;
goto v___jp_2546_;
}
else
{
size_t v___x_2565_; size_t v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = ((size_t)0ULL);
v___x_2566_ = lean_usize_of_nat(v___x_2563_);
v___x_2567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2544_, v_liveVars_2543_, v_buckets_2561_, v___x_2565_, v___x_2566_, v___x_2559_);
v___y_2547_ = v___x_2567_;
goto v___jp_2546_;
}
v___jp_2546_:
{
lean_object* v_borrows_2548_; lean_object* v_buckets_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v_borrows_2548_ = lean_ctor_get(v___y_2547_, 1);
v_buckets_2549_ = lean_ctor_get(v_borrows_2548_, 1);
v___x_2550_ = lean_unsigned_to_nat(0u);
v___x_2551_ = lean_array_get_size(v_buckets_2549_);
v___x_2552_ = lean_nat_dec_lt(v___x_2550_, v___x_2551_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; 
lean_dec_ref(v_liveVars_2543_);
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___y_2547_);
return v___x_2553_;
}
else
{
size_t v___x_2554_; size_t v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_inc_ref(v_buckets_2549_);
v___x_2554_ = ((size_t)0ULL);
v___x_2555_ = lean_usize_of_nat(v___x_2551_);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2544_, v_liveVars_2543_, v_buckets_2549_, v___x_2554_, v___x_2555_, v___y_2547_);
lean_dec_ref(v_buckets_2549_);
lean_dec_ref(v_liveVars_2543_);
v___x_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
return v___x_2557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg___boxed(lean_object* v_liveVars_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v_liveVars_2568_, v_a_2569_);
lean_dec_ref(v_a_2569_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows(lean_object* v_liveVars_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v_liveVars_2572_, v_a_2573_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___boxed(lean_object* v_liveVars_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows(v_liveVars_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2605_; 
v___x_2593_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_2594_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_2593_, v_a_2590_);
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2605_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2605_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2599_ = lean_st_ref_take(v_a_2591_);
lean_dec(v___x_2599_);
v___x_2600_ = lean_box(0);
v___x_2601_ = lean_st_ref_put(v_a_2591_, v_a_2595_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2600_);
v___x_2603_ = v___x_2597_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2600_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg___boxed(lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(v_a_2606_, v_a_2607_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2629_; 
v___x_2617_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_2618_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_2617_, v_a_2610_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2629_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2629_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2623_ = lean_st_ref_take(v_a_2611_);
lean_dec(v___x_2623_);
v___x_2624_ = lean_box(0);
v___x_2625_ = lean_st_ref_put(v_a_2611_, v_a_2619_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2624_);
v___x_2627_ = v___x_2621_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2624_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___boxed(lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(lean_object* v_fvarId_2638_, lean_object* v_k_2639_, lean_object* v_n_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_nat_dec_eq(v_n_2640_, v___x_2643_);
if (v___x_2644_ == 0)
{
lean_object* v_varMap_2645_; lean_object* v___f_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___y_2650_; uint8_t v_isDefiniteRef_2654_; 
v_varMap_2645_ = lean_ctor_get(v_a_2641_, 3);
v___f_2646_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_2647_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_fvarId_2638_);
lean_inc(v_varMap_2645_);
v___x_2648_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_2646_, v___x_2647_, v_varMap_2645_, v_fvarId_2638_);
v_isDefiniteRef_2654_ = lean_ctor_get_uint8(v___x_2648_, sizeof(void*)*2 + 1);
if (v_isDefiniteRef_2654_ == 0)
{
uint8_t v___x_2655_; 
v___x_2655_ = 1;
v___y_2650_ = v___x_2655_;
goto v___jp_2649_;
}
else
{
v___y_2650_ = v___x_2644_;
goto v___jp_2649_;
}
v___jp_2649_:
{
uint8_t v_persistent_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_persistent_2651_ = lean_ctor_get_uint8(v___x_2648_, sizeof(void*)*2 + 2);
lean_dec(v___x_2648_);
v___x_2652_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_2652_, 0, v_fvarId_2638_);
lean_ctor_set(v___x_2652_, 1, v_n_2640_);
lean_ctor_set(v___x_2652_, 2, v_k_2639_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*3, v___y_2650_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*3 + 1, v_persistent_2651_);
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
return v___x_2653_;
}
}
else
{
lean_object* v___x_2656_; 
lean_dec(v_n_2640_);
lean_dec(v_fvarId_2638_);
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_k_2639_);
return v___x_2656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg___boxed(lean_object* v_fvarId_2657_, lean_object* v_k_2658_, lean_object* v_n_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(v_fvarId_2657_, v_k_2658_, v_n_2659_, v_a_2660_);
lean_dec_ref(v_a_2660_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(lean_object* v_fvarId_2663_, lean_object* v_k_2664_, lean_object* v_n_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2673_ = lean_unsigned_to_nat(0u);
v___x_2674_ = lean_nat_dec_eq(v_n_2665_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v_varMap_2675_; lean_object* v___f_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; uint8_t v___y_2680_; uint8_t v_isDefiniteRef_2684_; 
v_varMap_2675_ = lean_ctor_get(v_a_2666_, 3);
v___f_2676_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_2677_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_fvarId_2663_);
lean_inc(v_varMap_2675_);
v___x_2678_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_2676_, v___x_2677_, v_varMap_2675_, v_fvarId_2663_);
v_isDefiniteRef_2684_ = lean_ctor_get_uint8(v___x_2678_, sizeof(void*)*2 + 1);
if (v_isDefiniteRef_2684_ == 0)
{
uint8_t v___x_2685_; 
v___x_2685_ = 1;
v___y_2680_ = v___x_2685_;
goto v___jp_2679_;
}
else
{
v___y_2680_ = v___x_2674_;
goto v___jp_2679_;
}
v___jp_2679_:
{
uint8_t v_persistent_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_persistent_2681_ = lean_ctor_get_uint8(v___x_2678_, sizeof(void*)*2 + 2);
lean_dec(v___x_2678_);
v___x_2682_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_2682_, 0, v_fvarId_2663_);
lean_ctor_set(v___x_2682_, 1, v_n_2665_);
lean_ctor_set(v___x_2682_, 2, v_k_2664_);
lean_ctor_set_uint8(v___x_2682_, sizeof(void*)*3, v___y_2680_);
lean_ctor_set_uint8(v___x_2682_, sizeof(void*)*3 + 1, v_persistent_2681_);
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
return v___x_2683_;
}
}
else
{
lean_object* v___x_2686_; 
lean_dec(v_n_2665_);
lean_dec(v_fvarId_2663_);
v___x_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2686_, 0, v_k_2664_);
return v___x_2686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___boxed(lean_object* v_fvarId_2687_, lean_object* v_k_2688_, lean_object* v_n_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(v_fvarId_2687_, v_k_2688_, v_n_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0_spec__0(lean_object* v_msg_2698_){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_2700_ = lean_panic_fn_borrowed(v___x_2699_, v_msg_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(lean_object* v_t_2701_, lean_object* v_k_2702_){
_start:
{
if (lean_obj_tag(v_t_2701_) == 0)
{
lean_object* v_k_2703_; lean_object* v_v_2704_; lean_object* v_l_2705_; lean_object* v_r_2706_; uint8_t v___x_2707_; 
v_k_2703_ = lean_ctor_get(v_t_2701_, 1);
v_v_2704_ = lean_ctor_get(v_t_2701_, 2);
v_l_2705_ = lean_ctor_get(v_t_2701_, 3);
v_r_2706_ = lean_ctor_get(v_t_2701_, 4);
v___x_2707_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2702_, v_k_2703_);
switch(v___x_2707_)
{
case 0:
{
v_t_2701_ = v_l_2705_;
goto _start;
}
case 1:
{
lean_inc(v_v_2704_);
return v_v_2704_;
}
default: 
{
v_t_2701_ = v_r_2706_;
goto _start;
}
}
}
else
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3);
v___x_2711_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0_spec__0(v___x_2710_);
return v___x_2711_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0___boxed(lean_object* v_t_2712_, lean_object* v_k_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_t_2712_, v_k_2713_);
lean_dec(v_k_2713_);
lean_dec(v_t_2712_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(lean_object* v_fvarId_2715_, lean_object* v_k_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_varMap_2719_; lean_object* v___x_2720_; lean_object* v_ctorInfo_2721_; 
v_varMap_2719_ = lean_ctor_get(v_a_2717_, 3);
v___x_2720_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_2719_, v_fvarId_2715_);
v_ctorInfo_2721_ = lean_ctor_get(v___x_2720_, 1);
lean_inc(v_ctorInfo_2721_);
if (lean_obj_tag(v_ctorInfo_2721_) == 0)
{
uint8_t v_isDefiniteRef_2722_; uint8_t v_persistent_2723_; lean_object* v___x_2724_; uint8_t v___y_2726_; 
v_isDefiniteRef_2722_ = lean_ctor_get_uint8(v___x_2720_, sizeof(void*)*2 + 1);
v_persistent_2723_ = lean_ctor_get_uint8(v___x_2720_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_2720_);
v___x_2724_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_2722_ == 0)
{
uint8_t v___x_2730_; 
v___x_2730_ = 1;
v___y_2726_ = v___x_2730_;
goto v___jp_2725_;
}
else
{
uint8_t v___x_2731_; 
v___x_2731_ = 0;
v___y_2726_ = v___x_2731_;
goto v___jp_2725_;
}
v___jp_2725_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_box(0);
v___x_2728_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_2728_, 0, v_fvarId_2715_);
lean_ctor_set(v___x_2728_, 1, v___x_2724_);
lean_ctor_set(v___x_2728_, 2, v___x_2727_);
lean_ctor_set(v___x_2728_, 3, v_k_2716_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*4, v___y_2726_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*4 + 1, v_persistent_2723_);
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
return v___x_2729_;
}
}
else
{
uint8_t v_persistent_2732_; lean_object* v_val_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2747_; 
v_persistent_2732_ = lean_ctor_get_uint8(v___x_2720_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_2720_);
v_val_2733_ = lean_ctor_get(v_ctorInfo_2721_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_ctorInfo_2721_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2735_ = v_ctorInfo_2721_;
v_isShared_2736_ = v_isSharedCheck_2747_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_val_2733_);
lean_dec(v_ctorInfo_2721_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2747_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
uint8_t v___x_2737_; 
v___x_2737_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_val_2733_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; 
lean_del_object(v___x_2735_);
lean_dec(v_val_2733_);
lean_dec(v_fvarId_2715_);
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_k_2716_);
return v___x_2738_;
}
else
{
lean_object* v_size_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; lean_object* v___x_2743_; 
v_size_2739_ = lean_ctor_get(v_val_2733_, 2);
lean_inc(v_size_2739_);
lean_dec(v_val_2733_);
v___x_2740_ = lean_unsigned_to_nat(1u);
v___x_2741_ = 0;
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v_size_2739_);
v___x_2743_ = v___x_2735_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_size_2739_);
v___x_2743_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_2744_, 0, v_fvarId_2715_);
lean_ctor_set(v___x_2744_, 1, v___x_2740_);
lean_ctor_set(v___x_2744_, 2, v___x_2743_);
lean_ctor_set(v___x_2744_, 3, v_k_2716_);
lean_ctor_set_uint8(v___x_2744_, sizeof(void*)*4, v___x_2741_);
lean_ctor_set_uint8(v___x_2744_, sizeof(void*)*4 + 1, v_persistent_2732_);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg___boxed(lean_object* v_fvarId_2748_, lean_object* v_k_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_2748_, v_k_2749_, v_a_2750_);
lean_dec_ref(v_a_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(lean_object* v_fvarId_2753_, lean_object* v_k_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_2753_, v_k_2754_, v_a_2755_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___boxed(lean_object* v_fvarId_2763_, lean_object* v_k_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(v_fvarId_2763_, v_k_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
return v_res_2772_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(lean_object* v_x_2773_, lean_object* v_x_2774_){
_start:
{
lean_object* v_snd_2775_; lean_object* v_snd_2776_; uint8_t v___x_2777_; 
v_snd_2775_ = lean_ctor_get(v_x_2773_, 1);
v_snd_2776_ = lean_ctor_get(v_x_2774_, 1);
v___x_2777_ = lean_nat_dec_lt(v_snd_2775_, v_snd_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0___boxed(lean_object* v_x_2778_, lean_object* v_x_2779_){
_start:
{
uint8_t v_res_2780_; lean_object* v_r_2781_; 
v_res_2780_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v_x_2778_, v_x_2779_);
lean_dec_ref(v_x_2779_);
lean_dec_ref(v_x_2778_);
v_r_2781_ = lean_box(v_res_2780_);
return v_r_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(lean_object* v_hi_2782_, lean_object* v_pivot_2783_, lean_object* v_as_2784_, lean_object* v_i_2785_, lean_object* v_k_2786_){
_start:
{
uint8_t v___x_2787_; 
v___x_2787_ = lean_nat_dec_lt(v_k_2786_, v_hi_2782_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_dec(v_k_2786_);
v___x_2788_ = lean_array_fswap(v_as_2784_, v_i_2785_, v_hi_2782_);
v___x_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2789_, 0, v_i_2785_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
return v___x_2789_;
}
else
{
lean_object* v___x_2790_; lean_object* v_snd_2791_; lean_object* v_snd_2792_; uint8_t v___x_2793_; 
v___x_2790_ = lean_array_fget_borrowed(v_as_2784_, v_k_2786_);
v_snd_2791_ = lean_ctor_get(v___x_2790_, 1);
v_snd_2792_ = lean_ctor_get(v_pivot_2783_, 1);
v___x_2793_ = lean_nat_dec_lt(v_snd_2791_, v_snd_2792_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_unsigned_to_nat(1u);
v___x_2795_ = lean_nat_add(v_k_2786_, v___x_2794_);
lean_dec(v_k_2786_);
v_k_2786_ = v___x_2795_;
goto _start;
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2797_ = lean_array_fswap(v_as_2784_, v_i_2785_, v_k_2786_);
v___x_2798_ = lean_unsigned_to_nat(1u);
v___x_2799_ = lean_nat_add(v_i_2785_, v___x_2798_);
lean_dec(v_i_2785_);
v___x_2800_ = lean_nat_add(v_k_2786_, v___x_2798_);
lean_dec(v_k_2786_);
v_as_2784_ = v___x_2797_;
v_i_2785_ = v___x_2799_;
v_k_2786_ = v___x_2800_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg___boxed(lean_object* v_hi_2802_, lean_object* v_pivot_2803_, lean_object* v_as_2804_, lean_object* v_i_2805_, lean_object* v_k_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(v_hi_2802_, v_pivot_2803_, v_as_2804_, v_i_2805_, v_k_2806_);
lean_dec_ref(v_pivot_2803_);
lean_dec(v_hi_2802_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(lean_object* v_n_2808_, lean_object* v_as_2809_, lean_object* v_lo_2810_, lean_object* v_hi_2811_){
_start:
{
lean_object* v___y_2813_; uint8_t v___x_2823_; 
v___x_2823_ = lean_nat_dec_lt(v_lo_2810_, v_hi_2811_);
if (v___x_2823_ == 0)
{
lean_dec(v_lo_2810_);
return v_as_2809_;
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v_mid_2826_; lean_object* v___y_2828_; lean_object* v___y_2834_; lean_object* v___x_2839_; lean_object* v___x_2840_; uint8_t v___x_2841_; 
v___x_2824_ = lean_nat_add(v_lo_2810_, v_hi_2811_);
v___x_2825_ = lean_unsigned_to_nat(1u);
v_mid_2826_ = lean_nat_shiftr(v___x_2824_, v___x_2825_);
lean_dec(v___x_2824_);
v___x_2839_ = lean_array_fget_borrowed(v_as_2809_, v_mid_2826_);
v___x_2840_ = lean_array_fget_borrowed(v_as_2809_, v_lo_2810_);
v___x_2841_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v___x_2839_, v___x_2840_);
if (v___x_2841_ == 0)
{
v___y_2834_ = v_as_2809_;
goto v___jp_2833_;
}
else
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_array_fswap(v_as_2809_, v_lo_2810_, v_mid_2826_);
v___y_2834_ = v___x_2842_;
goto v___jp_2833_;
}
v___jp_2827_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2829_ = lean_array_fget_borrowed(v___y_2828_, v_mid_2826_);
v___x_2830_ = lean_array_fget_borrowed(v___y_2828_, v_hi_2811_);
v___x_2831_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v___x_2829_, v___x_2830_);
if (v___x_2831_ == 0)
{
lean_dec(v_mid_2826_);
v___y_2813_ = v___y_2828_;
goto v___jp_2812_;
}
else
{
lean_object* v___x_2832_; 
v___x_2832_ = lean_array_fswap(v___y_2828_, v_mid_2826_, v_hi_2811_);
lean_dec(v_mid_2826_);
v___y_2813_ = v___x_2832_;
goto v___jp_2812_;
}
}
v___jp_2833_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2835_ = lean_array_fget_borrowed(v___y_2834_, v_hi_2811_);
v___x_2836_ = lean_array_fget_borrowed(v___y_2834_, v_lo_2810_);
v___x_2837_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v___x_2835_, v___x_2836_);
if (v___x_2837_ == 0)
{
v___y_2828_ = v___y_2834_;
goto v___jp_2827_;
}
else
{
lean_object* v___x_2838_; 
v___x_2838_ = lean_array_fswap(v___y_2834_, v_lo_2810_, v_hi_2811_);
v___y_2828_ = v___x_2838_;
goto v___jp_2827_;
}
}
}
v___jp_2812_:
{
lean_object* v_pivot_2814_; lean_object* v___x_2815_; lean_object* v_fst_2816_; lean_object* v_snd_2817_; uint8_t v___x_2818_; 
v_pivot_2814_ = lean_array_fget(v___y_2813_, v_hi_2811_);
lean_inc_n(v_lo_2810_, 2);
v___x_2815_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(v_hi_2811_, v_pivot_2814_, v___y_2813_, v_lo_2810_, v_lo_2810_);
lean_dec(v_pivot_2814_);
v_fst_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_fst_2816_);
v_snd_2817_ = lean_ctor_get(v___x_2815_, 1);
lean_inc(v_snd_2817_);
lean_dec_ref(v___x_2815_);
v___x_2818_ = lean_nat_dec_le(v_hi_2811_, v_fst_2816_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_n_2808_, v_snd_2817_, v_lo_2810_, v_fst_2816_);
v___x_2820_ = lean_unsigned_to_nat(1u);
v___x_2821_ = lean_nat_add(v_fst_2816_, v___x_2820_);
lean_dec(v_fst_2816_);
v_as_2809_ = v___x_2819_;
v_lo_2810_ = v___x_2821_;
goto _start;
}
else
{
lean_dec(v_fst_2816_);
lean_dec(v_lo_2810_);
return v_snd_2817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___boxed(lean_object* v_n_2843_, lean_object* v_as_2844_, lean_object* v_lo_2845_, lean_object* v_hi_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_n_2843_, v_as_2844_, v_lo_2845_, v_hi_2846_);
lean_dec(v_hi_2846_);
lean_dec(v_n_2843_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(lean_object* v_altLiveVars_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
if (lean_obj_tag(v_a_2849_) == 0)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2854_, 0, v_a_2850_);
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
return v___x_2855_;
}
else
{
lean_object* v_key_2856_; lean_object* v_tail_2857_; lean_object* v_fst_2858_; lean_object* v_snd_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2910_; 
v_key_2856_ = lean_ctor_get(v_a_2849_, 0);
v_tail_2857_ = lean_ctor_get(v_a_2849_, 2);
v_fst_2858_ = lean_ctor_get(v_a_2850_, 0);
v_snd_2859_ = lean_ctor_get(v_a_2850_, 1);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_a_2850_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2861_ = v_a_2850_;
v_isShared_2862_ = v_isSharedCheck_2910_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_snd_2859_);
lean_inc(v_fst_2858_);
lean_dec(v_a_2850_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2910_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v_varMap_2863_; lean_object* v_vars_2864_; lean_object* v_borrows_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v_varMap_2863_ = lean_ctor_get(v___y_2851_, 3);
v_vars_2864_ = lean_ctor_get(v_altLiveVars_2848_, 0);
v_borrows_2865_ = lean_ctor_get(v_altLiveVars_2848_, 1);
v___x_2866_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_2863_, v_key_2856_);
v___x_2867_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2864_, v_key_2856_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; uint8_t v_isPossibleRef_2874_; 
v___x_2868_ = lean_st_ref_get(v___y_2852_);
v_isPossibleRef_2874_ = lean_ctor_get_uint8(v___x_2866_, sizeof(void*)*2);
if (v_isPossibleRef_2874_ == 0)
{
lean_dec(v___x_2868_);
lean_dec_ref(v___x_2866_);
goto v___jp_2869_;
}
else
{
lean_object* v_idx_2875_; lean_object* v_borrows_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2887_; 
v_idx_2875_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_idx_2875_);
lean_dec_ref(v___x_2866_);
v_borrows_2876_ = lean_ctor_get(v___x_2868_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v___x_2868_, 0);
lean_dec(v_unused_2888_);
v___x_2878_ = v___x_2868_;
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_borrows_2876_);
lean_dec(v___x_2868_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
uint8_t v___x_2880_; 
v___x_2880_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_2876_, v_key_2856_);
lean_dec_ref(v_borrows_2876_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2882_; 
lean_del_object(v___x_2861_);
lean_inc(v_key_2856_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 1, v_idx_2875_);
lean_ctor_set(v___x_2878_, 0, v_key_2856_);
v___x_2882_ = v___x_2878_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_key_2856_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_idx_2875_);
v___x_2882_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = lean_array_push(v_snd_2859_, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v_fst_2858_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v_a_2849_ = v_tail_2857_;
v_a_2850_ = v___x_2884_;
goto _start;
}
}
else
{
lean_del_object(v___x_2878_);
lean_dec(v_idx_2875_);
goto v___jp_2869_;
}
}
}
v___jp_2869_:
{
lean_object* v___x_2871_; 
if (v_isShared_2862_ == 0)
{
v___x_2871_ = v___x_2861_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_fst_2858_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_snd_2859_);
v___x_2871_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
v_a_2849_ = v_tail_2857_;
v_a_2850_ = v___x_2871_;
goto _start;
}
}
}
else
{
lean_object* v___x_2889_; lean_object* v_borrows_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2908_; 
v___x_2889_ = lean_st_ref_get(v___y_2852_);
v_borrows_2895_ = lean_ctor_get(v___x_2889_, 1);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2908_ == 0)
{
lean_object* v_unused_2909_; 
v_unused_2909_ = lean_ctor_get(v___x_2889_, 0);
lean_dec(v_unused_2909_);
v___x_2897_ = v___x_2889_;
v_isShared_2898_ = v_isSharedCheck_2908_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_borrows_2895_);
lean_dec(v___x_2889_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2908_;
goto v_resetjp_2896_;
}
v___jp_2890_:
{
lean_object* v___x_2892_; 
if (v_isShared_2862_ == 0)
{
v___x_2892_ = v___x_2861_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_fst_2858_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v_snd_2859_);
v___x_2892_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
v_a_2849_ = v_tail_2857_;
v_a_2850_ = v___x_2892_;
goto _start;
}
}
v_resetjp_2896_:
{
uint8_t v___x_2899_; 
v___x_2899_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_2895_, v_key_2856_);
lean_dec_ref(v_borrows_2895_);
if (v___x_2899_ == 0)
{
lean_del_object(v___x_2897_);
lean_dec_ref(v___x_2866_);
goto v___jp_2890_;
}
else
{
uint8_t v___x_2900_; 
v___x_2900_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_2865_, v_key_2856_);
if (v___x_2900_ == 0)
{
if (v___x_2899_ == 0)
{
lean_del_object(v___x_2897_);
lean_dec_ref(v___x_2866_);
goto v___jp_2890_;
}
else
{
lean_object* v_idx_2901_; lean_object* v___x_2903_; 
lean_del_object(v___x_2861_);
v_idx_2901_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_idx_2901_);
lean_dec_ref(v___x_2866_);
lean_inc(v_key_2856_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 1, v_idx_2901_);
lean_ctor_set(v___x_2897_, 0, v_key_2856_);
v___x_2903_ = v___x_2897_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_key_2856_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_idx_2901_);
v___x_2903_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = lean_array_push(v_fst_2858_, v___x_2903_);
v___x_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
lean_ctor_set(v___x_2905_, 1, v_snd_2859_);
v_a_2849_ = v_tail_2857_;
v_a_2850_ = v___x_2905_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_2897_);
lean_dec_ref(v___x_2866_);
goto v___jp_2890_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___boxed(lean_object* v_altLiveVars_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_2911_, v_a_2912_, v_a_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v_a_2912_);
lean_dec_ref(v_altLiveVars_2911_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(lean_object* v_altLiveVars_2918_, lean_object* v_as_2919_, size_t v_sz_2920_, size_t v_i_2921_, lean_object* v_b_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
uint8_t v___x_2930_; 
v___x_2930_ = lean_usize_dec_lt(v_i_2921_, v_sz_2920_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; 
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v_b_2922_);
return v___x_2931_;
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2933_; 
v_a_2932_ = lean_array_uget_borrowed(v_as_2919_, v_i_2921_);
v___x_2933_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_2918_, v_a_2932_, v_b_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2946_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2936_ = v___x_2933_;
v_isShared_2937_ = v_isSharedCheck_2946_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2946_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
if (lean_obj_tag(v_a_2934_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2940_; 
v_a_2938_ = lean_ctor_get(v_a_2934_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v_a_2934_, 1);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 0, v_a_2938_);
v___x_2940_ = v___x_2936_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2938_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
else
{
lean_object* v_a_2942_; size_t v___x_2943_; size_t v___x_2944_; 
lean_del_object(v___x_2936_);
v_a_2942_ = lean_ctor_get(v_a_2934_, 0);
lean_inc(v_a_2942_);
lean_dec_ref_known(v_a_2934_, 1);
v___x_2943_ = ((size_t)1ULL);
v___x_2944_ = lean_usize_add(v_i_2921_, v___x_2943_);
v_i_2921_ = v___x_2944_;
v_b_2922_ = v_a_2942_;
goto _start;
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
v_a_2947_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2933_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2933_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___boxed(lean_object* v_altLiveVars_2955_, lean_object* v_as_2956_, lean_object* v_sz_2957_, lean_object* v_i_2958_, lean_object* v_b_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
size_t v_sz_boxed_2967_; size_t v_i_boxed_2968_; lean_object* v_res_2969_; 
v_sz_boxed_2967_ = lean_unbox_usize(v_sz_2957_);
lean_dec(v_sz_2957_);
v_i_boxed_2968_ = lean_unbox_usize(v_i_2958_);
lean_dec(v_i_2958_);
v_res_2969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(v_altLiveVars_2955_, v_as_2956_, v_sz_boxed_2967_, v_i_boxed_2968_, v_b_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v_as_2956_);
lean_dec_ref(v_altLiveVars_2955_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(lean_object* v_as_2970_, size_t v_i_2971_, size_t v_stop_2972_, lean_object* v_b_2973_, lean_object* v___y_2974_){
_start:
{
uint8_t v___x_2976_; 
v___x_2976_ = lean_usize_dec_eq(v_i_2971_, v_stop_2972_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; lean_object* v_fst_2978_; lean_object* v___x_2979_; 
v___x_2977_ = lean_array_uget_borrowed(v_as_2970_, v_i_2971_);
v_fst_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_fst_2978_);
v___x_2979_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fst_2978_, v_b_2973_, v___y_2974_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; size_t v___x_2981_; size_t v___x_2982_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2981_ = ((size_t)1ULL);
v___x_2982_ = lean_usize_add(v_i_2971_, v___x_2981_);
v_i_2971_ = v___x_2982_;
v_b_2973_ = v_a_2980_;
goto _start;
}
else
{
return v___x_2979_;
}
}
else
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2984_, 0, v_b_2973_);
return v___x_2984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___boxed(lean_object* v_as_2985_, lean_object* v_i_2986_, lean_object* v_stop_2987_, lean_object* v_b_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
size_t v_i_boxed_2991_; size_t v_stop_boxed_2992_; lean_object* v_res_2993_; 
v_i_boxed_2991_ = lean_unbox_usize(v_i_2986_);
lean_dec(v_i_2986_);
v_stop_boxed_2992_ = lean_unbox_usize(v_stop_2987_);
lean_dec(v_stop_2987_);
v_res_2993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_as_2985_, v_i_boxed_2991_, v_stop_boxed_2992_, v_b_2988_, v___y_2989_);
lean_dec_ref(v___y_2989_);
lean_dec_ref(v_as_2985_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(lean_object* v_as_2994_, size_t v_i_2995_, size_t v_stop_2996_, lean_object* v_b_2997_, lean_object* v___y_2998_){
_start:
{
uint8_t v___x_3000_; 
v___x_3000_ = lean_usize_dec_eq(v_i_2995_, v_stop_2996_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v_fst_3002_; lean_object* v_varMap_3003_; lean_object* v___x_3004_; uint8_t v_isDefiniteRef_3005_; lean_object* v___x_3006_; uint8_t v___y_3008_; 
v___x_3001_ = lean_array_uget_borrowed(v_as_2994_, v_i_2995_);
v_fst_3002_ = lean_ctor_get(v___x_3001_, 0);
v_varMap_3003_ = lean_ctor_get(v___y_2998_, 3);
v___x_3004_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3003_, v_fst_3002_);
v_isDefiniteRef_3005_ = lean_ctor_get_uint8(v___x_3004_, sizeof(void*)*2 + 1);
v___x_3006_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_3005_ == 0)
{
uint8_t v___x_3014_; 
v___x_3014_ = 1;
v___y_3008_ = v___x_3014_;
goto v___jp_3007_;
}
else
{
v___y_3008_ = v___x_3000_;
goto v___jp_3007_;
}
v___jp_3007_:
{
uint8_t v_persistent_3009_; lean_object* v___x_3010_; size_t v___x_3011_; size_t v___x_3012_; 
v_persistent_3009_ = lean_ctor_get_uint8(v___x_3004_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_3004_);
lean_inc(v_fst_3002_);
v___x_3010_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_3010_, 0, v_fst_3002_);
lean_ctor_set(v___x_3010_, 1, v___x_3006_);
lean_ctor_set(v___x_3010_, 2, v_b_2997_);
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*3, v___y_3008_);
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*3 + 1, v_persistent_3009_);
v___x_3011_ = ((size_t)1ULL);
v___x_3012_ = lean_usize_add(v_i_2995_, v___x_3011_);
v_i_2995_ = v___x_3012_;
v_b_2997_ = v___x_3010_;
goto _start;
}
}
else
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_b_2997_);
return v___x_3015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg___boxed(lean_object* v_as_3016_, lean_object* v_i_3017_, lean_object* v_stop_3018_, lean_object* v_b_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
size_t v_i_boxed_3022_; size_t v_stop_boxed_3023_; lean_object* v_res_3024_; 
v_i_boxed_3022_ = lean_unbox_usize(v_i_3017_);
lean_dec(v_i_3017_);
v_stop_boxed_3023_ = lean_unbox_usize(v_stop_3018_);
lean_dec(v_stop_3018_);
v_res_3024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v_as_3016_, v_i_boxed_3022_, v_stop_boxed_3023_, v_b_3019_, v___y_3020_);
lean_dec_ref(v___y_3020_);
lean_dec_ref(v_as_3016_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(lean_object* v_altLiveVars_3029_, lean_object* v_k_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v_vars_3040_; lean_object* v___x_3041_; lean_object* v_buckets_3042_; size_t v_sz_3043_; size_t v___x_3044_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___x_3056_; 
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3039_ = lean_st_ref_get(v_a_3032_);
v_vars_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc_ref(v_vars_3040_);
lean_dec(v___x_3039_);
v___x_3041_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1));
v_buckets_3042_ = lean_ctor_get(v_vars_3040_, 1);
lean_inc_ref(v_buckets_3042_);
lean_dec_ref(v_vars_3040_);
v_sz_3043_ = lean_array_size(v_buckets_3042_);
v___x_3044_ = ((size_t)0ULL);
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(v_altLiveVars_3029_, v_buckets_3042_, v_sz_3043_, v___x_3044_, v___x_3041_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
lean_dec_ref(v_buckets_3042_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3114_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3114_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3114_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v_fst_3061_; lean_object* v_snd_3062_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___x_3077_; lean_object* v___y_3079_; lean_object* v_a_3080_; lean_object* v___y_3086_; lean_object* v___y_3089_; lean_object* v___x_3103_; lean_object* v___y_3105_; lean_object* v___y_3106_; uint8_t v___x_3108_; 
v_fst_3061_ = lean_ctor_get(v_a_3057_, 0);
lean_inc(v_fst_3061_);
v_snd_3062_ = lean_ctor_get(v_a_3057_, 1);
lean_inc(v_snd_3062_);
lean_dec(v_a_3057_);
v___x_3077_ = lean_unsigned_to_nat(1u);
v___x_3103_ = lean_array_get_size(v_snd_3062_);
v___x_3108_ = lean_nat_dec_eq(v___x_3103_, v___x_3038_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___y_3111_; uint8_t v___x_3113_; 
v___x_3109_ = lean_nat_sub(v___x_3103_, v___x_3077_);
v___x_3113_ = lean_nat_dec_le(v___x_3038_, v___x_3109_);
if (v___x_3113_ == 0)
{
lean_inc(v___x_3109_);
v___y_3111_ = v___x_3109_;
goto v___jp_3110_;
}
else
{
v___y_3111_ = v___x_3038_;
goto v___jp_3110_;
}
v___jp_3110_:
{
uint8_t v___x_3112_; 
v___x_3112_ = lean_nat_dec_le(v___y_3111_, v___x_3109_);
if (v___x_3112_ == 0)
{
lean_dec(v___x_3109_);
lean_inc(v___y_3111_);
v___y_3105_ = v___y_3111_;
v___y_3106_ = v___y_3111_;
goto v___jp_3104_;
}
else
{
v___y_3105_ = v___y_3111_;
v___y_3106_ = v___x_3109_;
goto v___jp_3104_;
}
}
}
else
{
v___y_3089_ = v_snd_3062_;
goto v___jp_3088_;
}
v___jp_3063_:
{
lean_object* v___x_3069_; 
v___x_3069_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v___y_3067_, v_fst_3061_, v___y_3066_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec(v___y_3067_);
v___y_3046_ = v___y_3064_;
v___y_3047_ = v___y_3065_;
v___y_3048_ = v___x_3069_;
goto v___jp_3045_;
}
v___jp_3070_:
{
uint8_t v___x_3076_; 
v___x_3076_ = lean_nat_dec_le(v___y_3075_, v___y_3074_);
if (v___x_3076_ == 0)
{
lean_dec(v___y_3074_);
lean_inc(v___y_3075_);
v___y_3064_ = v___y_3071_;
v___y_3065_ = v___y_3072_;
v___y_3066_ = v___y_3075_;
v___y_3067_ = v___y_3073_;
v___y_3068_ = v___y_3075_;
goto v___jp_3063_;
}
else
{
v___y_3064_ = v___y_3071_;
v___y_3065_ = v___y_3072_;
v___y_3066_ = v___y_3075_;
v___y_3067_ = v___y_3073_;
v___y_3068_ = v___y_3074_;
goto v___jp_3063_;
}
}
v___jp_3078_:
{
lean_object* v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = lean_array_get_size(v_fst_3061_);
v___x_3082_ = lean_nat_dec_eq(v___x_3081_, v___x_3038_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; uint8_t v___x_3084_; 
v___x_3083_ = lean_nat_sub(v___x_3081_, v___x_3077_);
v___x_3084_ = lean_nat_dec_le(v___x_3038_, v___x_3083_);
if (v___x_3084_ == 0)
{
lean_inc(v___x_3083_);
v___y_3071_ = v___y_3079_;
v___y_3072_ = v_a_3080_;
v___y_3073_ = v___x_3081_;
v___y_3074_ = v___x_3083_;
v___y_3075_ = v___x_3083_;
goto v___jp_3070_;
}
else
{
v___y_3071_ = v___y_3079_;
v___y_3072_ = v_a_3080_;
v___y_3073_ = v___x_3081_;
v___y_3074_ = v___x_3083_;
v___y_3075_ = v___x_3038_;
goto v___jp_3070_;
}
}
else
{
v___y_3046_ = v___y_3079_;
v___y_3047_ = v_a_3080_;
v___y_3048_ = v_fst_3061_;
goto v___jp_3045_;
}
}
v___jp_3085_:
{
if (lean_obj_tag(v___y_3086_) == 0)
{
lean_object* v_a_3087_; 
v_a_3087_ = lean_ctor_get(v___y_3086_, 0);
lean_inc(v_a_3087_);
v___y_3079_ = v___y_3086_;
v_a_3080_ = v_a_3087_;
goto v___jp_3078_;
}
else
{
lean_dec(v_fst_3061_);
return v___y_3086_;
}
}
v___jp_3088_:
{
lean_object* v___x_3090_; uint8_t v___x_3091_; 
v___x_3090_ = lean_array_get_size(v___y_3089_);
v___x_3091_ = lean_nat_dec_lt(v___x_3038_, v___x_3090_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3093_; 
lean_dec_ref(v___y_3089_);
lean_inc_ref(v_k_3030_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v_k_3030_);
v___x_3093_ = v___x_3059_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_k_3030_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
v___y_3079_ = v___x_3093_;
v_a_3080_ = v_k_3030_;
goto v___jp_3078_;
}
}
else
{
uint8_t v___x_3095_; 
v___x_3095_ = lean_nat_dec_le(v___x_3090_, v___x_3090_);
if (v___x_3095_ == 0)
{
if (v___x_3091_ == 0)
{
lean_object* v___x_3097_; 
lean_dec_ref(v___y_3089_);
lean_inc_ref(v_k_3030_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v_k_3030_);
v___x_3097_ = v___x_3059_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_k_3030_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
v___y_3079_ = v___x_3097_;
v_a_3080_ = v_k_3030_;
goto v___jp_3078_;
}
}
else
{
size_t v___x_3099_; lean_object* v___x_3100_; 
lean_del_object(v___x_3059_);
v___x_3099_ = lean_usize_of_nat(v___x_3090_);
v___x_3100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v___y_3089_, v___x_3044_, v___x_3099_, v_k_3030_, v_a_3031_);
lean_dec_ref(v___y_3089_);
v___y_3086_ = v___x_3100_;
goto v___jp_3085_;
}
}
else
{
size_t v___x_3101_; lean_object* v___x_3102_; 
lean_del_object(v___x_3059_);
v___x_3101_ = lean_usize_of_nat(v___x_3090_);
v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v___y_3089_, v___x_3044_, v___x_3101_, v_k_3030_, v_a_3031_);
lean_dec_ref(v___y_3089_);
v___y_3086_ = v___x_3102_;
goto v___jp_3085_;
}
}
}
v___jp_3104_:
{
lean_object* v___x_3107_; 
v___x_3107_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v___x_3103_, v_snd_3062_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
v___y_3089_ = v___x_3107_;
goto v___jp_3088_;
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec_ref(v_k_3030_);
v_a_3115_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3056_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3056_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
v___jp_3045_:
{
lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3049_ = lean_array_get_size(v___y_3048_);
v___x_3050_ = lean_nat_dec_lt(v___x_3038_, v___x_3049_);
if (v___x_3050_ == 0)
{
lean_dec_ref(v___y_3048_);
lean_dec_ref(v___y_3047_);
return v___y_3046_;
}
else
{
uint8_t v___x_3051_; 
v___x_3051_ = lean_nat_dec_le(v___x_3049_, v___x_3049_);
if (v___x_3051_ == 0)
{
if (v___x_3050_ == 0)
{
lean_dec_ref(v___y_3048_);
lean_dec_ref(v___y_3047_);
return v___y_3046_;
}
else
{
size_t v___x_3052_; lean_object* v___x_3053_; 
lean_dec_ref(v___y_3046_);
v___x_3052_ = lean_usize_of_nat(v___x_3049_);
v___x_3053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v___y_3048_, v___x_3044_, v___x_3052_, v___y_3047_, v_a_3031_);
lean_dec_ref(v___y_3048_);
return v___x_3053_;
}
}
else
{
size_t v___x_3054_; lean_object* v___x_3055_; 
lean_dec_ref(v___y_3046_);
v___x_3054_ = lean_usize_of_nat(v___x_3049_);
v___x_3055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v___y_3048_, v___x_3044_, v___x_3054_, v___y_3047_, v_a_3031_);
lean_dec_ref(v___y_3048_);
return v___x_3055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___boxed(lean_object* v_altLiveVars_3123_, lean_object* v_k_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_altLiveVars_3123_, v_k_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_);
lean_dec(v_a_3130_);
lean_dec_ref(v_a_3129_);
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
lean_dec_ref(v_altLiveVars_3123_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(lean_object* v_altLiveVars_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_3133_, v_a_3134_, v_a_3135_, v___y_3136_, v___y_3137_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___boxed(lean_object* v_altLiveVars_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(v_altLiveVars_3144_, v_a_3145_, v_a_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v_a_3145_);
lean_dec_ref(v_altLiveVars_3144_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(lean_object* v_as_3155_, size_t v_i_3156_, size_t v_stop_3157_, lean_object* v_b_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v_as_3155_, v_i_3156_, v_stop_3157_, v_b_3158_, v___y_3159_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___boxed(lean_object* v_as_3167_, lean_object* v_i_3168_, lean_object* v_stop_3169_, lean_object* v_b_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
size_t v_i_boxed_3178_; size_t v_stop_boxed_3179_; lean_object* v_res_3180_; 
v_i_boxed_3178_ = lean_unbox_usize(v_i_3168_);
lean_dec(v_i_3168_);
v_stop_boxed_3179_ = lean_unbox_usize(v_stop_3169_);
lean_dec(v_stop_3169_);
v_res_3180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(v_as_3167_, v_i_boxed_3178_, v_stop_boxed_3179_, v_b_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec_ref(v_as_3167_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3(lean_object* v_n_3181_, lean_object* v_as_3182_, lean_object* v_lo_3183_, lean_object* v_hi_3184_, lean_object* v_w_3185_, lean_object* v_hlo_3186_, lean_object* v_hhi_3187_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_n_3181_, v_as_3182_, v_lo_3183_, v_hi_3184_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___boxed(lean_object* v_n_3189_, lean_object* v_as_3190_, lean_object* v_lo_3191_, lean_object* v_hi_3192_, lean_object* v_w_3193_, lean_object* v_hlo_3194_, lean_object* v_hhi_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3(v_n_3189_, v_as_3190_, v_lo_3191_, v_hi_3192_, v_w_3193_, v_hlo_3194_, v_hhi_3195_);
lean_dec(v_hi_3192_);
lean_dec(v_n_3189_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(lean_object* v_as_3197_, size_t v_i_3198_, size_t v_stop_3199_, lean_object* v_b_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_as_3197_, v_i_3198_, v_stop_3199_, v_b_3200_, v___y_3201_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___boxed(lean_object* v_as_3209_, lean_object* v_i_3210_, lean_object* v_stop_3211_, lean_object* v_b_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
size_t v_i_boxed_3220_; size_t v_stop_boxed_3221_; lean_object* v_res_3222_; 
v_i_boxed_3220_ = lean_unbox_usize(v_i_3210_);
lean_dec(v_i_3210_);
v_stop_boxed_3221_ = lean_unbox_usize(v_stop_3211_);
lean_dec(v_stop_3211_);
v_res_3222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(v_as_3209_, v_i_boxed_3220_, v_stop_boxed_3221_, v_b_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec_ref(v_as_3209_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3(lean_object* v_n_3223_, lean_object* v_lo_3224_, lean_object* v_hi_3225_, lean_object* v_hhi_3226_, lean_object* v_pivot_3227_, lean_object* v_as_3228_, lean_object* v_i_3229_, lean_object* v_k_3230_, lean_object* v_ilo_3231_, lean_object* v_ik_3232_, lean_object* v_w_3233_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(v_hi_3225_, v_pivot_3227_, v_as_3228_, v_i_3229_, v_k_3230_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___boxed(lean_object* v_n_3235_, lean_object* v_lo_3236_, lean_object* v_hi_3237_, lean_object* v_hhi_3238_, lean_object* v_pivot_3239_, lean_object* v_as_3240_, lean_object* v_i_3241_, lean_object* v_k_3242_, lean_object* v_ilo_3243_, lean_object* v_ik_3244_, lean_object* v_w_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3(v_n_3235_, v_lo_3236_, v_hi_3237_, v_hhi_3238_, v_pivot_3239_, v_as_3240_, v_i_3241_, v_k_3242_, v_ilo_3243_, v_ik_3244_, v_w_3245_);
lean_dec_ref(v_pivot_3239_);
lean_dec(v_hi_3237_);
lean_dec(v_lo_3236_);
lean_dec(v_n_3235_);
return v_res_3246_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(lean_object* v_args_3247_, lean_object* v_x_3248_, lean_object* v_n_3249_, lean_object* v_i_3250_){
_start:
{
lean_object* v_zero_3251_; uint8_t v_isZero_3252_; 
v_zero_3251_ = lean_unsigned_to_nat(0u);
v_isZero_3252_ = lean_nat_dec_eq(v_i_3250_, v_zero_3251_);
if (v_isZero_3252_ == 1)
{
lean_dec(v_i_3250_);
return v_isZero_3252_;
}
else
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v___x_3253_ = lean_box(0);
v___x_3254_ = lean_nat_sub(v_n_3249_, v_i_3250_);
v___x_3255_ = lean_array_get_borrowed(v___x_3253_, v_args_3247_, v___x_3254_);
lean_dec(v___x_3254_);
v___x_3256_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_3255_, v_x_3248_);
if (v___x_3256_ == 0)
{
lean_object* v_one_3257_; lean_object* v_n_3258_; 
v_one_3257_ = lean_unsigned_to_nat(1u);
v_n_3258_ = lean_nat_sub(v_i_3250_, v_one_3257_);
lean_dec(v_i_3250_);
v_i_3250_ = v_n_3258_;
goto _start;
}
else
{
lean_dec(v_i_3250_);
return v_isZero_3252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg___boxed(lean_object* v_args_3260_, lean_object* v_x_3261_, lean_object* v_n_3262_, lean_object* v_i_3263_){
_start:
{
uint8_t v_res_3264_; lean_object* v_r_3265_; 
v_res_3264_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3260_, v_x_3261_, v_n_3262_, v_i_3263_);
lean_dec(v_n_3262_);
lean_dec(v_x_3261_);
lean_dec_ref(v_args_3260_);
v_r_3265_ = lean_box(v_res_3264_);
return v_r_3265_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(lean_object* v_args_3266_, lean_object* v_i_3267_){
_start:
{
lean_object* v___x_3268_; lean_object* v_x_3269_; uint8_t v___x_3270_; 
v___x_3268_ = lean_box(0);
v_x_3269_ = lean_array_get_borrowed(v___x_3268_, v_args_3266_, v_i_3267_);
lean_inc(v_i_3267_);
v___x_3270_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3266_, v_x_3269_, v_i_3267_, v_i_3267_);
lean_dec(v_i_3267_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc___boxed(lean_object* v_args_3271_, lean_object* v_i_3272_){
_start:
{
uint8_t v_res_3273_; lean_object* v_r_3274_; 
v_res_3273_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3271_, v_i_3272_);
lean_dec_ref(v_args_3271_);
v_r_3274_ = lean_box(v_res_3273_);
return v_r_3274_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(lean_object* v_args_3275_, lean_object* v_x_3276_, lean_object* v_n_3277_, lean_object* v_i_3278_, lean_object* v_a_3279_){
_start:
{
uint8_t v___x_3280_; 
v___x_3280_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3275_, v_x_3276_, v_n_3277_, v_i_3278_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___boxed(lean_object* v_args_3281_, lean_object* v_x_3282_, lean_object* v_n_3283_, lean_object* v_i_3284_, lean_object* v_a_3285_){
_start:
{
uint8_t v_res_3286_; lean_object* v_r_3287_; 
v_res_3286_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(v_args_3281_, v_x_3282_, v_n_3283_, v_i_3284_, v_a_3285_);
lean_dec(v_n_3283_);
lean_dec(v_x_3282_);
lean_dec_ref(v_args_3281_);
v_r_3287_ = lean_box(v_res_3286_);
return v_r_3287_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(lean_object* v_args_3288_, lean_object* v_arg_3289_, lean_object* v_consumeParamPred_3290_, lean_object* v_n_3291_, lean_object* v_i_3292_){
_start:
{
lean_object* v_zero_3293_; uint8_t v_isZero_3294_; 
v_zero_3293_ = lean_unsigned_to_nat(0u);
v_isZero_3294_ = lean_nat_dec_eq(v_i_3292_, v_zero_3293_);
if (v_isZero_3294_ == 1)
{
uint8_t v___x_3295_; 
lean_dec(v_i_3292_);
lean_dec_ref(v_consumeParamPred_3290_);
v___x_3295_ = 0;
return v___x_3295_;
}
else
{
lean_object* v_one_3296_; lean_object* v_n_3297_; uint8_t v___y_3299_; lean_object* v___x_3301_; lean_object* v_arg_x27_3302_; 
v_one_3296_ = lean_unsigned_to_nat(1u);
v_n_3297_ = lean_nat_sub(v_i_3292_, v_one_3296_);
v___x_3301_ = lean_nat_sub(v_n_3291_, v_i_3292_);
lean_dec(v_i_3292_);
v_arg_x27_3302_ = lean_array_fget_borrowed(v_args_3288_, v___x_3301_);
if (lean_obj_tag(v_arg_x27_3302_) == 0)
{
lean_dec(v___x_3301_);
v_i_3292_ = v_n_3297_;
goto _start;
}
else
{
lean_object* v_fvarId_3304_; uint8_t v___x_3305_; 
v_fvarId_3304_ = lean_ctor_get(v_arg_x27_3302_, 0);
v___x_3305_ = l_Lean_instBEqFVarId_beq(v_arg_3289_, v_fvarId_3304_);
if (v___x_3305_ == 0)
{
lean_dec(v___x_3301_);
v___y_3299_ = v___x_3305_;
goto v___jp_3298_;
}
else
{
lean_object* v___x_3306_; uint8_t v___x_3307_; 
lean_inc_ref(v_consumeParamPred_3290_);
v___x_3306_ = lean_apply_1(v_consumeParamPred_3290_, v___x_3301_);
v___x_3307_ = lean_unbox(v___x_3306_);
if (v___x_3307_ == 0)
{
v___y_3299_ = v___x_3305_;
goto v___jp_3298_;
}
else
{
v_i_3292_ = v_n_3297_;
goto _start;
}
}
}
v___jp_3298_:
{
if (v___y_3299_ == 0)
{
v_i_3292_ = v_n_3297_;
goto _start;
}
else
{
lean_dec(v_n_3297_);
lean_dec_ref(v_consumeParamPred_3290_);
return v___y_3299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg___boxed(lean_object* v_args_3309_, lean_object* v_arg_3310_, lean_object* v_consumeParamPred_3311_, lean_object* v_n_3312_, lean_object* v_i_3313_){
_start:
{
uint8_t v_res_3314_; lean_object* v_r_3315_; 
v_res_3314_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3309_, v_arg_3310_, v_consumeParamPred_3311_, v_n_3312_, v_i_3313_);
lean_dec(v_n_3312_);
lean_dec(v_arg_3310_);
lean_dec_ref(v_args_3309_);
v_r_3315_ = lean_box(v_res_3314_);
return v_r_3315_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(lean_object* v_arg_3316_, lean_object* v_args_3317_, lean_object* v_consumeParamPred_3318_){
_start:
{
lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3319_ = lean_array_get_size(v_args_3317_);
v___x_3320_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3317_, v_arg_3316_, v_consumeParamPred_3318_, v___x_3319_, v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux___boxed(lean_object* v_arg_3321_, lean_object* v_args_3322_, lean_object* v_consumeParamPred_3323_){
_start:
{
uint8_t v_res_3324_; lean_object* v_r_3325_; 
v_res_3324_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_arg_3321_, v_args_3322_, v_consumeParamPred_3323_);
lean_dec_ref(v_args_3322_);
lean_dec(v_arg_3321_);
v_r_3325_ = lean_box(v_res_3324_);
return v_r_3325_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(lean_object* v_args_3326_, lean_object* v_arg_3327_, lean_object* v_consumeParamPred_3328_, lean_object* v_n_3329_, lean_object* v_i_3330_, lean_object* v_a_3331_){
_start:
{
uint8_t v___x_3332_; 
v___x_3332_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3326_, v_arg_3327_, v_consumeParamPred_3328_, v_n_3329_, v_i_3330_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___boxed(lean_object* v_args_3333_, lean_object* v_arg_3334_, lean_object* v_consumeParamPred_3335_, lean_object* v_n_3336_, lean_object* v_i_3337_, lean_object* v_a_3338_){
_start:
{
uint8_t v_res_3339_; lean_object* v_r_3340_; 
v_res_3339_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(v_args_3333_, v_arg_3334_, v_consumeParamPred_3335_, v_n_3336_, v_i_3337_, v_a_3338_);
lean_dec(v_n_3336_);
lean_dec(v_arg_3334_);
lean_dec_ref(v_args_3333_);
v_r_3340_ = lean_box(v_res_3339_);
return v_r_3340_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_3341_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(lean_object* v_ps_3342_, lean_object* v_i_3343_){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v_borrow_3346_; 
v___x_3344_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0);
v___x_3345_ = lean_array_get_borrowed(v___x_3344_, v_ps_3342_, v_i_3343_);
v_borrow_3346_ = lean_ctor_get_uint8(v___x_3345_, sizeof(void*)*3);
if (v_borrow_3346_ == 0)
{
uint8_t v___x_3347_; 
v___x_3347_ = 1;
return v___x_3347_;
}
else
{
uint8_t v___x_3348_; 
v___x_3348_ = 0;
return v___x_3348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed(lean_object* v_ps_3349_, lean_object* v_i_3350_){
_start:
{
uint8_t v_res_3351_; lean_object* v_r_3352_; 
v_res_3351_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(v_ps_3349_, v_i_3350_);
lean_dec(v_i_3350_);
lean_dec_ref(v_ps_3349_);
v_r_3352_ = lean_box(v_res_3351_);
return v_r_3352_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(lean_object* v_arg_3353_, lean_object* v_args_3354_, lean_object* v_ps_3355_){
_start:
{
lean_object* v___f_3356_; uint8_t v___x_3357_; 
v___f_3356_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3356_, 0, v_ps_3355_);
v___x_3357_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_arg_3353_, v_args_3354_, v___f_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___boxed(lean_object* v_arg_3358_, lean_object* v_args_3359_, lean_object* v_ps_3360_){
_start:
{
uint8_t v_res_3361_; lean_object* v_r_3362_; 
v_res_3361_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(v_arg_3358_, v_args_3359_, v_ps_3360_);
lean_dec_ref(v_args_3359_);
lean_dec(v_arg_3358_);
v_r_3362_ = lean_box(v_res_3361_);
return v_r_3362_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(lean_object* v_upperBound_3363_, lean_object* v_args_3364_, lean_object* v_arg_3365_, lean_object* v_consumeParamPred_3366_, lean_object* v_a_3367_, lean_object* v_b_3368_){
_start:
{
lean_object* v_a_3370_; uint8_t v___y_3375_; uint8_t v___x_3378_; 
v___x_3378_ = lean_nat_dec_lt(v_a_3367_, v_upperBound_3363_);
if (v___x_3378_ == 0)
{
lean_dec(v_a_3367_);
lean_dec_ref(v_consumeParamPred_3366_);
return v_b_3368_;
}
else
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_array_fget_borrowed(v_args_3364_, v_a_3367_);
if (lean_obj_tag(v___x_3379_) == 1)
{
lean_object* v_fvarId_3380_; uint8_t v___x_3381_; 
v_fvarId_3380_ = lean_ctor_get(v___x_3379_, 0);
v___x_3381_ = l_Lean_instBEqFVarId_beq(v_arg_3365_, v_fvarId_3380_);
if (v___x_3381_ == 0)
{
v___y_3375_ = v___x_3381_;
goto v___jp_3374_;
}
else
{
lean_object* v___x_3382_; uint8_t v___x_3383_; 
lean_inc_ref(v_consumeParamPred_3366_);
lean_inc(v_a_3367_);
v___x_3382_ = lean_apply_1(v_consumeParamPred_3366_, v_a_3367_);
v___x_3383_ = lean_unbox(v___x_3382_);
v___y_3375_ = v___x_3383_;
goto v___jp_3374_;
}
}
else
{
v_a_3370_ = v_b_3368_;
goto v___jp_3369_;
}
}
v___jp_3369_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = lean_unsigned_to_nat(1u);
v___x_3372_ = lean_nat_add(v_a_3367_, v___x_3371_);
lean_dec(v_a_3367_);
v_a_3367_ = v___x_3372_;
v_b_3368_ = v_a_3370_;
goto _start;
}
v___jp_3374_:
{
if (v___y_3375_ == 0)
{
v_a_3370_ = v_b_3368_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = lean_unsigned_to_nat(1u);
v___x_3377_ = lean_nat_add(v_b_3368_, v___x_3376_);
lean_dec(v_b_3368_);
v_a_3370_ = v___x_3377_;
goto v___jp_3369_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg___boxed(lean_object* v_upperBound_3384_, lean_object* v_args_3385_, lean_object* v_arg_3386_, lean_object* v_consumeParamPred_3387_, lean_object* v_a_3388_, lean_object* v_b_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v_upperBound_3384_, v_args_3385_, v_arg_3386_, v_consumeParamPred_3387_, v_a_3388_, v_b_3389_);
lean_dec(v_arg_3386_);
lean_dec_ref(v_args_3385_);
lean_dec(v_upperBound_3384_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(lean_object* v_arg_3391_, lean_object* v_args_3392_, lean_object* v_consumeParamPred_3393_){
_start:
{
lean_object* v_num_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v_num_3394_ = lean_unsigned_to_nat(0u);
v___x_3395_ = lean_array_get_size(v_args_3392_);
v___x_3396_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v___x_3395_, v_args_3392_, v_arg_3391_, v_consumeParamPred_3393_, v_num_3394_, v_num_3394_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions___boxed(lean_object* v_arg_3397_, lean_object* v_args_3398_, lean_object* v_consumeParamPred_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(v_arg_3397_, v_args_3398_, v_consumeParamPred_3399_);
lean_dec_ref(v_args_3398_);
lean_dec(v_arg_3397_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0(lean_object* v_upperBound_3401_, lean_object* v_args_3402_, lean_object* v_arg_3403_, lean_object* v_consumeParamPred_3404_, lean_object* v_inst_3405_, lean_object* v_R_3406_, lean_object* v_a_3407_, lean_object* v_b_3408_, lean_object* v_c_3409_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v_upperBound_3401_, v_args_3402_, v_arg_3403_, v_consumeParamPred_3404_, v_a_3407_, v_b_3408_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___boxed(lean_object* v_upperBound_3411_, lean_object* v_args_3412_, lean_object* v_arg_3413_, lean_object* v_consumeParamPred_3414_, lean_object* v_inst_3415_, lean_object* v_R_3416_, lean_object* v_a_3417_, lean_object* v_b_3418_, lean_object* v_c_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0(v_upperBound_3411_, v_args_3412_, v_arg_3413_, v_consumeParamPred_3414_, v_inst_3415_, v_R_3416_, v_a_3417_, v_b_3418_, v_c_3419_);
lean_dec(v_arg_3413_);
lean_dec_ref(v_args_3412_);
lean_dec(v_upperBound_3411_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(lean_object* v_fvarId_3421_, lean_object* v_b_3422_, uint8_t v___x_3423_, lean_object* v_numIncs_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v_a_3433_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v___x_3436_ = lean_unsigned_to_nat(0u);
v___x_3437_ = lean_nat_dec_eq(v_numIncs_3424_, v___x_3436_);
if (v___x_3437_ == 0)
{
lean_object* v_varMap_3438_; lean_object* v___x_3439_; uint8_t v___y_3441_; uint8_t v_isDefiniteRef_3444_; 
v_varMap_3438_ = lean_ctor_get(v___y_3425_, 3);
v___x_3439_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3438_, v_fvarId_3421_);
v_isDefiniteRef_3444_ = lean_ctor_get_uint8(v___x_3439_, sizeof(void*)*2 + 1);
if (v_isDefiniteRef_3444_ == 0)
{
v___y_3441_ = v___x_3423_;
goto v___jp_3440_;
}
else
{
v___y_3441_ = v___x_3437_;
goto v___jp_3440_;
}
v___jp_3440_:
{
uint8_t v_persistent_3442_; lean_object* v___x_3443_; 
v_persistent_3442_ = lean_ctor_get_uint8(v___x_3439_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_3439_);
v___x_3443_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_3443_, 0, v_fvarId_3421_);
lean_ctor_set(v___x_3443_, 1, v_numIncs_3424_);
lean_ctor_set(v___x_3443_, 2, v_b_3422_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*3, v___y_3441_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*3 + 1, v_persistent_3442_);
v_a_3433_ = v___x_3443_;
goto v___jp_3432_;
}
}
else
{
lean_dec(v_numIncs_3424_);
lean_dec(v_fvarId_3421_);
v_a_3433_ = v_b_3422_;
goto v___jp_3432_;
}
v___jp_3432_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3434_, 0, v_a_3433_);
v___x_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
return v___x_3435_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_3445_, lean_object* v_b_3446_, lean_object* v___x_3447_, lean_object* v_numIncs_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
uint8_t v___x_7163__boxed_3456_; lean_object* v_res_3457_; 
v___x_7163__boxed_3456_ = lean_unbox(v___x_3447_);
v_res_3457_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3445_, v_b_3446_, v___x_7163__boxed_3456_, v_numIncs_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(lean_object* v_upperBound_3458_, lean_object* v_args_3459_, lean_object* v_consumeParamPred_3460_, lean_object* v_a_3461_, lean_object* v_b_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v_a_3471_; lean_object* v___y_3476_; uint8_t v___x_3495_; 
v___x_3495_ = lean_nat_dec_lt(v_a_3461_, v_upperBound_3458_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; 
lean_dec(v_a_3461_);
lean_dec_ref(v_consumeParamPred_3460_);
v___x_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3496_, 0, v_b_3462_);
return v___x_3496_;
}
else
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_array_fget_borrowed(v_args_3459_, v_a_3461_);
if (lean_obj_tag(v___x_3497_) == 1)
{
lean_object* v_fvarId_3498_; lean_object* v_varMap_3499_; lean_object* v___x_3500_; uint8_t v_isPossibleRef_3501_; 
v_fvarId_3498_ = lean_ctor_get(v___x_3497_, 0);
v_varMap_3499_ = lean_ctor_get(v___y_3463_, 3);
v___x_3500_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3499_, v_fvarId_3498_);
v_isPossibleRef_3501_ = lean_ctor_get_uint8(v___x_3500_, sizeof(void*)*2);
lean_dec_ref(v___x_3500_);
if (v_isPossibleRef_3501_ == 0)
{
v_a_3471_ = v_b_3462_;
goto v___jp_3470_;
}
else
{
uint8_t v___x_3502_; 
lean_inc(v_a_3461_);
v___x_3502_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3459_, v_a_3461_);
if (v___x_3502_ == 0)
{
v_a_3471_ = v_b_3462_;
goto v___jp_3470_;
}
else
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v_vars_3505_; uint8_t v___x_3506_; lean_object* v___x_3507_; uint8_t v___y_3511_; 
lean_inc_ref(v_consumeParamPred_3460_);
v___x_3503_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(v_fvarId_3498_, v_args_3459_, v_consumeParamPred_3460_);
v___x_3504_ = lean_st_ref_get(v___y_3464_);
v_vars_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc_ref(v_vars_3505_);
lean_dec(v___x_3504_);
v___x_3506_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_3505_, v_fvarId_3498_);
lean_dec_ref(v_vars_3505_);
v___x_3507_ = lean_st_ref_get(v___y_3464_);
if (v___x_3506_ == 0)
{
lean_object* v_borrows_3516_; uint8_t v___x_3517_; 
v_borrows_3516_ = lean_ctor_get(v___x_3507_, 1);
lean_inc_ref(v_borrows_3516_);
lean_dec(v___x_3507_);
v___x_3517_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_3516_, v_fvarId_3498_);
lean_dec_ref(v_borrows_3516_);
v___y_3511_ = v___x_3517_;
goto v___jp_3510_;
}
else
{
lean_dec(v___x_3507_);
v___y_3511_ = v___x_3506_;
goto v___jp_3510_;
}
v___jp_3508_:
{
lean_object* v___x_3509_; 
lean_inc(v_fvarId_3498_);
v___x_3509_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3498_, v_b_3462_, v___x_3495_, v___x_3503_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
v___y_3476_ = v___x_3509_;
goto v___jp_3475_;
}
v___jp_3510_:
{
if (v___y_3511_ == 0)
{
uint8_t v___x_3512_; 
lean_inc_ref(v_consumeParamPred_3460_);
v___x_3512_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_fvarId_3498_, v_args_3459_, v_consumeParamPred_3460_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = lean_unsigned_to_nat(1u);
v___x_3514_ = lean_nat_sub(v___x_3503_, v___x_3513_);
lean_dec(v___x_3503_);
lean_inc(v_fvarId_3498_);
v___x_3515_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3498_, v_b_3462_, v___x_3495_, v___x_3514_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
v___y_3476_ = v___x_3515_;
goto v___jp_3475_;
}
else
{
goto v___jp_3508_;
}
}
else
{
goto v___jp_3508_;
}
}
}
}
}
else
{
v_a_3471_ = v_b_3462_;
goto v___jp_3470_;
}
}
v___jp_3470_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = lean_unsigned_to_nat(1u);
v___x_3473_ = lean_nat_add(v_a_3461_, v___x_3472_);
lean_dec(v_a_3461_);
v_a_3461_ = v___x_3473_;
v_b_3462_ = v_a_3471_;
goto _start;
}
v___jp_3475_:
{
if (lean_obj_tag(v___y_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3486_; 
v_a_3477_ = lean_ctor_get(v___y_3476_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___y_3476_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3479_ = v___y_3476_;
v_isShared_3480_ = v_isSharedCheck_3486_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___y_3476_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3486_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
if (lean_obj_tag(v_a_3477_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3483_; 
lean_dec(v_a_3461_);
lean_dec_ref(v_consumeParamPred_3460_);
v_a_3481_ = lean_ctor_get(v_a_3477_, 0);
lean_inc(v_a_3481_);
lean_dec_ref_known(v_a_3477_, 1);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v_a_3481_);
v___x_3483_ = v___x_3479_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3481_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
else
{
lean_object* v_a_3485_; 
lean_del_object(v___x_3479_);
v_a_3485_ = lean_ctor_get(v_a_3477_, 0);
lean_inc(v_a_3485_);
lean_dec_ref_known(v_a_3477_, 1);
v_a_3471_ = v_a_3485_;
goto v___jp_3470_;
}
}
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec(v_a_3461_);
lean_dec_ref(v_consumeParamPred_3460_);
v_a_3487_ = lean_ctor_get(v___y_3476_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___y_3476_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___y_3476_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___y_3476_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___boxed(lean_object* v_upperBound_3518_, lean_object* v_args_3519_, lean_object* v_consumeParamPred_3520_, lean_object* v_a_3521_, lean_object* v_b_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v_upperBound_3518_, v_args_3519_, v_consumeParamPred_3520_, v_a_3521_, v_b_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v_args_3519_);
lean_dec(v_upperBound_3518_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(lean_object* v_args_3531_, lean_object* v_consumeParamPred_3532_, lean_object* v_k_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_unsigned_to_nat(0u);
v___x_3542_ = lean_array_get_size(v_args_3531_);
v___x_3543_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v___x_3542_, v_args_3531_, v_consumeParamPred_3532_, v___x_3541_, v_k_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux___boxed(lean_object* v_args_3544_, lean_object* v_consumeParamPred_3545_, lean_object* v_k_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3544_, v_consumeParamPred_3545_, v_k_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec_ref(v_args_3544_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(lean_object* v_upperBound_3555_, lean_object* v_args_3556_, lean_object* v_consumeParamPred_3557_, lean_object* v_inst_3558_, lean_object* v_R_3559_, lean_object* v_a_3560_, lean_object* v_b_3561_, lean_object* v_c_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v_upperBound_3555_, v_args_3556_, v_consumeParamPred_3557_, v_a_3560_, v_b_3561_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___boxed(lean_object* v_upperBound_3571_, lean_object* v_args_3572_, lean_object* v_consumeParamPred_3573_, lean_object* v_inst_3574_, lean_object* v_R_3575_, lean_object* v_a_3576_, lean_object* v_b_3577_, lean_object* v_c_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(v_upperBound_3571_, v_args_3572_, v_consumeParamPred_3573_, v_inst_3574_, v_R_3575_, v_a_3576_, v_b_3577_, v_c_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v_args_3572_);
lean_dec(v_upperBound_3571_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(lean_object* v_args_3587_, lean_object* v_ps_3588_, lean_object* v_k_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v___f_3597_; lean_object* v___x_3598_; 
v___f_3597_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3597_, 0, v_ps_3588_);
v___x_3598_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3587_, v___f_3597_, v_k_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore___boxed(lean_object* v_args_3599_, lean_object* v_ps_3600_, lean_object* v_k_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_3599_, v_ps_3600_, v_k_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
lean_dec(v_a_3605_);
lean_dec_ref(v_a_3604_);
lean_dec(v_a_3603_);
lean_dec_ref(v_a_3602_);
lean_dec_ref(v_args_3599_);
return v_res_3609_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(lean_object* v_x_3610_){
_start:
{
uint8_t v___x_3611_; 
v___x_3611_ = 1;
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0___boxed(lean_object* v_x_3612_){
_start:
{
uint8_t v_res_3613_; lean_object* v_r_3614_; 
v_res_3613_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(v_x_3612_);
lean_dec(v_x_3612_);
v_r_3614_ = lean_box(v_res_3613_);
return v_r_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(lean_object* v_args_3616_, lean_object* v_k_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v___f_3625_; lean_object* v___x_3626_; 
v___f_3625_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___closed__0));
v___x_3626_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3616_, v___f_3625_, v_k_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___boxed(lean_object* v_args_3627_, lean_object* v_k_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_3627_, v_k_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
lean_dec(v_a_3632_);
lean_dec_ref(v_a_3631_);
lean_dec(v_a_3630_);
lean_dec_ref(v_a_3629_);
lean_dec_ref(v_args_3627_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(lean_object* v_upperBound_3637_, lean_object* v_args_3638_, lean_object* v_ps_3639_, lean_object* v_a_3640_, lean_object* v_b_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_a_3646_; uint8_t v___x_3650_; 
v___x_3650_ = lean_nat_dec_lt(v_a_3640_, v_upperBound_3637_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; 
lean_dec(v_a_3640_);
lean_dec_ref(v_ps_3639_);
v___x_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3651_, 0, v_b_3641_);
return v___x_3651_;
}
else
{
lean_object* v___x_3652_; 
v___x_3652_ = lean_array_fget_borrowed(v_args_3638_, v_a_3640_);
if (lean_obj_tag(v___x_3652_) == 0)
{
v_a_3646_ = v_b_3641_;
goto v___jp_3645_;
}
else
{
lean_object* v_fvarId_3653_; lean_object* v_varMap_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v_vars_3657_; uint8_t v___x_3658_; lean_object* v___x_3659_; uint8_t v_isPossibleRef_3660_; 
v_fvarId_3653_ = lean_ctor_get(v___x_3652_, 0);
v_varMap_3654_ = lean_ctor_get(v___y_3642_, 3);
v___x_3655_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3654_, v_fvarId_3653_);
v___x_3656_ = lean_st_ref_get(v___y_3643_);
v_vars_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc_ref(v_vars_3657_);
lean_dec(v___x_3656_);
v___x_3658_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_3657_, v_fvarId_3653_);
lean_dec_ref(v_vars_3657_);
v___x_3659_ = lean_st_ref_get(v___y_3643_);
v_isPossibleRef_3660_ = lean_ctor_get_uint8(v___x_3655_, sizeof(void*)*2);
lean_dec_ref(v___x_3655_);
if (v_isPossibleRef_3660_ == 0)
{
lean_dec(v___x_3659_);
v_a_3646_ = v_b_3641_;
goto v___jp_3645_;
}
else
{
uint8_t v___x_3661_; 
lean_inc(v_a_3640_);
v___x_3661_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3638_, v_a_3640_);
if (v___x_3661_ == 0)
{
lean_dec(v___x_3659_);
v_a_3646_ = v_b_3641_;
goto v___jp_3645_;
}
else
{
uint8_t v___x_3662_; 
lean_inc_ref(v_ps_3639_);
v___x_3662_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(v_fvarId_3653_, v_args_3638_, v_ps_3639_);
if (v___x_3662_ == 0)
{
lean_dec(v___x_3659_);
v_a_3646_ = v_b_3641_;
goto v___jp_3645_;
}
else
{
if (v___x_3658_ == 0)
{
lean_object* v_borrows_3663_; uint8_t v___x_3664_; 
v_borrows_3663_ = lean_ctor_get(v___x_3659_, 1);
lean_inc_ref(v_borrows_3663_);
lean_dec(v___x_3659_);
v___x_3664_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_3663_, v_fvarId_3653_);
lean_dec_ref(v_borrows_3663_);
if (v___x_3664_ == 0)
{
lean_object* v___x_3665_; 
lean_inc(v_fvarId_3653_);
v___x_3665_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_3653_, v_b_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3665_, 1);
v_a_3646_ = v_a_3666_;
goto v___jp_3645_;
}
else
{
lean_dec(v_a_3640_);
lean_dec_ref(v_ps_3639_);
return v___x_3665_;
}
}
else
{
v_a_3646_ = v_b_3641_;
goto v___jp_3645_;
}
}
else
{
lean_dec(v___x_3659_);
v_a_3646_ = v_b_3641_;
goto v___jp_3645_;
}
}
}
}
}
}
v___jp_3645_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = lean_unsigned_to_nat(1u);
v___x_3648_ = lean_nat_add(v_a_3640_, v___x_3647_);
lean_dec(v_a_3640_);
v_a_3640_ = v___x_3648_;
v_b_3641_ = v_a_3646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg___boxed(lean_object* v_upperBound_3667_, lean_object* v_args_3668_, lean_object* v_ps_3669_, lean_object* v_a_3670_, lean_object* v_b_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v_upperBound_3667_, v_args_3668_, v_ps_3669_, v_a_3670_, v_b_3671_, v___y_3672_, v___y_3673_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec_ref(v_args_3668_);
lean_dec(v_upperBound_3667_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(lean_object* v_args_3676_, lean_object* v_ps_3677_, lean_object* v_k_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3686_ = lean_unsigned_to_nat(0u);
v___x_3687_ = lean_array_get_size(v_args_3676_);
v___x_3688_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v___x_3687_, v_args_3676_, v_ps_3677_, v___x_3686_, v_k_3678_, v_a_3679_, v_a_3680_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp___boxed(lean_object* v_args_3689_, lean_object* v_ps_3690_, lean_object* v_k_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(v_args_3689_, v_ps_3690_, v_k_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_);
lean_dec(v_a_3697_);
lean_dec_ref(v_a_3696_);
lean_dec(v_a_3695_);
lean_dec_ref(v_a_3694_);
lean_dec(v_a_3693_);
lean_dec_ref(v_a_3692_);
lean_dec_ref(v_args_3689_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(lean_object* v_upperBound_3700_, lean_object* v_args_3701_, lean_object* v_ps_3702_, lean_object* v_inst_3703_, lean_object* v_R_3704_, lean_object* v_a_3705_, lean_object* v_b_3706_, lean_object* v_c_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v_upperBound_3700_, v_args_3701_, v_ps_3702_, v_a_3705_, v_b_3706_, v___y_3708_, v___y_3709_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___boxed(lean_object* v_upperBound_3716_, lean_object* v_args_3717_, lean_object* v_ps_3718_, lean_object* v_inst_3719_, lean_object* v_R_3720_, lean_object* v_a_3721_, lean_object* v_b_3722_, lean_object* v_c_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(v_upperBound_3716_, v_args_3717_, v_ps_3718_, v_inst_3719_, v_R_3720_, v_a_3721_, v_b_3722_, v_c_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec_ref(v_args_3717_);
lean_dec(v_upperBound_3716_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(lean_object* v_fvarId_3732_, lean_object* v_k_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v_varMap_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v_borrows_3740_; uint8_t v___x_3741_; lean_object* v___x_3742_; uint8_t v_isPossibleRef_3743_; 
v_varMap_3737_ = lean_ctor_get(v_a_3734_, 3);
v___x_3738_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3737_, v_fvarId_3732_);
v___x_3739_ = lean_st_ref_get(v_a_3735_);
v_borrows_3740_ = lean_ctor_get(v___x_3739_, 1);
lean_inc_ref(v_borrows_3740_);
lean_dec(v___x_3739_);
v___x_3741_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_3740_, v_fvarId_3732_);
lean_dec_ref(v_borrows_3740_);
v___x_3742_ = lean_st_ref_get(v_a_3735_);
v_isPossibleRef_3743_ = lean_ctor_get_uint8(v___x_3738_, sizeof(void*)*2);
lean_dec_ref(v___x_3738_);
if (v_isPossibleRef_3743_ == 0)
{
lean_object* v___x_3744_; 
lean_dec(v___x_3742_);
lean_dec(v_fvarId_3732_);
v___x_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3744_, 0, v_k_3733_);
return v___x_3744_;
}
else
{
if (v___x_3741_ == 0)
{
lean_object* v_vars_3745_; uint8_t v___x_3746_; 
v_vars_3745_ = lean_ctor_get(v___x_3742_, 0);
lean_inc_ref(v_vars_3745_);
lean_dec(v___x_3742_);
v___x_3746_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_3745_, v_fvarId_3732_);
lean_dec_ref(v_vars_3745_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3747_; 
v___x_3747_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_3732_, v_k_3733_, v_a_3734_);
return v___x_3747_;
}
else
{
lean_object* v___x_3748_; 
lean_dec(v_fvarId_3732_);
v___x_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3748_, 0, v_k_3733_);
return v___x_3748_;
}
}
else
{
lean_object* v___x_3749_; 
lean_dec(v___x_3742_);
lean_dec(v_fvarId_3732_);
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v_k_3733_);
return v___x_3749_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg___boxed(lean_object* v_fvarId_3750_, lean_object* v_k_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3750_, v_k_3751_, v_a_3752_, v_a_3753_);
lean_dec(v_a_3753_);
lean_dec_ref(v_a_3752_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(lean_object* v_fvarId_3756_, lean_object* v_k_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3756_, v_k_3757_, v_a_3758_, v_a_3759_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___boxed(lean_object* v_fvarId_3766_, lean_object* v_k_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(v_fvarId_3766_, v_k_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(lean_object* v_a_3776_, lean_object* v_x_3777_){
_start:
{
if (lean_obj_tag(v_x_3777_) == 0)
{
return v_x_3777_;
}
else
{
lean_object* v_key_3778_; lean_object* v_value_3779_; lean_object* v_tail_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3789_; 
v_key_3778_ = lean_ctor_get(v_x_3777_, 0);
v_value_3779_ = lean_ctor_get(v_x_3777_, 1);
v_tail_3780_ = lean_ctor_get(v_x_3777_, 2);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_x_3777_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3782_ = v_x_3777_;
v_isShared_3783_ = v_isSharedCheck_3789_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_tail_3780_);
lean_inc(v_value_3779_);
lean_inc(v_key_3778_);
lean_dec(v_x_3777_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3789_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
uint8_t v___x_3784_; 
v___x_3784_ = l_Lean_instBEqFVarId_beq(v_key_3778_, v_a_3776_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; lean_object* v___x_3787_; 
v___x_3785_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3776_, v_tail_3780_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 2, v___x_3785_);
v___x_3787_ = v___x_3782_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_key_3778_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v_value_3779_);
lean_ctor_set(v_reuseFailAlloc_3788_, 2, v___x_3785_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
else
{
lean_del_object(v___x_3782_);
lean_dec(v_value_3779_);
lean_dec(v_key_3778_);
return v_tail_3780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg___boxed(lean_object* v_a_3790_, lean_object* v_x_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3790_, v_x_3791_);
lean_dec(v_a_3790_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(lean_object* v_m_3793_, lean_object* v_a_3794_){
_start:
{
lean_object* v_size_3795_; lean_object* v_buckets_3796_; lean_object* v___x_3797_; uint64_t v___x_3798_; uint64_t v___x_3799_; uint64_t v___x_3800_; uint64_t v_fold_3801_; uint64_t v___x_3802_; uint64_t v___x_3803_; uint64_t v___x_3804_; size_t v___x_3805_; size_t v___x_3806_; size_t v___x_3807_; size_t v___x_3808_; size_t v___x_3809_; lean_object* v_bkt_3810_; uint8_t v___x_3811_; 
v_size_3795_ = lean_ctor_get(v_m_3793_, 0);
v_buckets_3796_ = lean_ctor_get(v_m_3793_, 1);
v___x_3797_ = lean_array_get_size(v_buckets_3796_);
v___x_3798_ = l_Lean_instHashableFVarId_hash(v_a_3794_);
v___x_3799_ = 32ULL;
v___x_3800_ = lean_uint64_shift_right(v___x_3798_, v___x_3799_);
v_fold_3801_ = lean_uint64_xor(v___x_3798_, v___x_3800_);
v___x_3802_ = 16ULL;
v___x_3803_ = lean_uint64_shift_right(v_fold_3801_, v___x_3802_);
v___x_3804_ = lean_uint64_xor(v_fold_3801_, v___x_3803_);
v___x_3805_ = lean_uint64_to_usize(v___x_3804_);
v___x_3806_ = lean_usize_of_nat(v___x_3797_);
v___x_3807_ = ((size_t)1ULL);
v___x_3808_ = lean_usize_sub(v___x_3806_, v___x_3807_);
v___x_3809_ = lean_usize_land(v___x_3805_, v___x_3808_);
v_bkt_3810_ = lean_array_uget_borrowed(v_buckets_3796_, v___x_3809_);
v___x_3811_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_3794_, v_bkt_3810_);
if (v___x_3811_ == 0)
{
return v_m_3793_;
}
else
{
lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3824_; 
lean_inc(v_bkt_3810_);
lean_inc_ref(v_buckets_3796_);
lean_inc(v_size_3795_);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_m_3793_);
if (v_isSharedCheck_3824_ == 0)
{
lean_object* v_unused_3825_; lean_object* v_unused_3826_; 
v_unused_3825_ = lean_ctor_get(v_m_3793_, 1);
lean_dec(v_unused_3825_);
v_unused_3826_ = lean_ctor_get(v_m_3793_, 0);
lean_dec(v_unused_3826_);
v___x_3813_ = v_m_3793_;
v_isShared_3814_ = v_isSharedCheck_3824_;
goto v_resetjp_3812_;
}
else
{
lean_dec(v_m_3793_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3824_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3815_; lean_object* v_buckets_x27_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3822_; 
v___x_3815_ = lean_box(0);
v_buckets_x27_3816_ = lean_array_uset(v_buckets_3796_, v___x_3809_, v___x_3815_);
v___x_3817_ = lean_unsigned_to_nat(1u);
v___x_3818_ = lean_nat_sub(v_size_3795_, v___x_3817_);
lean_dec(v_size_3795_);
v___x_3819_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3794_, v_bkt_3810_);
v___x_3820_ = lean_array_uset(v_buckets_x27_3816_, v___x_3809_, v___x_3819_);
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 1, v___x_3820_);
lean_ctor_set(v___x_3813_, 0, v___x_3818_);
v___x_3822_ = v___x_3813_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3818_);
lean_ctor_set(v_reuseFailAlloc_3823_, 1, v___x_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg___boxed(lean_object* v_m_3827_, lean_object* v_a_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_m_3827_, v_a_3828_);
lean_dec(v_a_3828_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(lean_object* v_as_3830_, size_t v_i_3831_, size_t v_stop_3832_, lean_object* v_b_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_a_3838_; uint8_t v___x_3842_; 
v___x_3842_ = lean_usize_dec_eq(v_i_3831_, v_stop_3832_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; lean_object* v_fvarId_3844_; lean_object* v___x_3845_; 
v___x_3843_ = lean_array_uget_borrowed(v_as_3830_, v_i_3831_);
v_fvarId_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_fvarId_3844_);
v___x_3845_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3844_, v_b_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3847_; lean_object* v_vars_3848_; lean_object* v_borrows_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3859_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v___x_3847_ = lean_st_ref_take(v___y_3835_);
v_vars_3848_ = lean_ctor_get(v___x_3847_, 0);
v_borrows_3849_ = lean_ctor_get(v___x_3847_, 1);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3851_ = v___x_3847_;
v_isShared_3852_ = v_isSharedCheck_3859_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_borrows_3849_);
lean_inc(v_vars_3848_);
lean_dec(v___x_3847_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3859_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v_vars_3853_; lean_object* v_borrows_3854_; lean_object* v___x_3856_; 
v_vars_3853_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_vars_3848_, v_fvarId_3844_);
v_borrows_3854_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_borrows_3849_, v_fvarId_3844_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 1, v_borrows_3854_);
lean_ctor_set(v___x_3851_, 0, v_vars_3853_);
v___x_3856_ = v___x_3851_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_vars_3853_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v_borrows_3854_);
v___x_3856_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_st_ref_put(v___y_3835_, v___x_3856_);
v_a_3838_ = v_a_3846_;
goto v___jp_3837_;
}
}
}
else
{
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3860_; 
v_a_3860_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v___x_3845_, 1);
v_a_3838_ = v_a_3860_;
goto v___jp_3837_;
}
else
{
return v___x_3845_;
}
}
}
else
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3861_, 0, v_b_3833_);
return v___x_3861_;
}
v___jp_3837_:
{
size_t v___x_3839_; size_t v___x_3840_; 
v___x_3839_ = ((size_t)1ULL);
v___x_3840_ = lean_usize_add(v_i_3831_, v___x_3839_);
v_i_3831_ = v___x_3840_;
v_b_3833_ = v_a_3838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg___boxed(lean_object* v_as_3862_, lean_object* v_i_3863_, lean_object* v_stop_3864_, lean_object* v_b_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
size_t v_i_boxed_3869_; size_t v_stop_boxed_3870_; lean_object* v_res_3871_; 
v_i_boxed_3869_ = lean_unbox_usize(v_i_3863_);
lean_dec(v_i_3863_);
v_stop_boxed_3870_ = lean_unbox_usize(v_stop_3864_);
lean_dec(v_stop_3864_);
v_res_3871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_as_3862_, v_i_boxed_3869_, v_stop_boxed_3870_, v_b_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec_ref(v_as_3862_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(lean_object* v_ps_3872_, lean_object* v_k_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3881_ = lean_unsigned_to_nat(0u);
v___x_3882_ = lean_array_get_size(v_ps_3872_);
v___x_3883_ = lean_nat_dec_lt(v___x_3881_, v___x_3882_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3884_, 0, v_k_3873_);
return v___x_3884_;
}
else
{
uint8_t v___x_3885_; 
v___x_3885_ = lean_nat_dec_le(v___x_3882_, v___x_3882_);
if (v___x_3885_ == 0)
{
if (v___x_3883_ == 0)
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3886_, 0, v_k_3873_);
return v___x_3886_;
}
else
{
size_t v___x_3887_; size_t v___x_3888_; lean_object* v___x_3889_; 
v___x_3887_ = ((size_t)0ULL);
v___x_3888_ = lean_usize_of_nat(v___x_3882_);
v___x_3889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_ps_3872_, v___x_3887_, v___x_3888_, v_k_3873_, v_a_3874_, v_a_3875_);
return v___x_3889_;
}
}
else
{
size_t v___x_3890_; size_t v___x_3891_; lean_object* v___x_3892_; 
v___x_3890_ = ((size_t)0ULL);
v___x_3891_ = lean_usize_of_nat(v___x_3882_);
v___x_3892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_ps_3872_, v___x_3890_, v___x_3891_, v_k_3873_, v_a_3874_, v_a_3875_);
return v___x_3892_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams___boxed(lean_object* v_ps_3893_, lean_object* v_k_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_ps_3893_, v_k_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
lean_dec(v_a_3900_);
lean_dec_ref(v_a_3899_);
lean_dec(v_a_3898_);
lean_dec_ref(v_a_3897_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec_ref(v_ps_3893_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(lean_object* v_00_u03b2_3903_, lean_object* v_m_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_m_3904_, v_a_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___boxed(lean_object* v_00_u03b2_3907_, lean_object* v_m_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(v_00_u03b2_3907_, v_m_3908_, v_a_3909_);
lean_dec(v_a_3909_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1(lean_object* v_as_3911_, size_t v_i_3912_, size_t v_stop_3913_, lean_object* v_b_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_as_3911_, v_i_3912_, v_stop_3913_, v_b_3914_, v___y_3915_, v___y_3916_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___boxed(lean_object* v_as_3923_, lean_object* v_i_3924_, lean_object* v_stop_3925_, lean_object* v_b_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
size_t v_i_boxed_3934_; size_t v_stop_boxed_3935_; lean_object* v_res_3936_; 
v_i_boxed_3934_ = lean_unbox_usize(v_i_3924_);
lean_dec(v_i_3924_);
v_stop_boxed_3935_ = lean_unbox_usize(v_stop_3925_);
lean_dec(v_stop_3925_);
v_res_3936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1(v_as_3923_, v_i_boxed_3934_, v_stop_boxed_3935_, v_b_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec_ref(v_as_3923_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0(lean_object* v_00_u03b2_3937_, lean_object* v_a_3938_, lean_object* v_x_3939_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3938_, v_x_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3941_, lean_object* v_a_3942_, lean_object* v_x_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0(v_00_u03b2_3941_, v_a_3942_, v_x_3943_);
lean_dec(v_a_3942_);
return v_res_3944_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(lean_object* v_msg_3946_){
_start:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0);
v___x_3948_ = lean_panic_fn_borrowed(v___x_3947_, v_msg_3946_);
return v___x_3948_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default___redArg();
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1(lean_object* v_msg_3950_){
_start:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0);
v___x_3952_ = lean_panic_fn_borrowed(v___x_3951_, v_msg_3950_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(lean_object* v_msg_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v_toApplicative_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_4026_; 
v___x_3961_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0);
v___x_3962_ = l_StateRefT_x27_instMonad___redArg(v___x_3961_);
v_toApplicative_3963_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_4026_ == 0)
{
lean_object* v_unused_4027_; 
v_unused_4027_ = lean_ctor_get(v___x_3962_, 1);
lean_dec(v_unused_4027_);
v___x_3965_ = v___x_3962_;
v_isShared_3966_ = v_isSharedCheck_4026_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_toApplicative_3963_);
lean_dec(v___x_3962_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_4026_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v_toFunctor_3967_; lean_object* v_toSeq_3968_; lean_object* v_toSeqLeft_3969_; lean_object* v_toSeqRight_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_4024_; 
v_toFunctor_3967_ = lean_ctor_get(v_toApplicative_3963_, 0);
v_toSeq_3968_ = lean_ctor_get(v_toApplicative_3963_, 2);
v_toSeqLeft_3969_ = lean_ctor_get(v_toApplicative_3963_, 3);
v_toSeqRight_3970_ = lean_ctor_get(v_toApplicative_3963_, 4);
v_isSharedCheck_4024_ = !lean_is_exclusive(v_toApplicative_3963_);
if (v_isSharedCheck_4024_ == 0)
{
lean_object* v_unused_4025_; 
v_unused_4025_ = lean_ctor_get(v_toApplicative_3963_, 1);
lean_dec(v_unused_4025_);
v___x_3972_ = v_toApplicative_3963_;
v_isShared_3973_ = v_isSharedCheck_4024_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_toSeqRight_3970_);
lean_inc(v_toSeqLeft_3969_);
lean_inc(v_toSeq_3968_);
lean_inc(v_toFunctor_3967_);
lean_dec(v_toApplicative_3963_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_4024_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___f_3974_; lean_object* v___f_3975_; lean_object* v___f_3976_; lean_object* v___f_3977_; lean_object* v___x_3978_; lean_object* v___f_3979_; lean_object* v___f_3980_; lean_object* v___f_3981_; lean_object* v___x_3983_; 
v___f_3974_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__1));
v___f_3975_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3967_);
v___f_3976_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3976_, 0, v_toFunctor_3967_);
v___f_3977_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3977_, 0, v_toFunctor_3967_);
v___x_3978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___f_3976_);
lean_ctor_set(v___x_3978_, 1, v___f_3977_);
v___f_3979_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3979_, 0, v_toSeqRight_3970_);
v___f_3980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3980_, 0, v_toSeqLeft_3969_);
v___f_3981_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3981_, 0, v_toSeq_3968_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 4, v___f_3979_);
lean_ctor_set(v___x_3972_, 3, v___f_3980_);
lean_ctor_set(v___x_3972_, 2, v___f_3981_);
lean_ctor_set(v___x_3972_, 1, v___f_3974_);
lean_ctor_set(v___x_3972_, 0, v___x_3978_);
v___x_3983_ = v___x_3972_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v___x_3978_);
lean_ctor_set(v_reuseFailAlloc_4023_, 1, v___f_3974_);
lean_ctor_set(v_reuseFailAlloc_4023_, 2, v___f_3981_);
lean_ctor_set(v_reuseFailAlloc_4023_, 3, v___f_3980_);
lean_ctor_set(v_reuseFailAlloc_4023_, 4, v___f_3979_);
v___x_3983_ = v_reuseFailAlloc_4023_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3985_; 
if (v_isShared_3966_ == 0)
{
lean_ctor_set(v___x_3965_, 1, v___f_3975_);
lean_ctor_set(v___x_3965_, 0, v___x_3983_);
v___x_3985_ = v___x_3965_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_3983_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v___f_3975_);
v___x_3985_ = v_reuseFailAlloc_4022_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3986_; lean_object* v_toApplicative_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_4020_; 
v___x_3986_ = l_StateRefT_x27_instMonad___redArg(v___x_3985_);
v_toApplicative_3987_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4020_ == 0)
{
lean_object* v_unused_4021_; 
v_unused_4021_ = lean_ctor_get(v___x_3986_, 1);
lean_dec(v_unused_4021_);
v___x_3989_ = v___x_3986_;
v_isShared_3990_ = v_isSharedCheck_4020_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_toApplicative_3987_);
lean_dec(v___x_3986_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_4020_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v_toFunctor_3991_; lean_object* v_toSeq_3992_; lean_object* v_toSeqLeft_3993_; lean_object* v_toSeqRight_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4018_; 
v_toFunctor_3991_ = lean_ctor_get(v_toApplicative_3987_, 0);
v_toSeq_3992_ = lean_ctor_get(v_toApplicative_3987_, 2);
v_toSeqLeft_3993_ = lean_ctor_get(v_toApplicative_3987_, 3);
v_toSeqRight_3994_ = lean_ctor_get(v_toApplicative_3987_, 4);
v_isSharedCheck_4018_ = !lean_is_exclusive(v_toApplicative_3987_);
if (v_isSharedCheck_4018_ == 0)
{
lean_object* v_unused_4019_; 
v_unused_4019_ = lean_ctor_get(v_toApplicative_3987_, 1);
lean_dec(v_unused_4019_);
v___x_3996_ = v_toApplicative_3987_;
v_isShared_3997_ = v_isSharedCheck_4018_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_toSeqRight_3994_);
lean_inc(v_toSeqLeft_3993_);
lean_inc(v_toSeq_3992_);
lean_inc(v_toFunctor_3991_);
lean_dec(v_toApplicative_3987_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4018_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___f_3998_; lean_object* v___f_3999_; lean_object* v___f_4000_; lean_object* v___f_4001_; lean_object* v___x_4002_; lean_object* v___f_4003_; lean_object* v___f_4004_; lean_object* v___f_4005_; lean_object* v___x_4007_; 
v___f_3998_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__3));
v___f_3999_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3991_);
v___f_4000_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4000_, 0, v_toFunctor_3991_);
v___f_4001_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4001_, 0, v_toFunctor_3991_);
v___x_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___f_4000_);
lean_ctor_set(v___x_4002_, 1, v___f_4001_);
v___f_4003_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4003_, 0, v_toSeqRight_3994_);
v___f_4004_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4004_, 0, v_toSeqLeft_3993_);
v___f_4005_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4005_, 0, v_toSeq_3992_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 4, v___f_4003_);
lean_ctor_set(v___x_3996_, 3, v___f_4004_);
lean_ctor_set(v___x_3996_, 2, v___f_4005_);
lean_ctor_set(v___x_3996_, 1, v___f_3998_);
lean_ctor_set(v___x_3996_, 0, v___x_4002_);
v___x_4007_ = v___x_3996_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_4002_);
lean_ctor_set(v_reuseFailAlloc_4017_, 1, v___f_3998_);
lean_ctor_set(v_reuseFailAlloc_4017_, 2, v___f_4005_);
lean_ctor_set(v_reuseFailAlloc_4017_, 3, v___f_4004_);
lean_ctor_set(v_reuseFailAlloc_4017_, 4, v___f_4003_);
v___x_4007_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4009_; 
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 1, v___f_3999_);
lean_ctor_set(v___x_3989_, 0, v___x_4007_);
v___x_4009_ = v___x_3989_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4007_);
lean_ctor_set(v_reuseFailAlloc_4016_, 1, v___f_3999_);
v___x_4009_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___f_4013_; lean_object* v___x_15460__overap_4014_; lean_object* v___x_4015_; 
v___x_4010_ = l_StateRefT_x27_instMonad___redArg(v___x_4009_);
v___x_4011_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0);
v___x_4012_ = l_instInhabitedOfMonad___redArg(v___x_4010_, v___x_4011_);
v___f_4013_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4013_, 0, v___x_4012_);
v___x_15460__overap_4014_ = lean_panic_fn_borrowed(v___f_4013_, v_msg_3953_);
lean_dec_ref(v___f_4013_);
lean_inc(v___y_3959_);
lean_inc_ref(v___y_3958_);
lean_inc(v___y_3957_);
lean_inc_ref(v___y_3956_);
lean_inc(v___y_3955_);
lean_inc_ref(v___y_3954_);
v___x_4015_ = lean_apply_7(v___x_15460__overap_4014_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, lean_box(0));
return v___x_4015_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2___boxed(lean_object* v_msg_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v_msg_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
return v_res_4036_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2(void){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4039_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_4040_ = lean_unsigned_to_nat(9u);
v___x_4041_ = lean_unsigned_to_nat(625u);
v___x_4042_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__1));
v___x_4043_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__0));
v___x_4044_ = l_mkPanicMessageWithDecl(v___x_4043_, v___x_4042_, v___x_4041_, v___x_4040_, v___x_4039_);
return v___x_4044_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10(void){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4054_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9));
v___x_4055_ = lean_unsigned_to_nat(14u);
v___x_4056_ = lean_unsigned_to_nat(22u);
v___x_4057_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8));
v___x_4058_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7));
v___x_4059_ = l_mkPanicMessageWithDecl(v___x_4058_, v___x_4057_, v___x_4056_, v___x_4055_, v___x_4054_);
return v___x_4059_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12(void){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4061_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_4062_ = lean_unsigned_to_nat(22u);
v___x_4063_ = lean_unsigned_to_nat(575u);
v___x_4064_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11));
v___x_4065_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_4066_ = l_mkPanicMessageWithDecl(v___x_4065_, v___x_4064_, v___x_4063_, v___x_4062_, v___x_4061_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(lean_object* v_code_4067_, lean_object* v_decl_4068_, lean_object* v_k_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_){
_start:
{
lean_object* v_fvarId_4077_; lean_object* v_value_4078_; lean_object* v_k_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v_k_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___x_4153_; 
v_fvarId_4077_ = lean_ctor_get(v_decl_4068_, 0);
lean_inc_n(v_fvarId_4077_, 2);
v_value_4078_ = lean_ctor_get(v_decl_4068_, 3);
lean_inc(v_value_4078_);
v___x_4153_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_4077_, v_k_4069_, v_a_4070_, v_a_4071_);
switch(lean_obj_tag(v_value_4078_))
{
case 4:
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4196_; 
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4156_ = v___x_4153_;
v_isShared_4157_ = v_isSharedCheck_4196_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4153_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4196_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v_fvarId_4158_; lean_object* v_args_4159_; lean_object* v___x_4161_; 
v_fvarId_4158_ = lean_ctor_get(v_value_4078_, 0);
v_args_4159_ = lean_ctor_get(v_value_4078_, 1);
lean_inc(v_fvarId_4158_);
if (v_isShared_4157_ == 0)
{
lean_ctor_set_tag(v___x_4156_, 1);
lean_ctor_set(v___x_4156_, 0, v_fvarId_4158_);
v___x_4161_ = v___x_4156_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_fvarId_4158_);
v___x_4161_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4162_; lean_object* v___y_4164_; 
lean_inc_ref(v_args_4159_);
v___x_4162_ = lean_array_push(v_args_4159_, v___x_4161_);
if (lean_obj_tag(v_code_4067_) == 0)
{
lean_object* v_decl_4167_; lean_object* v_k_4168_; size_t v___x_4169_; size_t v___x_4170_; uint8_t v___x_4171_; 
v_decl_4167_ = lean_ctor_get(v_code_4067_, 0);
v_k_4168_ = lean_ctor_get(v_code_4067_, 1);
v___x_4169_ = lean_ptr_addr(v_k_4168_);
v___x_4170_ = lean_ptr_addr(v_a_4154_);
v___x_4171_ = lean_usize_dec_eq(v___x_4169_, v___x_4170_);
if (v___x_4171_ == 0)
{
lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4178_; 
v_isSharedCheck_4178_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4178_ == 0)
{
lean_object* v_unused_4179_; lean_object* v_unused_4180_; 
v_unused_4179_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4179_);
v_unused_4180_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4180_);
v___x_4173_ = v_code_4067_;
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
else
{
lean_dec(v_code_4067_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4176_; 
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 1, v_a_4154_);
lean_ctor_set(v___x_4173_, 0, v_decl_4068_);
v___x_4176_ = v___x_4173_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4177_, 1, v_a_4154_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
v___y_4164_ = v___x_4176_;
goto v___jp_4163_;
}
}
}
else
{
size_t v___x_4181_; size_t v___x_4182_; uint8_t v___x_4183_; 
v___x_4181_ = lean_ptr_addr(v_decl_4167_);
v___x_4182_ = lean_ptr_addr(v_decl_4068_);
v___x_4183_ = lean_usize_dec_eq(v___x_4181_, v___x_4182_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
v_isSharedCheck_4190_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4190_ == 0)
{
lean_object* v_unused_4191_; lean_object* v_unused_4192_; 
v_unused_4191_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4191_);
v_unused_4192_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4192_);
v___x_4185_ = v_code_4067_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_dec(v_code_4067_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 1, v_a_4154_);
lean_ctor_set(v___x_4185_, 0, v_decl_4068_);
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4189_, 1, v_a_4154_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
v___y_4164_ = v___x_4188_;
goto v___jp_4163_;
}
}
}
else
{
lean_dec(v_a_4154_);
lean_dec_ref(v_decl_4068_);
v___y_4164_ = v_code_4067_;
goto v___jp_4163_;
}
}
}
else
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_dec(v_a_4154_);
lean_dec_ref(v_decl_4068_);
lean_dec_ref(v_code_4067_);
v___x_4193_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4194_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4193_);
v___y_4164_ = v___x_4194_;
goto v___jp_4163_;
}
v___jp_4163_:
{
lean_object* v___x_4165_; 
v___x_4165_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v___x_4162_, v___y_4164_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_);
lean_dec_ref(v___x_4162_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4165_, 1);
v_k_4080_ = v_a_4166_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
else
{
lean_dec_ref_known(v_value_4078_, 2);
lean_dec(v_fvarId_4077_);
return v___x_4165_;
}
}
}
}
}
case 5:
{
lean_object* v_a_4197_; lean_object* v_args_4198_; lean_object* v___y_4200_; 
v_a_4197_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4197_);
lean_dec_ref(v___x_4153_);
v_args_4198_ = lean_ctor_get(v_value_4078_, 1);
if (lean_obj_tag(v_code_4067_) == 0)
{
lean_object* v_decl_4203_; lean_object* v_k_4204_; size_t v___x_4205_; size_t v___x_4206_; uint8_t v___x_4207_; 
v_decl_4203_ = lean_ctor_get(v_code_4067_, 0);
v_k_4204_ = lean_ctor_get(v_code_4067_, 1);
v___x_4205_ = lean_ptr_addr(v_k_4204_);
v___x_4206_ = lean_ptr_addr(v_a_4197_);
v___x_4207_ = lean_usize_dec_eq(v___x_4205_, v___x_4206_);
if (v___x_4207_ == 0)
{
lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
v_isSharedCheck_4214_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4214_ == 0)
{
lean_object* v_unused_4215_; lean_object* v_unused_4216_; 
v_unused_4215_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4215_);
v_unused_4216_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4216_);
v___x_4209_ = v_code_4067_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_dec(v_code_4067_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 1, v_a_4197_);
lean_ctor_set(v___x_4209_, 0, v_decl_4068_);
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4213_, 1, v_a_4197_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
v___y_4200_ = v___x_4212_;
goto v___jp_4199_;
}
}
}
else
{
size_t v___x_4217_; size_t v___x_4218_; uint8_t v___x_4219_; 
v___x_4217_ = lean_ptr_addr(v_decl_4203_);
v___x_4218_ = lean_ptr_addr(v_decl_4068_);
v___x_4219_ = lean_usize_dec_eq(v___x_4217_, v___x_4218_);
if (v___x_4219_ == 0)
{
lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
v_isSharedCheck_4226_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4226_ == 0)
{
lean_object* v_unused_4227_; lean_object* v_unused_4228_; 
v_unused_4227_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4227_);
v_unused_4228_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4228_);
v___x_4221_ = v_code_4067_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_dec(v_code_4067_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 1, v_a_4197_);
lean_ctor_set(v___x_4221_, 0, v_decl_4068_);
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_a_4197_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
v___y_4200_ = v___x_4224_;
goto v___jp_4199_;
}
}
}
else
{
lean_dec(v_a_4197_);
lean_dec_ref(v_decl_4068_);
v___y_4200_ = v_code_4067_;
goto v___jp_4199_;
}
}
}
else
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
lean_dec(v_a_4197_);
lean_dec_ref(v_decl_4068_);
lean_dec_ref(v_code_4067_);
v___x_4229_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4230_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4229_);
v___y_4200_ = v___x_4230_;
goto v___jp_4199_;
}
v___jp_4199_:
{
lean_object* v___x_4201_; 
v___x_4201_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4198_, v___y_4200_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4202_);
lean_dec_ref_known(v___x_4201_, 1);
v_k_4080_ = v_a_4202_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
else
{
lean_dec_ref_known(v_value_4078_, 2);
lean_dec(v_fvarId_4077_);
return v___x_4201_;
}
}
}
case 6:
{
lean_object* v_a_4231_; lean_object* v_var_4232_; lean_object* v___x_4233_; lean_object* v_a_4234_; lean_object* v___x_4235_; lean_object* v_borrows_4236_; uint8_t v___x_4237_; 
v_a_4231_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4231_);
lean_dec_ref(v___x_4153_);
v_var_4232_ = lean_ctor_get(v_value_4078_, 1);
lean_inc(v_var_4232_);
v___x_4233_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4232_, v_a_4231_, v_a_4070_, v_a_4071_);
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref(v___x_4233_);
v___x_4235_ = lean_st_ref_get(v_a_4071_);
v_borrows_4236_ = lean_ctor_get(v___x_4235_, 1);
lean_inc_ref(v_borrows_4236_);
lean_dec(v___x_4235_);
v___x_4237_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4236_, v_fvarId_4077_);
lean_dec_ref(v_borrows_4236_);
if (v___x_4237_ == 0)
{
lean_object* v_varMap_4238_; lean_object* v___x_4239_; uint8_t v_isDefiniteRef_4240_; lean_object* v___x_4241_; uint8_t v___y_4243_; 
v_varMap_4238_ = lean_ctor_get(v_a_4070_, 3);
v___x_4239_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_4238_, v_fvarId_4077_);
v_isDefiniteRef_4240_ = lean_ctor_get_uint8(v___x_4239_, sizeof(void*)*2 + 1);
v___x_4241_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_4240_ == 0)
{
uint8_t v___x_4246_; 
v___x_4246_ = 1;
v___y_4243_ = v___x_4246_;
goto v___jp_4242_;
}
else
{
v___y_4243_ = v___x_4237_;
goto v___jp_4242_;
}
v___jp_4242_:
{
uint8_t v_persistent_4244_; lean_object* v___x_4245_; 
v_persistent_4244_ = lean_ctor_get_uint8(v___x_4239_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_4239_);
lean_inc(v_fvarId_4077_);
v___x_4245_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_4245_, 0, v_fvarId_4077_);
lean_ctor_set(v___x_4245_, 1, v___x_4241_);
lean_ctor_set(v___x_4245_, 2, v_a_4234_);
lean_ctor_set_uint8(v___x_4245_, sizeof(void*)*3, v___y_4243_);
lean_ctor_set_uint8(v___x_4245_, sizeof(void*)*3 + 1, v_persistent_4244_);
v_k_4118_ = v___x_4245_;
v___y_4119_ = v_a_4070_;
v___y_4120_ = v_a_4071_;
v___y_4121_ = v_a_4072_;
v___y_4122_ = v_a_4073_;
v___y_4123_ = v_a_4074_;
v___y_4124_ = v_a_4075_;
goto v___jp_4117_;
}
}
else
{
v_k_4118_ = v_a_4234_;
v___y_4119_ = v_a_4070_;
v___y_4120_ = v_a_4071_;
v___y_4121_ = v_a_4072_;
v___y_4122_ = v_a_4073_;
v___y_4123_ = v_a_4074_;
v___y_4124_ = v_a_4075_;
goto v___jp_4117_;
}
}
case 7:
{
lean_object* v_a_4247_; lean_object* v_var_4248_; lean_object* v___x_4249_; 
v_a_4247_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4247_);
lean_dec_ref(v___x_4153_);
v_var_4248_ = lean_ctor_get(v_value_4078_, 1);
lean_inc(v_var_4248_);
v___x_4249_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4248_, v_a_4247_, v_a_4070_, v_a_4071_);
if (lean_obj_tag(v_code_4067_) == 0)
{
lean_object* v_a_4250_; lean_object* v_decl_4251_; lean_object* v_k_4252_; size_t v___x_4253_; size_t v___x_4254_; uint8_t v___x_4255_; 
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
lean_inc(v_a_4250_);
lean_dec_ref(v___x_4249_);
v_decl_4251_ = lean_ctor_get(v_code_4067_, 0);
v_k_4252_ = lean_ctor_get(v_code_4067_, 1);
v___x_4253_ = lean_ptr_addr(v_k_4252_);
v___x_4254_ = lean_ptr_addr(v_a_4250_);
v___x_4255_ = lean_usize_dec_eq(v___x_4253_, v___x_4254_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4262_; 
v_isSharedCheck_4262_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4262_ == 0)
{
lean_object* v_unused_4263_; lean_object* v_unused_4264_; 
v_unused_4263_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4263_);
v_unused_4264_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4264_);
v___x_4257_ = v_code_4067_;
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
else
{
lean_dec(v_code_4067_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4260_; 
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 1, v_a_4250_);
lean_ctor_set(v___x_4257_, 0, v_decl_4068_);
v___x_4260_ = v___x_4257_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4261_, 1, v_a_4250_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
v_k_4080_ = v___x_4260_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
else
{
size_t v___x_4265_; size_t v___x_4266_; uint8_t v___x_4267_; 
v___x_4265_ = lean_ptr_addr(v_decl_4251_);
v___x_4266_ = lean_ptr_addr(v_decl_4068_);
v___x_4267_ = lean_usize_dec_eq(v___x_4265_, v___x_4266_);
if (v___x_4267_ == 0)
{
lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
v_isSharedCheck_4274_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4274_ == 0)
{
lean_object* v_unused_4275_; lean_object* v_unused_4276_; 
v_unused_4275_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4275_);
v_unused_4276_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4276_);
v___x_4269_ = v_code_4067_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_dec(v_code_4067_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 1, v_a_4250_);
lean_ctor_set(v___x_4269_, 0, v_decl_4068_);
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v_a_4250_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
v_k_4080_ = v___x_4272_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
else
{
lean_dec(v_a_4250_);
lean_dec_ref(v_decl_4068_);
v_k_4080_ = v_code_4067_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
else
{
lean_object* v___x_4277_; lean_object* v___x_4278_; 
lean_dec_ref(v___x_4249_);
lean_dec_ref(v_decl_4068_);
lean_dec_ref(v_code_4067_);
v___x_4277_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4278_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4277_);
v_k_4080_ = v___x_4278_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
case 8:
{
lean_object* v_a_4279_; lean_object* v_var_4280_; lean_object* v___x_4281_; 
v_a_4279_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4279_);
lean_dec_ref(v___x_4153_);
v_var_4280_ = lean_ctor_get(v_value_4078_, 2);
lean_inc(v_var_4280_);
v___x_4281_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4280_, v_a_4279_, v_a_4070_, v_a_4071_);
if (lean_obj_tag(v_code_4067_) == 0)
{
lean_object* v_a_4282_; lean_object* v_decl_4283_; lean_object* v_k_4284_; size_t v___x_4285_; size_t v___x_4286_; uint8_t v___x_4287_; 
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_a_4282_);
lean_dec_ref(v___x_4281_);
v_decl_4283_ = lean_ctor_get(v_code_4067_, 0);
v_k_4284_ = lean_ctor_get(v_code_4067_, 1);
v___x_4285_ = lean_ptr_addr(v_k_4284_);
v___x_4286_ = lean_ptr_addr(v_a_4282_);
v___x_4287_ = lean_usize_dec_eq(v___x_4285_, v___x_4286_);
if (v___x_4287_ == 0)
{
lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
v_isSharedCheck_4294_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4294_ == 0)
{
lean_object* v_unused_4295_; lean_object* v_unused_4296_; 
v_unused_4295_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4295_);
v_unused_4296_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4296_);
v___x_4289_ = v_code_4067_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_dec(v_code_4067_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
lean_ctor_set(v___x_4289_, 1, v_a_4282_);
lean_ctor_set(v___x_4289_, 0, v_decl_4068_);
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4293_, 1, v_a_4282_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
v_k_4080_ = v___x_4292_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
else
{
size_t v___x_4297_; size_t v___x_4298_; uint8_t v___x_4299_; 
v___x_4297_ = lean_ptr_addr(v_decl_4283_);
v___x_4298_ = lean_ptr_addr(v_decl_4068_);
v___x_4299_ = lean_usize_dec_eq(v___x_4297_, v___x_4298_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
v_isSharedCheck_4306_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4306_ == 0)
{
lean_object* v_unused_4307_; lean_object* v_unused_4308_; 
v_unused_4307_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4307_);
v_unused_4308_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4308_);
v___x_4301_ = v_code_4067_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_dec(v_code_4067_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 1, v_a_4282_);
lean_ctor_set(v___x_4301_, 0, v_decl_4068_);
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4305_, 1, v_a_4282_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
v_k_4080_ = v___x_4304_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
else
{
lean_dec(v_a_4282_);
lean_dec_ref(v_decl_4068_);
v_k_4080_ = v_code_4067_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
else
{
lean_object* v___x_4309_; lean_object* v___x_4310_; 
lean_dec_ref(v___x_4281_);
lean_dec_ref(v_decl_4068_);
lean_dec_ref(v_code_4067_);
v___x_4309_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4310_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4309_);
v_k_4080_ = v___x_4310_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
case 9:
{
lean_object* v_a_4311_; lean_object* v_fn_4312_; lean_object* v_args_4313_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___x_4325_; 
v_a_4311_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4311_);
lean_dec_ref(v___x_4153_);
v_fn_4312_ = lean_ctor_get(v_value_4078_, 0);
v_args_4313_ = lean_ctor_get(v_value_4078_, 1);
lean_inc(v_fn_4312_);
v___x_4325_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_4312_, v_a_4075_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v_a_4326_; uint8_t v___x_4327_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v_value_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; uint8_t v___y_4380_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; uint8_t v___y_4388_; uint8_t v___y_4389_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; uint8_t v___y_4400_; uint8_t v___y_4401_; uint8_t v___y_4402_; lean_object* v___y_4410_; 
v_a_4326_ = lean_ctor_get(v___x_4325_, 0);
lean_inc(v_a_4326_);
lean_dec_ref_known(v___x_4325_, 1);
v___x_4327_ = 1;
if (lean_obj_tag(v_a_4326_) == 0)
{
lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4426_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10);
v___x_4427_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1(v___x_4426_);
v___y_4410_ = v___x_4427_;
goto v___jp_4409_;
}
else
{
lean_object* v_val_4428_; 
v_val_4428_ = lean_ctor_get(v_a_4326_, 0);
lean_inc(v_val_4428_);
lean_dec_ref_known(v_a_4326_, 1);
v___y_4410_ = v_val_4428_;
goto v___jp_4409_;
}
v___jp_4328_:
{
lean_object* v___x_4338_; 
v___x_4338_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_4327_, v_decl_4068_, v_value_4331_, v___y_4335_);
if (lean_obj_tag(v___x_4338_) == 0)
{
if (lean_obj_tag(v_code_4067_) == 0)
{
lean_object* v_a_4339_; lean_object* v_decl_4340_; lean_object* v_k_4341_; size_t v___x_4342_; size_t v___x_4343_; uint8_t v___x_4344_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_a_4339_);
lean_dec_ref_known(v___x_4338_, 1);
v_decl_4340_ = lean_ctor_get(v_code_4067_, 0);
v_k_4341_ = lean_ctor_get(v_code_4067_, 1);
v___x_4342_ = lean_ptr_addr(v_k_4341_);
v___x_4343_ = lean_ptr_addr(v___y_4329_);
v___x_4344_ = lean_usize_dec_eq(v___x_4342_, v___x_4343_);
if (v___x_4344_ == 0)
{
lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
v_isSharedCheck_4351_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4351_ == 0)
{
lean_object* v_unused_4352_; lean_object* v_unused_4353_; 
v_unused_4352_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4352_);
v_unused_4353_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4353_);
v___x_4346_ = v_code_4067_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_dec(v_code_4067_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 1, v___y_4329_);
lean_ctor_set(v___x_4346_, 0, v_a_4339_);
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4339_);
lean_ctor_set(v_reuseFailAlloc_4350_, 1, v___y_4329_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
v___y_4315_ = v___y_4335_;
v___y_4316_ = v___y_4336_;
v___y_4317_ = v___y_4332_;
v___y_4318_ = v___y_4330_;
v___y_4319_ = v___y_4333_;
v___y_4320_ = v___y_4337_;
v___y_4321_ = v___y_4334_;
v___y_4322_ = v___x_4349_;
goto v___jp_4314_;
}
}
}
else
{
size_t v___x_4354_; size_t v___x_4355_; uint8_t v___x_4356_; 
v___x_4354_ = lean_ptr_addr(v_decl_4340_);
v___x_4355_ = lean_ptr_addr(v_a_4339_);
v___x_4356_ = lean_usize_dec_eq(v___x_4354_, v___x_4355_);
if (v___x_4356_ == 0)
{
lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
v_isSharedCheck_4363_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4363_ == 0)
{
lean_object* v_unused_4364_; lean_object* v_unused_4365_; 
v_unused_4364_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4364_);
v_unused_4365_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4365_);
v___x_4358_ = v_code_4067_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_dec(v_code_4067_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 1, v___y_4329_);
lean_ctor_set(v___x_4358_, 0, v_a_4339_);
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4339_);
lean_ctor_set(v_reuseFailAlloc_4362_, 1, v___y_4329_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
v___y_4315_ = v___y_4335_;
v___y_4316_ = v___y_4336_;
v___y_4317_ = v___y_4332_;
v___y_4318_ = v___y_4330_;
v___y_4319_ = v___y_4333_;
v___y_4320_ = v___y_4337_;
v___y_4321_ = v___y_4334_;
v___y_4322_ = v___x_4361_;
goto v___jp_4314_;
}
}
}
else
{
lean_dec(v_a_4339_);
lean_dec_ref(v___y_4329_);
v___y_4315_ = v___y_4335_;
v___y_4316_ = v___y_4336_;
v___y_4317_ = v___y_4332_;
v___y_4318_ = v___y_4330_;
v___y_4319_ = v___y_4333_;
v___y_4320_ = v___y_4337_;
v___y_4321_ = v___y_4334_;
v___y_4322_ = v_code_4067_;
goto v___jp_4314_;
}
}
}
else
{
lean_object* v___x_4366_; lean_object* v___x_4367_; 
lean_dec_ref_known(v___x_4338_, 1);
lean_dec_ref(v___y_4329_);
lean_dec_ref(v_code_4067_);
v___x_4366_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4367_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4366_);
v___y_4315_ = v___y_4335_;
v___y_4316_ = v___y_4336_;
v___y_4317_ = v___y_4332_;
v___y_4318_ = v___y_4330_;
v___y_4319_ = v___y_4333_;
v___y_4320_ = v___y_4337_;
v___y_4321_ = v___y_4334_;
v___y_4322_ = v___x_4367_;
goto v___jp_4314_;
}
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
lean_dec_ref(v___y_4330_);
lean_dec_ref(v___y_4329_);
lean_dec_ref_known(v_value_4078_, 2);
lean_dec(v_fvarId_4077_);
lean_dec_ref(v_code_4067_);
v_a_4368_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4338_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4338_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
}
v___jp_4376_:
{
if (v___y_4380_ == 0)
{
lean_inc_ref(v_value_4078_);
v___y_4329_ = v___y_4377_;
v___y_4330_ = v___y_4378_;
v_value_4331_ = v_value_4078_;
v___y_4332_ = v_a_4070_;
v___y_4333_ = v_a_4071_;
v___y_4334_ = v_a_4072_;
v___y_4335_ = v_a_4073_;
v___y_4336_ = v_a_4074_;
v___y_4337_ = v_a_4075_;
goto v___jp_4328_;
}
else
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4381_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__3));
lean_inc_ref(v___y_4379_);
v___x_4382_ = l_Lean_Name_mkStr2(v___y_4379_, v___x_4381_);
lean_inc_ref(v_args_4313_);
v___x_4383_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4382_);
lean_ctor_set(v___x_4383_, 1, v_args_4313_);
v___y_4329_ = v___y_4377_;
v___y_4330_ = v___y_4378_;
v_value_4331_ = v___x_4383_;
v___y_4332_ = v_a_4070_;
v___y_4333_ = v_a_4071_;
v___y_4334_ = v_a_4072_;
v___y_4335_ = v_a_4073_;
v___y_4336_ = v_a_4074_;
v___y_4337_ = v_a_4075_;
goto v___jp_4328_;
}
}
v___jp_4384_:
{
if (v___y_4389_ == 0)
{
lean_object* v___x_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; 
v___x_4390_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__3));
lean_inc_ref(v___y_4387_);
v___x_4391_ = l_Lean_Name_mkStr2(v___y_4387_, v___x_4390_);
v___x_4392_ = lean_name_eq(v_fn_4312_, v___x_4391_);
lean_dec(v___x_4391_);
if (v___x_4392_ == 0)
{
v___y_4377_ = v___y_4385_;
v___y_4378_ = v___y_4386_;
v___y_4379_ = v___y_4387_;
v___y_4380_ = v___x_4392_;
goto v___jp_4376_;
}
else
{
v___y_4377_ = v___y_4385_;
v___y_4378_ = v___y_4386_;
v___y_4379_ = v___y_4387_;
v___y_4380_ = v___y_4388_;
goto v___jp_4376_;
}
}
else
{
lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4393_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__4));
lean_inc_ref(v___y_4387_);
v___x_4394_ = l_Lean_Name_mkStr2(v___y_4387_, v___x_4393_);
lean_inc_ref(v_args_4313_);
v___x_4395_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4394_);
lean_ctor_set(v___x_4395_, 1, v_args_4313_);
v___y_4329_ = v___y_4385_;
v___y_4330_ = v___y_4386_;
v_value_4331_ = v___x_4395_;
v___y_4332_ = v_a_4070_;
v___y_4333_ = v_a_4071_;
v___y_4334_ = v_a_4072_;
v___y_4335_ = v_a_4073_;
v___y_4336_ = v_a_4074_;
v___y_4337_ = v_a_4075_;
goto v___jp_4328_;
}
}
v___jp_4396_:
{
if (v___y_4402_ == 0)
{
lean_object* v___x_4403_; lean_object* v___x_4404_; uint8_t v___x_4405_; 
v___x_4403_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__2));
lean_inc_ref(v___y_4399_);
v___x_4404_ = l_Lean_Name_mkStr2(v___y_4399_, v___x_4403_);
v___x_4405_ = lean_name_eq(v_fn_4312_, v___x_4404_);
lean_dec(v___x_4404_);
if (v___x_4405_ == 0)
{
v___y_4385_ = v___y_4397_;
v___y_4386_ = v___y_4398_;
v___y_4387_ = v___y_4399_;
v___y_4388_ = v___y_4401_;
v___y_4389_ = v___x_4405_;
goto v___jp_4384_;
}
else
{
v___y_4385_ = v___y_4397_;
v___y_4386_ = v___y_4398_;
v___y_4387_ = v___y_4399_;
v___y_4388_ = v___y_4401_;
v___y_4389_ = v___y_4400_;
goto v___jp_4384_;
}
}
else
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4406_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5));
lean_inc_ref(v___y_4399_);
v___x_4407_ = l_Lean_Name_mkStr2(v___y_4399_, v___x_4406_);
lean_inc_ref(v_args_4313_);
v___x_4408_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4407_);
lean_ctor_set(v___x_4408_, 1, v_args_4313_);
v___y_4329_ = v___y_4397_;
v___y_4330_ = v___y_4398_;
v_value_4331_ = v___x_4408_;
v___y_4332_ = v_a_4070_;
v___y_4333_ = v_a_4071_;
v___y_4334_ = v_a_4072_;
v___y_4335_ = v_a_4073_;
v___y_4336_ = v_a_4074_;
v___y_4337_ = v_a_4075_;
goto v___jp_4328_;
}
}
v___jp_4409_:
{
lean_object* v_params_4411_; lean_object* v___x_4412_; 
v_params_4411_ = lean_ctor_get(v___y_4410_, 3);
lean_inc_ref_n(v_params_4411_, 2);
lean_dec_ref(v___y_4410_);
v___x_4412_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(v_args_4313_, v_params_4411_, v_a_4311_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4414_; lean_object* v_borrows_4415_; uint8_t v___x_4416_; lean_object* v___x_4417_; lean_object* v_borrows_4418_; uint8_t v___x_4419_; lean_object* v___x_4420_; lean_object* v_borrows_4421_; uint8_t v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v___x_4414_ = lean_st_ref_get(v_a_4071_);
v_borrows_4415_ = lean_ctor_get(v___x_4414_, 1);
lean_inc_ref(v_borrows_4415_);
lean_dec(v___x_4414_);
v___x_4416_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4415_, v_fvarId_4077_);
lean_dec_ref(v_borrows_4415_);
v___x_4417_ = lean_st_ref_get(v_a_4071_);
v_borrows_4418_ = lean_ctor_get(v___x_4417_, 1);
lean_inc_ref(v_borrows_4418_);
lean_dec(v___x_4417_);
v___x_4419_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4418_, v_fvarId_4077_);
lean_dec_ref(v_borrows_4418_);
v___x_4420_ = lean_st_ref_get(v_a_4071_);
v_borrows_4421_ = lean_ctor_get(v___x_4420_, 1);
lean_inc_ref(v_borrows_4421_);
lean_dec(v___x_4420_);
v___x_4422_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4421_, v_fvarId_4077_);
lean_dec_ref(v_borrows_4421_);
v___x_4423_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0));
v___x_4424_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6));
v___x_4425_ = lean_name_eq(v_fn_4312_, v___x_4424_);
if (v___x_4425_ == 0)
{
v___y_4397_ = v_a_4413_;
v___y_4398_ = v_params_4411_;
v___y_4399_ = v___x_4423_;
v___y_4400_ = v___x_4419_;
v___y_4401_ = v___x_4422_;
v___y_4402_ = v___x_4425_;
goto v___jp_4396_;
}
else
{
v___y_4397_ = v_a_4413_;
v___y_4398_ = v_params_4411_;
v___y_4399_ = v___x_4423_;
v___y_4400_ = v___x_4419_;
v___y_4401_ = v___x_4422_;
v___y_4402_ = v___x_4416_;
goto v___jp_4396_;
}
}
else
{
lean_dec_ref(v_params_4411_);
lean_dec_ref_known(v_value_4078_, 2);
lean_dec(v_fvarId_4077_);
lean_dec_ref(v_decl_4068_);
lean_dec_ref(v_code_4067_);
return v___x_4412_;
}
}
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec(v_a_4311_);
lean_dec_ref_known(v_value_4078_, 2);
lean_dec(v_fvarId_4077_);
lean_dec_ref(v_decl_4068_);
lean_dec_ref(v_code_4067_);
v_a_4429_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4325_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4325_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
v___jp_4314_:
{
lean_object* v___x_4323_; 
v___x_4323_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_4313_, v___y_4318_, v___y_4322_, v___y_4317_, v___y_4319_, v___y_4321_, v___y_4315_, v___y_4316_, v___y_4320_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4323_, 1);
v_k_4080_ = v_a_4324_;
v___y_4081_ = v___y_4317_;
v___y_4082_ = v___y_4319_;
v___y_4083_ = v___y_4321_;
v___y_4084_ = v___y_4315_;
v___y_4085_ = v___y_4316_;
v___y_4086_ = v___y_4320_;
goto v___jp_4079_;
}
else
{
lean_dec_ref_known(v_value_4078_, 2);
lean_dec(v_fvarId_4077_);
return v___x_4323_;
}
}
}
case 10:
{
lean_object* v_a_4437_; lean_object* v_args_4438_; lean_object* v___y_4440_; 
v_a_4437_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4437_);
lean_dec_ref(v___x_4153_);
v_args_4438_ = lean_ctor_get(v_value_4078_, 1);
if (lean_obj_tag(v_code_4067_) == 0)
{
lean_object* v_decl_4443_; lean_object* v_k_4444_; size_t v___x_4445_; size_t v___x_4446_; uint8_t v___x_4447_; 
v_decl_4443_ = lean_ctor_get(v_code_4067_, 0);
v_k_4444_ = lean_ctor_get(v_code_4067_, 1);
v___x_4445_ = lean_ptr_addr(v_k_4444_);
v___x_4446_ = lean_ptr_addr(v_a_4437_);
v___x_4447_ = lean_usize_dec_eq(v___x_4445_, v___x_4446_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
v_isSharedCheck_4454_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4454_ == 0)
{
lean_object* v_unused_4455_; lean_object* v_unused_4456_; 
v_unused_4455_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4455_);
v_unused_4456_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4456_);
v___x_4449_ = v_code_4067_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_dec(v_code_4067_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 1, v_a_4437_);
lean_ctor_set(v___x_4449_, 0, v_decl_4068_);
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4453_, 1, v_a_4437_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
v___y_4440_ = v___x_4452_;
goto v___jp_4439_;
}
}
}
else
{
size_t v___x_4457_; size_t v___x_4458_; uint8_t v___x_4459_; 
v___x_4457_ = lean_ptr_addr(v_decl_4443_);
v___x_4458_ = lean_ptr_addr(v_decl_4068_);
v___x_4459_ = lean_usize_dec_eq(v___x_4457_, v___x_4458_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
v_isSharedCheck_4466_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4466_ == 0)
{
lean_object* v_unused_4467_; lean_object* v_unused_4468_; 
v_unused_4467_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4467_);
v_unused_4468_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4468_);
v___x_4461_ = v_code_4067_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_dec(v_code_4067_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 1, v_a_4437_);
lean_ctor_set(v___x_4461_, 0, v_decl_4068_);
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4465_, 1, v_a_4437_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
v___y_4440_ = v___x_4464_;
goto v___jp_4439_;
}
}
}
else
{
lean_dec(v_a_4437_);
lean_dec_ref(v_decl_4068_);
v___y_4440_ = v_code_4067_;
goto v___jp_4439_;
}
}
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
lean_dec(v_a_4437_);
lean_dec_ref(v_decl_4068_);
lean_dec_ref(v_code_4067_);
v___x_4469_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4470_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4469_);
v___y_4440_ = v___x_4470_;
goto v___jp_4439_;
}
v___jp_4439_:
{
lean_object* v___x_4441_; 
v___x_4441_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4438_, v___y_4440_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_);
if (lean_obj_tag(v___x_4441_) == 0)
{
lean_object* v_a_4442_; 
v_a_4442_ = lean_ctor_get(v___x_4441_, 0);
lean_inc(v_a_4442_);
lean_dec_ref_known(v___x_4441_, 1);
v_k_4080_ = v_a_4442_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
else
{
lean_dec_ref_known(v_value_4078_, 2);
lean_dec(v_fvarId_4077_);
return v___x_4441_;
}
}
}
case 12:
{
lean_object* v_a_4471_; lean_object* v_args_4472_; lean_object* v___y_4474_; 
v_a_4471_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4471_);
lean_dec_ref(v___x_4153_);
v_args_4472_ = lean_ctor_get(v_value_4078_, 2);
if (lean_obj_tag(v_code_4067_) == 0)
{
lean_object* v_decl_4477_; lean_object* v_k_4478_; size_t v___x_4479_; size_t v___x_4480_; uint8_t v___x_4481_; 
v_decl_4477_ = lean_ctor_get(v_code_4067_, 0);
v_k_4478_ = lean_ctor_get(v_code_4067_, 1);
v___x_4479_ = lean_ptr_addr(v_k_4478_);
v___x_4480_ = lean_ptr_addr(v_a_4471_);
v___x_4481_ = lean_usize_dec_eq(v___x_4479_, v___x_4480_);
if (v___x_4481_ == 0)
{
lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
v_isSharedCheck_4488_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4488_ == 0)
{
lean_object* v_unused_4489_; lean_object* v_unused_4490_; 
v_unused_4489_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4489_);
v_unused_4490_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4490_);
v___x_4483_ = v_code_4067_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_dec(v_code_4067_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 1, v_a_4471_);
lean_ctor_set(v___x_4483_, 0, v_decl_4068_);
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v_a_4471_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
v___y_4474_ = v___x_4486_;
goto v___jp_4473_;
}
}
}
else
{
size_t v___x_4491_; size_t v___x_4492_; uint8_t v___x_4493_; 
v___x_4491_ = lean_ptr_addr(v_decl_4477_);
v___x_4492_ = lean_ptr_addr(v_decl_4068_);
v___x_4493_ = lean_usize_dec_eq(v___x_4491_, v___x_4492_);
if (v___x_4493_ == 0)
{
lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
v_isSharedCheck_4500_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4500_ == 0)
{
lean_object* v_unused_4501_; lean_object* v_unused_4502_; 
v_unused_4501_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4501_);
v_unused_4502_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4502_);
v___x_4495_ = v_code_4067_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_dec(v_code_4067_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 1, v_a_4471_);
lean_ctor_set(v___x_4495_, 0, v_decl_4068_);
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v_a_4471_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
v___y_4474_ = v___x_4498_;
goto v___jp_4473_;
}
}
}
else
{
lean_dec(v_a_4471_);
lean_dec_ref(v_decl_4068_);
v___y_4474_ = v_code_4067_;
goto v___jp_4473_;
}
}
}
else
{
lean_object* v___x_4503_; lean_object* v___x_4504_; 
lean_dec(v_a_4471_);
lean_dec_ref(v_decl_4068_);
lean_dec_ref(v_code_4067_);
v___x_4503_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4504_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4503_);
v___y_4474_ = v___x_4504_;
goto v___jp_4473_;
}
v___jp_4473_:
{
lean_object* v___x_4475_; 
v___x_4475_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4472_, v___y_4474_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_);
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_object* v_a_4476_; 
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
lean_inc(v_a_4476_);
lean_dec_ref_known(v___x_4475_, 1);
v_k_4080_ = v_a_4476_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
else
{
lean_dec_ref_known(v_value_4078_, 3);
lean_dec(v_fvarId_4077_);
return v___x_4475_;
}
}
}
case 14:
{
lean_object* v_a_4505_; lean_object* v_fvarId_4506_; lean_object* v___x_4507_; 
v_a_4505_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4505_);
lean_dec_ref(v___x_4153_);
v_fvarId_4506_ = lean_ctor_get(v_value_4078_, 0);
lean_inc(v_fvarId_4506_);
v___x_4507_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_4506_, v_a_4505_, v_a_4070_, v_a_4071_);
if (lean_obj_tag(v_code_4067_) == 0)
{
lean_object* v_a_4508_; lean_object* v_decl_4509_; lean_object* v_k_4510_; size_t v___x_4511_; size_t v___x_4512_; uint8_t v___x_4513_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4508_);
lean_dec_ref(v___x_4507_);
v_decl_4509_ = lean_ctor_get(v_code_4067_, 0);
v_k_4510_ = lean_ctor_get(v_code_4067_, 1);
v___x_4511_ = lean_ptr_addr(v_k_4510_);
v___x_4512_ = lean_ptr_addr(v_a_4508_);
v___x_4513_ = lean_usize_dec_eq(v___x_4511_, v___x_4512_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
v_isSharedCheck_4520_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4520_ == 0)
{
lean_object* v_unused_4521_; lean_object* v_unused_4522_; 
v_unused_4521_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4521_);
v_unused_4522_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4522_);
v___x_4515_ = v_code_4067_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_dec(v_code_4067_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 1, v_a_4508_);
lean_ctor_set(v___x_4515_, 0, v_decl_4068_);
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4519_, 1, v_a_4508_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
v_k_4080_ = v___x_4518_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
else
{
size_t v___x_4523_; size_t v___x_4524_; uint8_t v___x_4525_; 
v___x_4523_ = lean_ptr_addr(v_decl_4509_);
v___x_4524_ = lean_ptr_addr(v_decl_4068_);
v___x_4525_ = lean_usize_dec_eq(v___x_4523_, v___x_4524_);
if (v___x_4525_ == 0)
{
lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4532_; 
v_isSharedCheck_4532_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4532_ == 0)
{
lean_object* v_unused_4533_; lean_object* v_unused_4534_; 
v_unused_4533_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4533_);
v_unused_4534_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4534_);
v___x_4527_ = v_code_4067_;
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
else
{
lean_dec(v_code_4067_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4530_; 
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 1, v_a_4508_);
lean_ctor_set(v___x_4527_, 0, v_decl_4068_);
v___x_4530_ = v___x_4527_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4531_, 1, v_a_4508_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
v_k_4080_ = v___x_4530_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
else
{
lean_dec(v_a_4508_);
lean_dec_ref(v_decl_4068_);
v_k_4080_ = v_code_4067_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
else
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
lean_dec_ref(v___x_4507_);
lean_dec_ref(v_decl_4068_);
lean_dec_ref(v_code_4067_);
v___x_4535_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4536_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4535_);
v_k_4080_ = v___x_4536_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
case 15:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
lean_dec_ref(v___x_4153_);
lean_dec_ref(v_decl_4068_);
lean_dec_ref(v_code_4067_);
v___x_4537_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12);
v___x_4538_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v___x_4537_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v_a_4539_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref_known(v___x_4538_, 1);
v_k_4080_ = v_a_4539_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
else
{
lean_dec_ref_known(v_value_4078_, 1);
lean_dec(v_fvarId_4077_);
return v___x_4538_;
}
}
default: 
{
if (lean_obj_tag(v_code_4067_) == 0)
{
lean_object* v_a_4540_; lean_object* v_decl_4541_; lean_object* v_k_4542_; size_t v___x_4543_; size_t v___x_4544_; uint8_t v___x_4545_; 
v_a_4540_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4540_);
lean_dec_ref(v___x_4153_);
v_decl_4541_ = lean_ctor_get(v_code_4067_, 0);
v_k_4542_ = lean_ctor_get(v_code_4067_, 1);
v___x_4543_ = lean_ptr_addr(v_k_4542_);
v___x_4544_ = lean_ptr_addr(v_a_4540_);
v___x_4545_ = lean_usize_dec_eq(v___x_4543_, v___x_4544_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
v_isSharedCheck_4552_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4552_ == 0)
{
lean_object* v_unused_4553_; lean_object* v_unused_4554_; 
v_unused_4553_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4553_);
v_unused_4554_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4554_);
v___x_4547_ = v_code_4067_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_dec(v_code_4067_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 1, v_a_4540_);
lean_ctor_set(v___x_4547_, 0, v_decl_4068_);
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4551_, 1, v_a_4540_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
v_k_4080_ = v___x_4550_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
else
{
size_t v___x_4555_; size_t v___x_4556_; uint8_t v___x_4557_; 
v___x_4555_ = lean_ptr_addr(v_decl_4541_);
v___x_4556_ = lean_ptr_addr(v_decl_4068_);
v___x_4557_ = lean_usize_dec_eq(v___x_4555_, v___x_4556_);
if (v___x_4557_ == 0)
{
lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
v_isSharedCheck_4564_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4564_ == 0)
{
lean_object* v_unused_4565_; lean_object* v_unused_4566_; 
v_unused_4565_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4565_);
v_unused_4566_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4566_);
v___x_4559_ = v_code_4067_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_dec(v_code_4067_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 1, v_a_4540_);
lean_ctor_set(v___x_4559_, 0, v_decl_4068_);
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4563_, 1, v_a_4540_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
v_k_4080_ = v___x_4562_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
else
{
lean_dec(v_a_4540_);
lean_dec_ref(v_decl_4068_);
v_k_4080_ = v_code_4067_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
else
{
lean_object* v___x_4567_; lean_object* v___x_4568_; 
lean_dec_ref(v___x_4153_);
lean_dec_ref(v_decl_4068_);
lean_dec_ref(v_code_4067_);
v___x_4567_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4568_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4567_);
v_k_4080_ = v___x_4568_;
v___y_4081_ = v_a_4070_;
v___y_4082_ = v_a_4071_;
v___y_4083_ = v_a_4072_;
v___y_4084_ = v_a_4073_;
v___y_4085_ = v_a_4074_;
v___y_4086_ = v_a_4075_;
goto v___jp_4079_;
}
}
}
v___jp_4079_:
{
lean_object* v___x_4087_; 
v___x_4087_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(v_value_4078_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4107_; 
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4107_ == 0)
{
lean_object* v_unused_4108_; 
v_unused_4108_ = lean_ctor_get(v___x_4087_, 0);
lean_dec(v_unused_4108_);
v___x_4089_ = v___x_4087_;
v_isShared_4090_ = v_isSharedCheck_4107_;
goto v_resetjp_4088_;
}
else
{
lean_dec(v___x_4087_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4107_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4091_; lean_object* v_vars_4092_; lean_object* v_borrows_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4106_; 
v___x_4091_ = lean_st_ref_take(v___y_4082_);
v_vars_4092_ = lean_ctor_get(v___x_4091_, 0);
v_borrows_4093_ = lean_ctor_get(v___x_4091_, 1);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4095_ = v___x_4091_;
v_isShared_4096_ = v_isSharedCheck_4106_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_borrows_4093_);
lean_inc(v_vars_4092_);
lean_dec(v___x_4091_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4106_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v_vars_4097_; lean_object* v_borrows_4098_; lean_object* v___x_4100_; 
v_vars_4097_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_vars_4092_, v_fvarId_4077_);
v_borrows_4098_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_borrows_4093_, v_fvarId_4077_);
lean_dec(v_fvarId_4077_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 1, v_borrows_4098_);
lean_ctor_set(v___x_4095_, 0, v_vars_4097_);
v___x_4100_ = v___x_4095_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_vars_4097_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v_borrows_4098_);
v___x_4100_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
lean_object* v___x_4101_; lean_object* v___x_4103_; 
v___x_4101_ = lean_st_ref_put(v___y_4082_, v___x_4100_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v_k_4080_);
v___x_4103_ = v___x_4089_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_k_4080_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
lean_dec_ref(v_k_4080_);
lean_dec(v_fvarId_4077_);
v_a_4109_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4087_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4087_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
v___jp_4117_:
{
if (lean_obj_tag(v_code_4067_) == 0)
{
lean_object* v_decl_4125_; lean_object* v_k_4126_; size_t v___x_4127_; size_t v___x_4128_; uint8_t v___x_4129_; 
v_decl_4125_ = lean_ctor_get(v_code_4067_, 0);
v_k_4126_ = lean_ctor_get(v_code_4067_, 1);
v___x_4127_ = lean_ptr_addr(v_k_4126_);
v___x_4128_ = lean_ptr_addr(v_k_4118_);
v___x_4129_ = lean_usize_dec_eq(v___x_4127_, v___x_4128_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
v_isSharedCheck_4136_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4136_ == 0)
{
lean_object* v_unused_4137_; lean_object* v_unused_4138_; 
v_unused_4137_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4137_);
v_unused_4138_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4138_);
v___x_4131_ = v_code_4067_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_dec(v_code_4067_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
lean_ctor_set(v___x_4131_, 1, v_k_4118_);
lean_ctor_set(v___x_4131_, 0, v_decl_4068_);
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4135_, 1, v_k_4118_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
v_k_4080_ = v___x_4134_;
v___y_4081_ = v___y_4119_;
v___y_4082_ = v___y_4120_;
v___y_4083_ = v___y_4121_;
v___y_4084_ = v___y_4122_;
v___y_4085_ = v___y_4123_;
v___y_4086_ = v___y_4124_;
goto v___jp_4079_;
}
}
}
else
{
size_t v___x_4139_; size_t v___x_4140_; uint8_t v___x_4141_; 
v___x_4139_ = lean_ptr_addr(v_decl_4125_);
v___x_4140_ = lean_ptr_addr(v_decl_4068_);
v___x_4141_ = lean_usize_dec_eq(v___x_4139_, v___x_4140_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
v_isSharedCheck_4148_ = !lean_is_exclusive(v_code_4067_);
if (v_isSharedCheck_4148_ == 0)
{
lean_object* v_unused_4149_; lean_object* v_unused_4150_; 
v_unused_4149_ = lean_ctor_get(v_code_4067_, 1);
lean_dec(v_unused_4149_);
v_unused_4150_ = lean_ctor_get(v_code_4067_, 0);
lean_dec(v_unused_4150_);
v___x_4143_ = v_code_4067_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_dec(v_code_4067_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 1, v_k_4118_);
lean_ctor_set(v___x_4143_, 0, v_decl_4068_);
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_decl_4068_);
lean_ctor_set(v_reuseFailAlloc_4147_, 1, v_k_4118_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
v_k_4080_ = v___x_4146_;
v___y_4081_ = v___y_4119_;
v___y_4082_ = v___y_4120_;
v___y_4083_ = v___y_4121_;
v___y_4084_ = v___y_4122_;
v___y_4085_ = v___y_4123_;
v___y_4086_ = v___y_4124_;
goto v___jp_4079_;
}
}
}
else
{
lean_dec_ref(v_k_4118_);
lean_dec_ref(v_decl_4068_);
v_k_4080_ = v_code_4067_;
v___y_4081_ = v___y_4119_;
v___y_4082_ = v___y_4120_;
v___y_4083_ = v___y_4121_;
v___y_4084_ = v___y_4122_;
v___y_4085_ = v___y_4123_;
v___y_4086_ = v___y_4124_;
goto v___jp_4079_;
}
}
}
else
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
lean_dec_ref(v_k_4118_);
lean_dec_ref(v_decl_4068_);
lean_dec_ref(v_code_4067_);
v___x_4151_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4152_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4151_);
v_k_4080_ = v___x_4152_;
v___y_4081_ = v___y_4119_;
v___y_4082_ = v___y_4120_;
v___y_4083_ = v___y_4121_;
v___y_4084_ = v___y_4122_;
v___y_4085_ = v___y_4123_;
v___y_4086_ = v___y_4124_;
goto v___jp_4079_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___boxed(lean_object* v_code_4569_, lean_object* v_decl_4570_, lean_object* v_k_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(v_code_4569_, v_decl_4570_, v_k_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_);
lean_dec(v_a_4577_);
lean_dec_ref(v_a_4576_);
lean_dec(v_a_4575_);
lean_dec_ref(v_a_4574_);
lean_dec(v_a_4573_);
lean_dec_ref(v_a_4572_);
return v_res_4579_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0(void){
_start:
{
lean_object* v___x_4580_; 
v___x_4580_ = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___redArg();
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5(lean_object* v_msg_4581_){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4582_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0);
v___x_4583_ = lean_panic_fn_borrowed(v___x_4582_, v_msg_4581_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(lean_object* v_a_4584_, lean_object* v_b_4585_, lean_object* v_x_4586_){
_start:
{
if (lean_obj_tag(v_x_4586_) == 0)
{
lean_dec(v_b_4585_);
lean_dec(v_a_4584_);
return v_x_4586_;
}
else
{
lean_object* v_key_4587_; lean_object* v_value_4588_; lean_object* v_tail_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4601_; 
v_key_4587_ = lean_ctor_get(v_x_4586_, 0);
v_value_4588_ = lean_ctor_get(v_x_4586_, 1);
v_tail_4589_ = lean_ctor_get(v_x_4586_, 2);
v_isSharedCheck_4601_ = !lean_is_exclusive(v_x_4586_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4591_ = v_x_4586_;
v_isShared_4592_ = v_isSharedCheck_4601_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_tail_4589_);
lean_inc(v_value_4588_);
lean_inc(v_key_4587_);
lean_dec(v_x_4586_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4601_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
uint8_t v___x_4593_; 
v___x_4593_ = l_Lean_instBEqFVarId_beq(v_key_4587_, v_a_4584_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; lean_object* v___x_4596_; 
v___x_4594_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(v_a_4584_, v_b_4585_, v_tail_4589_);
if (v_isShared_4592_ == 0)
{
lean_ctor_set(v___x_4591_, 2, v___x_4594_);
v___x_4596_ = v___x_4591_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_key_4587_);
lean_ctor_set(v_reuseFailAlloc_4597_, 1, v_value_4588_);
lean_ctor_set(v_reuseFailAlloc_4597_, 2, v___x_4594_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
else
{
lean_object* v___x_4599_; 
lean_dec(v_value_4588_);
lean_dec(v_key_4587_);
if (v_isShared_4592_ == 0)
{
lean_ctor_set(v___x_4591_, 1, v_b_4585_);
lean_ctor_set(v___x_4591_, 0, v_a_4584_);
v___x_4599_ = v___x_4591_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_a_4584_);
lean_ctor_set(v_reuseFailAlloc_4600_, 1, v_b_4585_);
lean_ctor_set(v_reuseFailAlloc_4600_, 2, v_tail_4589_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(lean_object* v_m_4602_, lean_object* v_a_4603_, lean_object* v_b_4604_){
_start:
{
lean_object* v_size_4605_; lean_object* v_buckets_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4649_; 
v_size_4605_ = lean_ctor_get(v_m_4602_, 0);
v_buckets_4606_ = lean_ctor_get(v_m_4602_, 1);
v_isSharedCheck_4649_ = !lean_is_exclusive(v_m_4602_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4608_ = v_m_4602_;
v_isShared_4609_ = v_isSharedCheck_4649_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_buckets_4606_);
lean_inc(v_size_4605_);
lean_dec(v_m_4602_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4649_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4610_; uint64_t v___x_4611_; uint64_t v___x_4612_; uint64_t v___x_4613_; uint64_t v_fold_4614_; uint64_t v___x_4615_; uint64_t v___x_4616_; uint64_t v___x_4617_; size_t v___x_4618_; size_t v___x_4619_; size_t v___x_4620_; size_t v___x_4621_; size_t v___x_4622_; lean_object* v_bkt_4623_; uint8_t v___x_4624_; 
v___x_4610_ = lean_array_get_size(v_buckets_4606_);
v___x_4611_ = l_Lean_instHashableFVarId_hash(v_a_4603_);
v___x_4612_ = 32ULL;
v___x_4613_ = lean_uint64_shift_right(v___x_4611_, v___x_4612_);
v_fold_4614_ = lean_uint64_xor(v___x_4611_, v___x_4613_);
v___x_4615_ = 16ULL;
v___x_4616_ = lean_uint64_shift_right(v_fold_4614_, v___x_4615_);
v___x_4617_ = lean_uint64_xor(v_fold_4614_, v___x_4616_);
v___x_4618_ = lean_uint64_to_usize(v___x_4617_);
v___x_4619_ = lean_usize_of_nat(v___x_4610_);
v___x_4620_ = ((size_t)1ULL);
v___x_4621_ = lean_usize_sub(v___x_4619_, v___x_4620_);
v___x_4622_ = lean_usize_land(v___x_4618_, v___x_4621_);
v_bkt_4623_ = lean_array_uget_borrowed(v_buckets_4606_, v___x_4622_);
v___x_4624_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_4603_, v_bkt_4623_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4625_; lean_object* v_size_x27_4626_; lean_object* v___x_4627_; lean_object* v_buckets_x27_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; 
v___x_4625_ = lean_unsigned_to_nat(1u);
v_size_x27_4626_ = lean_nat_add(v_size_4605_, v___x_4625_);
lean_dec(v_size_4605_);
lean_inc(v_bkt_4623_);
v___x_4627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4627_, 0, v_a_4603_);
lean_ctor_set(v___x_4627_, 1, v_b_4604_);
lean_ctor_set(v___x_4627_, 2, v_bkt_4623_);
v_buckets_x27_4628_ = lean_array_uset(v_buckets_4606_, v___x_4622_, v___x_4627_);
v___x_4629_ = lean_unsigned_to_nat(4u);
v___x_4630_ = lean_nat_mul(v_size_x27_4626_, v___x_4629_);
v___x_4631_ = lean_unsigned_to_nat(3u);
v___x_4632_ = lean_nat_div(v___x_4630_, v___x_4631_);
lean_dec(v___x_4630_);
v___x_4633_ = lean_array_get_size(v_buckets_x27_4628_);
v___x_4634_ = lean_nat_dec_le(v___x_4632_, v___x_4633_);
lean_dec(v___x_4632_);
if (v___x_4634_ == 0)
{
lean_object* v_val_4635_; lean_object* v___x_4637_; 
v_val_4635_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(v_buckets_x27_4628_);
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 1, v_val_4635_);
lean_ctor_set(v___x_4608_, 0, v_size_x27_4626_);
v___x_4637_ = v___x_4608_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_size_x27_4626_);
lean_ctor_set(v_reuseFailAlloc_4638_, 1, v_val_4635_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
else
{
lean_object* v___x_4640_; 
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 1, v_buckets_x27_4628_);
lean_ctor_set(v___x_4608_, 0, v_size_x27_4626_);
v___x_4640_ = v___x_4608_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_size_x27_4626_);
lean_ctor_set(v_reuseFailAlloc_4641_, 1, v_buckets_x27_4628_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
else
{
lean_object* v___x_4642_; lean_object* v_buckets_x27_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4647_; 
lean_inc(v_bkt_4623_);
v___x_4642_ = lean_box(0);
v_buckets_x27_4643_ = lean_array_uset(v_buckets_4606_, v___x_4622_, v___x_4642_);
v___x_4644_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(v_a_4603_, v_b_4604_, v_bkt_4623_);
v___x_4645_ = lean_array_uset(v_buckets_x27_4643_, v___x_4622_, v___x_4644_);
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 1, v___x_4645_);
v___x_4647_ = v___x_4608_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_size_4605_);
lean_ctor_set(v_reuseFailAlloc_4648_, 1, v___x_4645_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__2(lean_object* v_a_4650_, lean_object* v_a_4651_){
_start:
{
if (lean_obj_tag(v_a_4650_) == 0)
{
lean_object* v___x_4652_; 
v___x_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4652_, 0, v_a_4651_);
return v___x_4652_;
}
else
{
lean_object* v_key_4653_; lean_object* v_value_4654_; lean_object* v_tail_4655_; lean_object* v_r_4656_; 
v_key_4653_ = lean_ctor_get(v_a_4650_, 0);
lean_inc(v_key_4653_);
v_value_4654_ = lean_ctor_get(v_a_4650_, 1);
lean_inc(v_value_4654_);
v_tail_4655_ = lean_ctor_get(v_a_4650_, 2);
lean_inc(v_tail_4655_);
lean_dec_ref_known(v_a_4650_, 3);
v_r_4656_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(v_a_4651_, v_key_4653_, v_value_4654_);
v_a_4650_ = v_tail_4655_;
v_a_4651_ = v_r_4656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(lean_object* v_as_4658_, size_t v_sz_4659_, size_t v_i_4660_, lean_object* v_b_4661_){
_start:
{
uint8_t v___x_4662_; 
v___x_4662_ = lean_usize_dec_lt(v_i_4660_, v_sz_4659_);
if (v___x_4662_ == 0)
{
return v_b_4661_;
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4664_; 
v_a_4663_ = lean_array_uget_borrowed(v_as_4658_, v_i_4660_);
lean_inc(v_a_4663_);
v___x_4664_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__2(v_a_4663_, v_b_4661_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref_known(v___x_4664_, 1);
return v_a_4665_;
}
else
{
lean_object* v_a_4666_; size_t v___x_4667_; size_t v___x_4668_; 
v_a_4666_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___x_4664_, 1);
v___x_4667_ = ((size_t)1ULL);
v___x_4668_ = lean_usize_add(v_i_4660_, v___x_4667_);
v_i_4660_ = v___x_4668_;
v_b_4661_ = v_a_4666_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3___boxed(lean_object* v_as_4670_, lean_object* v_sz_4671_, lean_object* v_i_4672_, lean_object* v_b_4673_){
_start:
{
size_t v_sz_boxed_4674_; size_t v_i_boxed_4675_; lean_object* v_res_4676_; 
v_sz_boxed_4674_ = lean_unbox_usize(v_sz_4671_);
lean_dec(v_sz_4671_);
v_i_boxed_4675_ = lean_unbox_usize(v_i_4672_);
lean_dec(v_i_4672_);
v_res_4676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(v_as_4670_, v_sz_boxed_4674_, v_i_boxed_4675_, v_b_4673_);
lean_dec_ref(v_as_4670_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(lean_object* v_m_4677_, lean_object* v_l_4678_){
_start:
{
lean_object* v_buckets_4679_; size_t v_sz_4680_; size_t v___x_4681_; lean_object* v___x_4682_; 
v_buckets_4679_ = lean_ctor_get(v_l_4678_, 1);
v_sz_4680_ = lean_array_size(v_buckets_4679_);
v___x_4681_ = ((size_t)0ULL);
v___x_4682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(v_buckets_4679_, v_sz_4680_, v___x_4681_, v_m_4677_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1___boxed(lean_object* v_m_4683_, lean_object* v_l_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_m_4683_, v_l_4684_);
lean_dec_ref(v_l_4684_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(lean_object* v_a_4686_, lean_object* v_a_4687_){
_start:
{
if (lean_obj_tag(v_a_4686_) == 0)
{
lean_object* v___x_4688_; 
v___x_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4688_, 0, v_a_4687_);
return v___x_4688_;
}
else
{
lean_object* v_key_4689_; lean_object* v_value_4690_; lean_object* v_tail_4691_; lean_object* v_r_4692_; 
v_key_4689_ = lean_ctor_get(v_a_4686_, 0);
lean_inc(v_key_4689_);
v_value_4690_ = lean_ctor_get(v_a_4686_, 1);
lean_inc(v_value_4690_);
v_tail_4691_ = lean_ctor_get(v_a_4686_, 2);
lean_inc(v_tail_4691_);
lean_dec_ref_known(v_a_4686_, 3);
v_r_4692_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_a_4687_, v_key_4689_, v_value_4690_);
v_a_4686_ = v_tail_4691_;
v_a_4687_ = v_r_4692_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(lean_object* v_as_4694_, size_t v_sz_4695_, size_t v_i_4696_, lean_object* v_b_4697_){
_start:
{
uint8_t v___x_4698_; 
v___x_4698_ = lean_usize_dec_lt(v_i_4696_, v_sz_4695_);
if (v___x_4698_ == 0)
{
return v_b_4697_;
}
else
{
lean_object* v_a_4699_; lean_object* v___x_4700_; 
v_a_4699_ = lean_array_uget_borrowed(v_as_4694_, v_i_4696_);
lean_inc(v_a_4699_);
v___x_4700_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(v_a_4699_, v_b_4697_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v_a_4701_; 
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v___x_4700_, 1);
return v_a_4701_;
}
else
{
lean_object* v_a_4702_; size_t v___x_4703_; size_t v___x_4704_; 
v_a_4702_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4702_);
lean_dec_ref_known(v___x_4700_, 1);
v___x_4703_ = ((size_t)1ULL);
v___x_4704_ = lean_usize_add(v_i_4696_, v___x_4703_);
v_i_4696_ = v___x_4704_;
v_b_4697_ = v_a_4702_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2___boxed(lean_object* v_as_4706_, lean_object* v_sz_4707_, lean_object* v_i_4708_, lean_object* v_b_4709_){
_start:
{
size_t v_sz_boxed_4710_; size_t v_i_boxed_4711_; lean_object* v_res_4712_; 
v_sz_boxed_4710_ = lean_unbox_usize(v_sz_4707_);
lean_dec(v_sz_4707_);
v_i_boxed_4711_ = lean_unbox_usize(v_i_4708_);
lean_dec(v_i_4708_);
v_res_4712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_as_4706_, v_sz_boxed_4710_, v_i_boxed_4711_, v_b_4709_);
lean_dec_ref(v_as_4706_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(lean_object* v_as_4713_, size_t v_i_4714_, size_t v_stop_4715_, lean_object* v_b_4716_){
_start:
{
lean_object* v___y_4718_; lean_object* v___y_4719_; uint8_t v___x_4724_; 
v___x_4724_ = lean_usize_dec_eq(v_i_4714_, v_stop_4715_);
if (v___x_4724_ == 0)
{
lean_object* v___x_4725_; lean_object* v_snd_4726_; lean_object* v_vars_4727_; lean_object* v_borrows_4728_; lean_object* v_vars_4729_; lean_object* v_borrows_4730_; lean_object* v___y_4732_; lean_object* v_size_4741_; lean_object* v_buckets_4742_; lean_object* v_size_4743_; uint8_t v___x_4744_; 
v___x_4725_ = lean_array_uget_borrowed(v_as_4713_, v_i_4714_);
v_snd_4726_ = lean_ctor_get(v___x_4725_, 1);
v_vars_4727_ = lean_ctor_get(v_b_4716_, 0);
lean_inc_ref(v_vars_4727_);
v_borrows_4728_ = lean_ctor_get(v_b_4716_, 1);
lean_inc_ref(v_borrows_4728_);
lean_dec_ref(v_b_4716_);
v_vars_4729_ = lean_ctor_get(v_snd_4726_, 0);
v_borrows_4730_ = lean_ctor_get(v_snd_4726_, 1);
v_size_4741_ = lean_ctor_get(v_vars_4727_, 0);
v_buckets_4742_ = lean_ctor_get(v_vars_4727_, 1);
v_size_4743_ = lean_ctor_get(v_vars_4729_, 0);
v___x_4744_ = lean_nat_dec_le(v_size_4741_, v_size_4743_);
if (v___x_4744_ == 0)
{
lean_object* v___x_4745_; 
v___x_4745_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_vars_4727_, v_vars_4729_);
v___y_4732_ = v___x_4745_;
goto v___jp_4731_;
}
else
{
size_t v_sz_4746_; size_t v___x_4747_; lean_object* v___x_4748_; 
lean_inc_ref(v_buckets_4742_);
lean_dec_ref(v_vars_4727_);
v_sz_4746_ = lean_array_size(v_buckets_4742_);
v___x_4747_ = ((size_t)0ULL);
lean_inc_ref(v_vars_4729_);
v___x_4748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_buckets_4742_, v_sz_4746_, v___x_4747_, v_vars_4729_);
lean_dec_ref(v_buckets_4742_);
v___y_4732_ = v___x_4748_;
goto v___jp_4731_;
}
v___jp_4731_:
{
lean_object* v_size_4733_; lean_object* v_buckets_4734_; lean_object* v_size_4735_; uint8_t v___x_4736_; 
v_size_4733_ = lean_ctor_get(v_borrows_4728_, 0);
v_buckets_4734_ = lean_ctor_get(v_borrows_4728_, 1);
v_size_4735_ = lean_ctor_get(v_borrows_4730_, 0);
v___x_4736_ = lean_nat_dec_le(v_size_4733_, v_size_4735_);
if (v___x_4736_ == 0)
{
lean_object* v___x_4737_; 
v___x_4737_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_borrows_4728_, v_borrows_4730_);
v___y_4718_ = v___y_4732_;
v___y_4719_ = v___x_4737_;
goto v___jp_4717_;
}
else
{
size_t v_sz_4738_; size_t v___x_4739_; lean_object* v___x_4740_; 
lean_inc_ref(v_buckets_4734_);
lean_dec_ref(v_borrows_4728_);
v_sz_4738_ = lean_array_size(v_buckets_4734_);
v___x_4739_ = ((size_t)0ULL);
lean_inc_ref(v_borrows_4730_);
v___x_4740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_buckets_4734_, v_sz_4738_, v___x_4739_, v_borrows_4730_);
lean_dec_ref(v_buckets_4734_);
v___y_4718_ = v___y_4732_;
v___y_4719_ = v___x_4740_;
goto v___jp_4717_;
}
}
}
else
{
return v_b_4716_;
}
v___jp_4717_:
{
lean_object* v___x_4720_; size_t v___x_4721_; size_t v___x_4722_; 
v___x_4720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4720_, 0, v___y_4718_);
lean_ctor_set(v___x_4720_, 1, v___y_4719_);
v___x_4721_ = ((size_t)1ULL);
v___x_4722_ = lean_usize_add(v_i_4714_, v___x_4721_);
v_i_4714_ = v___x_4722_;
v_b_4716_ = v___x_4720_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8___boxed(lean_object* v_as_4749_, lean_object* v_i_4750_, lean_object* v_stop_4751_, lean_object* v_b_4752_){
_start:
{
size_t v_i_boxed_4753_; size_t v_stop_boxed_4754_; lean_object* v_res_4755_; 
v_i_boxed_4753_ = lean_unbox_usize(v_i_4750_);
lean_dec(v_i_4750_);
v_stop_boxed_4754_ = lean_unbox_usize(v_stop_4751_);
lean_dec(v_stop_4751_);
v_res_4755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_as_4749_, v_i_boxed_4753_, v_stop_boxed_4754_, v_b_4752_);
lean_dec_ref(v_as_4749_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(lean_object* v_as_4756_, size_t v_i_4757_, size_t v_stop_4758_, lean_object* v_b_4759_){
_start:
{
lean_object* v___y_4761_; uint8_t v___x_4765_; 
v___x_4765_ = lean_usize_dec_eq(v_i_4757_, v_stop_4758_);
if (v___x_4765_ == 0)
{
lean_object* v_resetTargets_4766_; lean_object* v_unconditionalBorrows_4767_; lean_object* v_derivedValMap_4768_; lean_object* v_varMap_4769_; lean_object* v_jpLiveVarMap_4770_; lean_object* v_idx_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4792_; 
v_resetTargets_4766_ = lean_ctor_get(v_b_4759_, 0);
v_unconditionalBorrows_4767_ = lean_ctor_get(v_b_4759_, 1);
v_derivedValMap_4768_ = lean_ctor_get(v_b_4759_, 2);
v_varMap_4769_ = lean_ctor_get(v_b_4759_, 3);
v_jpLiveVarMap_4770_ = lean_ctor_get(v_b_4759_, 4);
v_idx_4771_ = lean_ctor_get(v_b_4759_, 5);
v_isSharedCheck_4792_ = !lean_is_exclusive(v_b_4759_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4773_ = v_b_4759_;
v_isShared_4774_ = v_isSharedCheck_4792_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_idx_4771_);
lean_inc(v_jpLiveVarMap_4770_);
lean_inc(v_varMap_4769_);
lean_inc(v_derivedValMap_4768_);
lean_inc(v_unconditionalBorrows_4767_);
lean_inc(v_resetTargets_4766_);
lean_dec(v_b_4759_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4792_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4775_; lean_object* v_fvarId_4776_; lean_object* v_type_4777_; uint8_t v_borrow_4778_; uint8_t v___x_4779_; uint8_t v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v_varMap_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v_ctx_4787_; 
v___x_4775_ = lean_array_uget_borrowed(v_as_4756_, v_i_4757_);
v_fvarId_4776_ = lean_ctor_get(v___x_4775_, 0);
v_type_4777_ = lean_ctor_get(v___x_4775_, 2);
v_borrow_4778_ = lean_ctor_get_uint8(v___x_4775_, sizeof(void*)*3);
v___x_4779_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_4777_);
v___x_4780_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_4777_);
v___x_4781_ = lean_box(0);
lean_inc(v_idx_4771_);
v___x_4782_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4782_, 0, v_idx_4771_);
lean_ctor_set(v___x_4782_, 1, v___x_4781_);
lean_ctor_set_uint8(v___x_4782_, sizeof(void*)*2, v___x_4779_);
lean_ctor_set_uint8(v___x_4782_, sizeof(void*)*2 + 1, v___x_4780_);
lean_ctor_set_uint8(v___x_4782_, sizeof(void*)*2 + 2, v___x_4765_);
lean_inc(v_fvarId_4776_);
v_varMap_4783_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_4776_, v___x_4782_, v_varMap_4769_);
v___x_4784_ = lean_unsigned_to_nat(1u);
v___x_4785_ = lean_nat_add(v_idx_4771_, v___x_4784_);
lean_dec(v_idx_4771_);
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 5, v___x_4785_);
lean_ctor_set(v___x_4773_, 3, v_varMap_4783_);
v_ctx_4787_ = v___x_4773_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_resetTargets_4766_);
lean_ctor_set(v_reuseFailAlloc_4791_, 1, v_unconditionalBorrows_4767_);
lean_ctor_set(v_reuseFailAlloc_4791_, 2, v_derivedValMap_4768_);
lean_ctor_set(v_reuseFailAlloc_4791_, 3, v_varMap_4783_);
lean_ctor_set(v_reuseFailAlloc_4791_, 4, v_jpLiveVarMap_4770_);
lean_ctor_set(v_reuseFailAlloc_4791_, 5, v___x_4785_);
v_ctx_4787_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
lean_object* v___x_4788_; lean_object* v_ctx_4789_; 
v___x_4788_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
lean_inc(v_fvarId_4776_);
v_ctx_4789_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_4787_, v___x_4788_, v_fvarId_4776_);
if (v_borrow_4778_ == 0)
{
v___y_4761_ = v_ctx_4789_;
goto v___jp_4760_;
}
else
{
if (v___x_4779_ == 0)
{
v___y_4761_ = v_ctx_4789_;
goto v___jp_4760_;
}
else
{
lean_object* v___x_4790_; 
lean_inc(v_fvarId_4776_);
v___x_4790_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(v_ctx_4789_, v_fvarId_4776_);
v___y_4761_ = v___x_4790_;
goto v___jp_4760_;
}
}
}
}
}
else
{
return v_b_4759_;
}
v___jp_4760_:
{
size_t v___x_4762_; size_t v___x_4763_; 
v___x_4762_ = ((size_t)1ULL);
v___x_4763_ = lean_usize_add(v_i_4757_, v___x_4762_);
v_i_4757_ = v___x_4763_;
v_b_4759_ = v___y_4761_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3___boxed(lean_object* v_as_4793_, lean_object* v_i_4794_, lean_object* v_stop_4795_, lean_object* v_b_4796_){
_start:
{
size_t v_i_boxed_4797_; size_t v_stop_boxed_4798_; lean_object* v_res_4799_; 
v_i_boxed_4797_ = lean_unbox_usize(v_i_4794_);
lean_dec(v_i_4794_);
v_stop_boxed_4798_ = lean_unbox_usize(v_stop_4795_);
lean_dec(v_stop_4795_);
v_res_4799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_as_4793_, v_i_boxed_4797_, v_stop_boxed_4798_, v_b_4796_);
lean_dec_ref(v_as_4793_);
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4_spec__7(lean_object* v_msg_4800_){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
v___x_4802_ = lean_panic_fn_borrowed(v___x_4801_, v_msg_4800_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(lean_object* v_t_4803_, lean_object* v_k_4804_){
_start:
{
if (lean_obj_tag(v_t_4803_) == 0)
{
lean_object* v_k_4805_; lean_object* v_v_4806_; lean_object* v_l_4807_; lean_object* v_r_4808_; uint8_t v___x_4809_; 
v_k_4805_ = lean_ctor_get(v_t_4803_, 1);
v_v_4806_ = lean_ctor_get(v_t_4803_, 2);
v_l_4807_ = lean_ctor_get(v_t_4803_, 3);
v_r_4808_ = lean_ctor_get(v_t_4803_, 4);
v___x_4809_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4804_, v_k_4805_);
switch(v___x_4809_)
{
case 0:
{
v_t_4803_ = v_l_4807_;
goto _start;
}
case 1:
{
lean_inc(v_v_4806_);
return v_v_4806_;
}
default: 
{
v_t_4803_ = v_r_4808_;
goto _start;
}
}
}
else
{
lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4812_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3);
v___x_4813_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4_spec__7(v___x_4812_);
return v___x_4813_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4___boxed(lean_object* v_t_4814_, lean_object* v_k_4815_){
_start:
{
lean_object* v_res_4816_; 
v_res_4816_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(v_t_4814_, v_k_4815_);
lean_dec(v_k_4815_);
lean_dec(v_t_4814_);
return v_res_4816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(lean_object* v_discr_4817_, size_t v_sz_4818_, size_t v_i_4819_, lean_object* v_bs_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_){
_start:
{
uint8_t v___x_4828_; 
v___x_4828_ = lean_usize_dec_lt(v_i_4819_, v_sz_4818_);
if (v___x_4828_ == 0)
{
lean_object* v___x_4829_; 
lean_dec(v_discr_4817_);
v___x_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4829_, 0, v_bs_4820_);
return v___x_4829_;
}
else
{
lean_object* v_v_4830_; lean_object* v_fst_4831_; lean_object* v_snd_4832_; lean_object* v___x_4833_; lean_object* v_bs_x27_4834_; lean_object* v_a_4836_; 
v_v_4830_ = lean_array_uget_borrowed(v_bs_4820_, v_i_4819_);
v_fst_4831_ = lean_ctor_get(v_v_4830_, 0);
lean_inc(v_fst_4831_);
v_snd_4832_ = lean_ctor_get(v_v_4830_, 1);
lean_inc(v_snd_4832_);
v___x_4833_ = lean_unsigned_to_nat(0u);
v_bs_x27_4834_ = lean_array_uset(v_bs_4820_, v_i_4819_, v___x_4833_);
if (lean_obj_tag(v_fst_4831_) == 1)
{
lean_object* v_info_4841_; lean_object* v_code_4842_; lean_object* v_resetTargets_4843_; lean_object* v_unconditionalBorrows_4844_; lean_object* v_derivedValMap_4845_; lean_object* v_varMap_4846_; lean_object* v_jpLiveVarMap_4847_; lean_object* v_idx_4848_; lean_object* v___y_4850_; lean_object* v___x_4865_; 
v_info_4841_ = lean_ctor_get(v_fst_4831_, 0);
v_code_4842_ = lean_ctor_get(v_fst_4831_, 1);
v_resetTargets_4843_ = lean_ctor_get(v___y_4821_, 0);
v_unconditionalBorrows_4844_ = lean_ctor_get(v___y_4821_, 1);
v_derivedValMap_4845_ = lean_ctor_get(v___y_4821_, 2);
v_varMap_4846_ = lean_ctor_get(v___y_4821_, 3);
v_jpLiveVarMap_4847_ = lean_ctor_get(v___y_4821_, 4);
v_idx_4848_ = lean_ctor_get(v___y_4821_, 5);
v___x_4865_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_varMap_4846_, v_discr_4817_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_inc(v_varMap_4846_);
v___y_4850_ = v_varMap_4846_;
goto v___jp_4849_;
}
else
{
lean_object* v_val_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4887_; 
v_val_4866_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4868_ = v___x_4865_;
v_isShared_4869_ = v_isSharedCheck_4887_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_val_4866_);
lean_dec(v___x_4865_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4887_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
uint8_t v_persistent_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4884_; 
v_persistent_4870_ = lean_ctor_get_uint8(v_val_4866_, sizeof(void*)*2 + 2);
v_isSharedCheck_4884_ = !lean_is_exclusive(v_val_4866_);
if (v_isSharedCheck_4884_ == 0)
{
lean_object* v_unused_4885_; lean_object* v_unused_4886_; 
v_unused_4885_ = lean_ctor_get(v_val_4866_, 1);
lean_dec(v_unused_4885_);
v_unused_4886_ = lean_ctor_get(v_val_4866_, 0);
lean_dec(v_unused_4886_);
v___x_4872_ = v_val_4866_;
v_isShared_4873_ = v_isSharedCheck_4884_;
goto v_resetjp_4871_;
}
else
{
lean_dec(v_val_4866_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4884_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
uint8_t v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4878_; 
v___x_4874_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_info_4841_);
v___x_4875_ = lean_unsigned_to_nat(1u);
v___x_4876_ = lean_nat_add(v_idx_4848_, v___x_4875_);
lean_inc_ref(v_info_4841_);
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 0, v_info_4841_);
v___x_4878_ = v___x_4868_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_info_4841_);
v___x_4878_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
lean_object* v___x_4880_; 
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 1, v___x_4878_);
lean_ctor_set(v___x_4872_, 0, v___x_4876_);
v___x_4880_ = v___x_4872_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v___x_4876_);
lean_ctor_set(v_reuseFailAlloc_4882_, 1, v___x_4878_);
lean_ctor_set_uint8(v_reuseFailAlloc_4882_, sizeof(void*)*2 + 2, v_persistent_4870_);
v___x_4880_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
lean_object* v___x_4881_; 
lean_ctor_set_uint8(v___x_4880_, sizeof(void*)*2, v___x_4874_);
lean_ctor_set_uint8(v___x_4880_, sizeof(void*)*2 + 1, v___x_4874_);
lean_inc(v_varMap_4846_);
lean_inc(v_discr_4817_);
v___x_4881_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_4817_, v___x_4880_, v_varMap_4846_);
v___y_4850_ = v___x_4881_;
goto v___jp_4849_;
}
}
}
}
}
v___jp_4849_:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; 
v___x_4851_ = lean_unsigned_to_nat(1u);
v___x_4852_ = lean_nat_add(v_idx_4848_, v___x_4851_);
lean_inc(v_jpLiveVarMap_4847_);
lean_inc(v_derivedValMap_4845_);
lean_inc(v_unconditionalBorrows_4844_);
lean_inc_ref(v_resetTargets_4843_);
v___x_4853_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4853_, 0, v_resetTargets_4843_);
lean_ctor_set(v___x_4853_, 1, v_unconditionalBorrows_4844_);
lean_ctor_set(v___x_4853_, 2, v_derivedValMap_4845_);
lean_ctor_set(v___x_4853_, 3, v___y_4850_);
lean_ctor_set(v___x_4853_, 4, v_jpLiveVarMap_4847_);
lean_ctor_set(v___x_4853_, 5, v___x_4852_);
lean_inc_ref(v_code_4842_);
v___x_4854_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_snd_4832_, v_code_4842_, v___x_4853_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
lean_dec_ref_known(v___x_4853_, 6);
lean_dec(v_snd_4832_);
if (lean_obj_tag(v___x_4854_) == 0)
{
lean_object* v_a_4855_; lean_object* v___x_4856_; 
v_a_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc(v_a_4855_);
lean_dec_ref_known(v___x_4854_, 1);
v___x_4856_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_fst_4831_, v_a_4855_);
v_a_4836_ = v___x_4856_;
goto v___jp_4835_;
}
else
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
lean_dec_ref_known(v_fst_4831_, 2);
lean_dec_ref(v_bs_x27_4834_);
lean_dec(v_discr_4817_);
v_a_4857_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4859_ = v___x_4854_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4854_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
}
}
else
{
lean_object* v_code_4888_; lean_object* v___x_4889_; 
v_code_4888_ = lean_ctor_get(v_fst_4831_, 0);
lean_inc_ref(v_code_4888_);
v___x_4889_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_snd_4832_, v_code_4888_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
lean_dec(v_snd_4832_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4891_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
lean_inc(v_a_4890_);
lean_dec_ref_known(v___x_4889_, 1);
v___x_4891_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_fst_4831_, v_a_4890_);
v_a_4836_ = v___x_4891_;
goto v___jp_4835_;
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec_ref_known(v_fst_4831_, 1);
lean_dec_ref(v_bs_x27_4834_);
lean_dec(v_discr_4817_);
v_a_4892_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4889_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4889_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
v___jp_4835_:
{
size_t v___x_4837_; size_t v___x_4838_; lean_object* v___x_4839_; 
v___x_4837_ = ((size_t)1ULL);
v___x_4838_ = lean_usize_add(v_i_4819_, v___x_4837_);
v___x_4839_ = lean_array_uset(v_bs_x27_4834_, v_i_4819_, v_a_4836_);
v_i_4819_ = v___x_4838_;
v_bs_4820_ = v___x_4839_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7___boxed(lean_object* v_discr_4900_, lean_object* v_sz_4901_, lean_object* v_i_4902_, lean_object* v_bs_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
size_t v_sz_boxed_4911_; size_t v_i_boxed_4912_; lean_object* v_res_4913_; 
v_sz_boxed_4911_ = lean_unbox_usize(v_sz_4901_);
lean_dec(v_sz_4901_);
v_i_boxed_4912_ = lean_unbox_usize(v_i_4902_);
lean_dec(v_i_4902_);
v_res_4913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(v_discr_4900_, v_sz_boxed_4911_, v_i_boxed_4912_, v_bs_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
lean_dec(v___y_4905_);
lean_dec_ref(v___y_4904_);
return v_res_4913_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1(void){
_start:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4915_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_4916_ = lean_unsigned_to_nat(59u);
v___x_4917_ = lean_unsigned_to_nat(655u);
v___x_4918_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__0));
v___x_4919_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_4920_ = l_mkPanicMessageWithDecl(v___x_4919_, v___x_4918_, v___x_4917_, v___x_4916_, v___x_4915_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(lean_object* v_code_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_){
_start:
{
switch(lean_obj_tag(v_code_4921_))
{
case 0:
{
lean_object* v_decl_4929_; lean_object* v_k_4930_; lean_object* v_fvarId_4931_; lean_object* v_type_4932_; lean_object* v_value_4933_; lean_object* v___y_4935_; 
v_decl_4929_ = lean_ctor_get(v_code_4921_, 0);
lean_inc_ref(v_decl_4929_);
v_k_4930_ = lean_ctor_get(v_code_4921_, 1);
v_fvarId_4931_ = lean_ctor_get(v_decl_4929_, 0);
v_type_4932_ = lean_ctor_get(v_decl_4929_, 2);
v_value_4933_ = lean_ctor_get(v_decl_4929_, 3);
if (lean_obj_tag(v_value_4933_) == 5)
{
lean_object* v_i_4954_; lean_object* v___x_4955_; 
v_i_4954_ = lean_ctor_get(v_value_4933_, 0);
lean_inc_ref(v_i_4954_);
v___x_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4955_, 0, v_i_4954_);
v___y_4935_ = v___x_4955_;
goto v___jp_4934_;
}
else
{
lean_object* v___x_4956_; 
v___x_4956_ = lean_box(0);
v___y_4935_ = v___x_4956_;
goto v___jp_4934_;
}
v___jp_4934_:
{
lean_object* v_resetTargets_4936_; lean_object* v_unconditionalBorrows_4937_; lean_object* v_derivedValMap_4938_; lean_object* v_varMap_4939_; lean_object* v_jpLiveVarMap_4940_; lean_object* v_idx_4941_; uint8_t v___x_4942_; uint8_t v___x_4943_; uint8_t v___x_4944_; lean_object* v_varInfo_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v_ctx_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
v_resetTargets_4936_ = lean_ctor_get(v_a_4922_, 0);
v_unconditionalBorrows_4937_ = lean_ctor_get(v_a_4922_, 1);
v_derivedValMap_4938_ = lean_ctor_get(v_a_4922_, 2);
v_varMap_4939_ = lean_ctor_get(v_a_4922_, 3);
v_jpLiveVarMap_4940_ = lean_ctor_get(v_a_4922_, 4);
v_idx_4941_ = lean_ctor_get(v_a_4922_, 5);
v___x_4942_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_4932_);
v___x_4943_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_4932_);
v___x_4944_ = l_Lean_Compiler_LCNF_LetValue_isPersistent(v_value_4933_);
lean_inc(v_idx_4941_);
v_varInfo_4945_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_varInfo_4945_, 0, v_idx_4941_);
lean_ctor_set(v_varInfo_4945_, 1, v___y_4935_);
lean_ctor_set_uint8(v_varInfo_4945_, sizeof(void*)*2, v___x_4942_);
lean_ctor_set_uint8(v_varInfo_4945_, sizeof(void*)*2 + 1, v___x_4943_);
lean_ctor_set_uint8(v_varInfo_4945_, sizeof(void*)*2 + 2, v___x_4944_);
lean_inc(v_varMap_4939_);
lean_inc(v_fvarId_4931_);
v___x_4946_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_4931_, v_varInfo_4945_, v_varMap_4939_);
v___x_4947_ = lean_unsigned_to_nat(1u);
v___x_4948_ = lean_nat_add(v_idx_4941_, v___x_4947_);
lean_inc(v_jpLiveVarMap_4940_);
lean_inc(v_derivedValMap_4938_);
lean_inc(v_unconditionalBorrows_4937_);
lean_inc_ref(v_resetTargets_4936_);
v_ctx_4949_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_ctx_4949_, 0, v_resetTargets_4936_);
lean_ctor_set(v_ctx_4949_, 1, v_unconditionalBorrows_4937_);
lean_ctor_set(v_ctx_4949_, 2, v_derivedValMap_4938_);
lean_ctor_set(v_ctx_4949_, 3, v___x_4946_);
lean_ctor_set(v_ctx_4949_, 4, v_jpLiveVarMap_4940_);
lean_ctor_set(v_ctx_4949_, 5, v___x_4948_);
lean_inc_ref(v_decl_4929_);
v___x_4950_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(v_ctx_4949_, v_decl_4929_);
lean_inc_ref(v_k_4930_);
v___x_4951_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_4930_, v___x_4950_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
if (lean_obj_tag(v___x_4951_) == 0)
{
lean_object* v_a_4952_; lean_object* v___x_4953_; 
v_a_4952_ = lean_ctor_get(v___x_4951_, 0);
lean_inc(v_a_4952_);
lean_dec_ref_known(v___x_4951_, 1);
v___x_4953_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(v_code_4921_, v_decl_4929_, v_a_4952_, v___x_4950_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
lean_dec_ref(v___x_4950_);
return v___x_4953_;
}
else
{
lean_dec_ref(v___x_4950_);
lean_dec_ref(v_decl_4929_);
lean_dec_ref_known(v_code_4921_, 2);
return v___x_4951_;
}
}
}
case 2:
{
lean_object* v_decl_4957_; lean_object* v_k_4958_; lean_object* v_fst_4960_; lean_object* v_snd_4961_; lean_object* v_params_5010_; lean_object* v_type_5011_; lean_object* v_value_5012_; uint8_t v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; uint8_t v___x_5016_; 
v_decl_4957_ = lean_ctor_get(v_code_4921_, 0);
v_k_4958_ = lean_ctor_get(v_code_4921_, 1);
v_params_5010_ = lean_ctor_get(v_decl_4957_, 2);
v_type_5011_ = lean_ctor_get(v_decl_4957_, 3);
v_value_5012_ = lean_ctor_get(v_decl_4957_, 4);
v___x_5013_ = 1;
v___x_5014_ = lean_unsigned_to_nat(0u);
v___x_5015_ = lean_array_get_size(v_params_5010_);
v___x_5016_ = lean_nat_dec_lt(v___x_5014_, v___x_5015_);
if (v___x_5016_ == 0)
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5017_ = lean_st_ref_get(v_a_4923_);
v___x_5018_ = lean_st_ref_take(v_a_4923_);
lean_dec(v___x_5018_);
v___x_5019_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5020_ = lean_st_ref_put(v_a_4923_, v___x_5019_);
lean_inc_ref(v_value_5012_);
v___x_5021_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_value_5012_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_a_5022_; lean_object* v___x_5023_; 
v_a_5022_ = lean_ctor_get(v___x_5021_, 0);
lean_inc(v_a_5022_);
lean_dec_ref_known(v___x_5021_, 1);
v___x_5023_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5010_, v_a_5022_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
if (lean_obj_tag(v___x_5023_) == 0)
{
lean_object* v_a_5024_; lean_object* v___x_5025_; 
v_a_5024_ = lean_ctor_get(v___x_5023_, 0);
lean_inc(v_a_5024_);
lean_dec_ref_known(v___x_5023_, 1);
lean_inc_ref(v_params_5010_);
lean_inc_ref(v_type_5011_);
lean_inc_ref(v_decl_4957_);
v___x_5025_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5013_, v_decl_4957_, v_type_5011_, v_params_5010_, v_a_5024_, v_a_4925_);
if (lean_obj_tag(v___x_5025_) == 0)
{
lean_object* v_a_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v_a_5026_ = lean_ctor_get(v___x_5025_, 0);
lean_inc(v_a_5026_);
lean_dec_ref_known(v___x_5025_, 1);
v___x_5027_ = lean_st_ref_get(v_a_4923_);
v___x_5028_ = lean_st_ref_take(v_a_4923_);
lean_dec(v___x_5028_);
v___x_5029_ = lean_st_ref_put(v_a_4923_, v___x_5017_);
v_fst_4960_ = v_a_5026_;
v_snd_4961_ = v___x_5027_;
goto v___jp_4959_;
}
else
{
lean_object* v_a_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5037_; 
lean_dec(v___x_5017_);
lean_dec_ref_known(v_code_4921_, 2);
v_a_5030_ = lean_ctor_get(v___x_5025_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_5025_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5032_ = v___x_5025_;
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_a_5030_);
lean_dec(v___x_5025_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5035_; 
if (v_isShared_5033_ == 0)
{
v___x_5035_ = v___x_5032_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_a_5030_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
}
}
}
}
else
{
lean_dec(v___x_5017_);
lean_dec_ref_known(v_code_4921_, 2);
return v___x_5023_;
}
}
else
{
lean_dec(v___x_5017_);
lean_dec_ref_known(v_code_4921_, 2);
return v___x_5021_;
}
}
else
{
size_t v___x_5038_; size_t v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5038_ = ((size_t)0ULL);
v___x_5039_ = lean_usize_of_nat(v___x_5015_);
lean_inc_ref(v_a_4922_);
v___x_5040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_params_5010_, v___x_5038_, v___x_5039_, v_a_4922_);
v___x_5041_ = lean_st_ref_get(v_a_4923_);
v___x_5042_ = lean_st_ref_take(v_a_4923_);
lean_dec(v___x_5042_);
v___x_5043_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5044_ = lean_st_ref_put(v_a_4923_, v___x_5043_);
lean_inc_ref(v_value_5012_);
v___x_5045_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_value_5012_, v___x_5040_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
if (lean_obj_tag(v___x_5045_) == 0)
{
lean_object* v_a_5046_; lean_object* v___x_5047_; 
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
lean_inc(v_a_5046_);
lean_dec_ref_known(v___x_5045_, 1);
v___x_5047_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5010_, v_a_5046_, v___x_5040_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
lean_dec_ref(v___x_5040_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; lean_object* v___x_5049_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
lean_inc(v_a_5048_);
lean_dec_ref_known(v___x_5047_, 1);
lean_inc_ref(v_params_5010_);
lean_inc_ref(v_type_5011_);
lean_inc_ref(v_decl_4957_);
v___x_5049_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5013_, v_decl_4957_, v_type_5011_, v_params_5010_, v_a_5048_, v_a_4925_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_a_5050_);
lean_dec_ref_known(v___x_5049_, 1);
v___x_5051_ = lean_st_ref_get(v_a_4923_);
v___x_5052_ = lean_st_ref_take(v_a_4923_);
lean_dec(v___x_5052_);
v___x_5053_ = lean_st_ref_put(v_a_4923_, v___x_5041_);
v_fst_4960_ = v_a_5050_;
v_snd_4961_ = v___x_5051_;
goto v___jp_4959_;
}
else
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5061_; 
lean_dec(v___x_5041_);
lean_dec_ref_known(v_code_4921_, 2);
v_a_5054_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5061_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5061_ == 0)
{
v___x_5056_ = v___x_5049_;
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v___x_5049_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5059_; 
if (v_isShared_5057_ == 0)
{
v___x_5059_ = v___x_5056_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_a_5054_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
return v___x_5059_;
}
}
}
}
else
{
lean_dec(v___x_5041_);
lean_dec_ref_known(v_code_4921_, 2);
return v___x_5047_;
}
}
else
{
lean_dec(v___x_5041_);
lean_dec_ref(v___x_5040_);
lean_dec_ref_known(v_code_4921_, 2);
return v___x_5045_;
}
}
v___jp_4959_:
{
lean_object* v_fvarId_4962_; lean_object* v_resetTargets_4963_; lean_object* v_unconditionalBorrows_4964_; lean_object* v_derivedValMap_4965_; lean_object* v_varMap_4966_; lean_object* v_jpLiveVarMap_4967_; lean_object* v_idx_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v_fvarId_4962_ = lean_ctor_get(v_fst_4960_, 0);
v_resetTargets_4963_ = lean_ctor_get(v_a_4922_, 0);
v_unconditionalBorrows_4964_ = lean_ctor_get(v_a_4922_, 1);
v_derivedValMap_4965_ = lean_ctor_get(v_a_4922_, 2);
v_varMap_4966_ = lean_ctor_get(v_a_4922_, 3);
v_jpLiveVarMap_4967_ = lean_ctor_get(v_a_4922_, 4);
v_idx_4968_ = lean_ctor_get(v_a_4922_, 5);
lean_inc(v_jpLiveVarMap_4967_);
lean_inc(v_fvarId_4962_);
v___x_4969_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_4962_, v_snd_4961_, v_jpLiveVarMap_4967_);
lean_inc(v_idx_4968_);
lean_inc(v_varMap_4966_);
lean_inc(v_derivedValMap_4965_);
lean_inc(v_unconditionalBorrows_4964_);
lean_inc_ref(v_resetTargets_4963_);
v___x_4970_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4970_, 0, v_resetTargets_4963_);
lean_ctor_set(v___x_4970_, 1, v_unconditionalBorrows_4964_);
lean_ctor_set(v___x_4970_, 2, v_derivedValMap_4965_);
lean_ctor_set(v___x_4970_, 3, v_varMap_4966_);
lean_ctor_set(v___x_4970_, 4, v___x_4969_);
lean_ctor_set(v___x_4970_, 5, v_idx_4968_);
lean_inc_ref(v_k_4958_);
v___x_4971_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_4958_, v___x_4970_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
lean_dec_ref_known(v___x_4970_, 6);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v_a_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_5009_; 
v_a_4972_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_4974_ = v___x_4971_;
v_isShared_4975_ = v_isSharedCheck_5009_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_dec(v___x_4971_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_5009_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
size_t v___x_4976_; size_t v___x_4977_; uint8_t v___x_4978_; 
v___x_4976_ = lean_ptr_addr(v_k_4958_);
v___x_4977_ = lean_ptr_addr(v_a_4972_);
v___x_4978_ = lean_usize_dec_eq(v___x_4976_, v___x_4977_);
if (v___x_4978_ == 0)
{
lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4988_; 
v_isSharedCheck_4988_ = !lean_is_exclusive(v_code_4921_);
if (v_isSharedCheck_4988_ == 0)
{
lean_object* v_unused_4989_; lean_object* v_unused_4990_; 
v_unused_4989_ = lean_ctor_get(v_code_4921_, 1);
lean_dec(v_unused_4989_);
v_unused_4990_ = lean_ctor_get(v_code_4921_, 0);
lean_dec(v_unused_4990_);
v___x_4980_ = v_code_4921_;
v_isShared_4981_ = v_isSharedCheck_4988_;
goto v_resetjp_4979_;
}
else
{
lean_dec(v_code_4921_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4988_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4983_; 
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 1, v_a_4972_);
lean_ctor_set(v___x_4980_, 0, v_fst_4960_);
v___x_4983_ = v___x_4980_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_fst_4960_);
lean_ctor_set(v_reuseFailAlloc_4987_, 1, v_a_4972_);
v___x_4983_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
lean_object* v___x_4985_; 
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 0, v___x_4983_);
v___x_4985_ = v___x_4974_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v___x_4983_);
v___x_4985_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
return v___x_4985_;
}
}
}
}
else
{
size_t v___x_4991_; size_t v___x_4992_; uint8_t v___x_4993_; 
v___x_4991_ = lean_ptr_addr(v_decl_4957_);
v___x_4992_ = lean_ptr_addr(v_fst_4960_);
v___x_4993_ = lean_usize_dec_eq(v___x_4991_, v___x_4992_);
if (v___x_4993_ == 0)
{
lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5003_; 
v_isSharedCheck_5003_ = !lean_is_exclusive(v_code_4921_);
if (v_isSharedCheck_5003_ == 0)
{
lean_object* v_unused_5004_; lean_object* v_unused_5005_; 
v_unused_5004_ = lean_ctor_get(v_code_4921_, 1);
lean_dec(v_unused_5004_);
v_unused_5005_ = lean_ctor_get(v_code_4921_, 0);
lean_dec(v_unused_5005_);
v___x_4995_ = v_code_4921_;
v_isShared_4996_ = v_isSharedCheck_5003_;
goto v_resetjp_4994_;
}
else
{
lean_dec(v_code_4921_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5003_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4998_; 
if (v_isShared_4996_ == 0)
{
lean_ctor_set(v___x_4995_, 1, v_a_4972_);
lean_ctor_set(v___x_4995_, 0, v_fst_4960_);
v___x_4998_ = v___x_4995_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_fst_4960_);
lean_ctor_set(v_reuseFailAlloc_5002_, 1, v_a_4972_);
v___x_4998_ = v_reuseFailAlloc_5002_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
lean_object* v___x_5000_; 
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 0, v___x_4998_);
v___x_5000_ = v___x_4974_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v___x_4998_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
}
}
else
{
lean_object* v___x_5007_; 
lean_dec(v_a_4972_);
lean_dec_ref(v_fst_4960_);
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 0, v_code_4921_);
v___x_5007_ = v___x_4974_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_code_4921_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
}
else
{
lean_dec_ref(v_fst_4960_);
lean_dec_ref_known(v_code_4921_, 2);
return v___x_4971_;
}
}
}
case 3:
{
lean_object* v_fvarId_5062_; lean_object* v_args_5063_; lean_object* v_jpLiveVarMap_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v_fvarId_5062_ = lean_ctor_get(v_code_4921_, 0);
v_args_5063_ = lean_ctor_get(v_code_4921_, 1);
lean_inc_ref(v_args_5063_);
v_jpLiveVarMap_5064_ = lean_ctor_get(v_a_4922_, 4);
v___x_5065_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(v_jpLiveVarMap_5064_, v_fvarId_5062_);
v___x_5066_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_5065_, v_a_4922_);
if (lean_obj_tag(v___x_5066_) == 0)
{
lean_object* v_a_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; uint8_t v___x_5070_; lean_object* v___x_5071_; 
v_a_5067_ = lean_ctor_get(v___x_5066_, 0);
lean_inc(v_a_5067_);
lean_dec_ref_known(v___x_5066_, 1);
v___x_5068_ = lean_st_ref_take(v_a_4923_);
lean_dec(v___x_5068_);
v___x_5069_ = lean_st_ref_put(v_a_4923_, v_a_5067_);
v___x_5070_ = 1;
v___x_5071_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_5070_, v_fvarId_5062_, v_a_4925_);
if (lean_obj_tag(v___x_5071_) == 0)
{
lean_object* v_a_5072_; lean_object* v___y_5074_; 
v_a_5072_ = lean_ctor_get(v___x_5071_, 0);
lean_inc(v_a_5072_);
lean_dec_ref_known(v___x_5071_, 1);
if (lean_obj_tag(v_a_5072_) == 0)
{
lean_object* v___x_5095_; lean_object* v___x_5096_; 
v___x_5095_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10);
v___x_5096_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5(v___x_5095_);
v___y_5074_ = v___x_5096_;
goto v___jp_5073_;
}
else
{
lean_object* v_val_5097_; 
v_val_5097_ = lean_ctor_get(v_a_5072_, 0);
lean_inc(v_val_5097_);
lean_dec_ref_known(v_a_5072_, 1);
v___y_5074_ = v_val_5097_;
goto v___jp_5073_;
}
v___jp_5073_:
{
lean_object* v_params_5075_; lean_object* v___x_5076_; 
v_params_5075_ = lean_ctor_get(v___y_5074_, 2);
lean_inc_ref(v_params_5075_);
lean_dec_ref(v___y_5074_);
v___x_5076_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_5063_, v_params_5075_, v_code_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v_a_5077_; lean_object* v___x_5078_; 
v_a_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_a_5077_);
lean_dec_ref_known(v___x_5076_, 1);
v___x_5078_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_5063_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
lean_dec_ref(v_args_5063_);
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5085_; 
v_isSharedCheck_5085_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5085_ == 0)
{
lean_object* v_unused_5086_; 
v_unused_5086_ = lean_ctor_get(v___x_5078_, 0);
lean_dec(v_unused_5086_);
v___x_5080_ = v___x_5078_;
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
else
{
lean_dec(v___x_5078_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5083_; 
if (v_isShared_5081_ == 0)
{
lean_ctor_set(v___x_5080_, 0, v_a_5077_);
v___x_5083_ = v___x_5080_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_a_5077_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
return v___x_5083_;
}
}
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5094_; 
lean_dec(v_a_5077_);
v_a_5087_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5089_ = v___x_5078_;
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5078_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5092_; 
if (v_isShared_5090_ == 0)
{
v___x_5092_ = v___x_5089_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
}
else
{
lean_dec_ref(v_args_5063_);
return v___x_5076_;
}
}
}
else
{
lean_object* v_a_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5105_; 
lean_dec_ref(v_args_5063_);
lean_dec_ref_known(v_code_4921_, 2);
v_a_5098_ = lean_ctor_get(v___x_5071_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5100_ = v___x_5071_;
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_a_5098_);
lean_dec(v___x_5071_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
lean_object* v___x_5103_; 
if (v_isShared_5101_ == 0)
{
v___x_5103_ = v___x_5100_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_a_5098_);
v___x_5103_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
return v___x_5103_;
}
}
}
}
else
{
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5113_; 
lean_dec_ref(v_args_5063_);
lean_dec_ref_known(v_code_4921_, 2);
v_a_5106_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5108_ = v___x_5066_;
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5066_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5111_; 
if (v_isShared_5109_ == 0)
{
v___x_5111_ = v___x_5108_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_a_5106_);
v___x_5111_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
return v___x_5111_;
}
}
}
}
case 4:
{
lean_object* v_cases_5114_; lean_object* v_typeName_5115_; lean_object* v_resultType_5116_; lean_object* v_discr_5117_; lean_object* v_alts_5118_; size_t v_sz_5119_; size_t v___x_5120_; lean_object* v___x_5121_; 
v_cases_5114_ = lean_ctor_get(v_code_4921_, 0);
v_typeName_5115_ = lean_ctor_get(v_cases_5114_, 0);
v_resultType_5116_ = lean_ctor_get(v_cases_5114_, 1);
v_discr_5117_ = lean_ctor_get(v_cases_5114_, 2);
v_alts_5118_ = lean_ctor_get(v_cases_5114_, 3);
v_sz_5119_ = lean_array_size(v_alts_5118_);
v___x_5120_ = ((size_t)0ULL);
lean_inc_ref(v_alts_5118_);
lean_inc_ref(v_cases_5114_);
v___x_5121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(v_cases_5114_, v_sz_5119_, v___x_5120_, v_alts_5118_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
if (lean_obj_tag(v___x_5121_) == 0)
{
lean_object* v_a_5122_; lean_object* v___y_5124_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; uint8_t v___x_5172_; 
v_a_5122_ = lean_ctor_get(v___x_5121_, 0);
lean_inc(v_a_5122_);
lean_dec_ref_known(v___x_5121_, 1);
v___x_5169_ = lean_unsigned_to_nat(0u);
v___x_5170_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5171_ = lean_array_get_size(v_a_5122_);
v___x_5172_ = lean_nat_dec_lt(v___x_5169_, v___x_5171_);
if (v___x_5172_ == 0)
{
v___y_5124_ = v___x_5170_;
goto v___jp_5123_;
}
else
{
uint8_t v___x_5173_; 
v___x_5173_ = lean_nat_dec_le(v___x_5171_, v___x_5171_);
if (v___x_5173_ == 0)
{
if (v___x_5172_ == 0)
{
v___y_5124_ = v___x_5170_;
goto v___jp_5123_;
}
else
{
size_t v___x_5174_; lean_object* v___x_5175_; 
v___x_5174_ = lean_usize_of_nat(v___x_5171_);
v___x_5175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_a_5122_, v___x_5120_, v___x_5174_, v___x_5170_);
v___y_5124_ = v___x_5175_;
goto v___jp_5123_;
}
}
else
{
size_t v___x_5176_; lean_object* v___x_5177_; 
v___x_5176_ = lean_usize_of_nat(v___x_5171_);
v___x_5177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_a_5122_, v___x_5120_, v___x_5176_, v___x_5170_);
v___y_5124_ = v___x_5177_;
goto v___jp_5123_;
}
}
v___jp_5123_:
{
lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
v___x_5125_ = lean_st_ref_take(v_a_4923_);
lean_dec(v___x_5125_);
v___x_5126_ = lean_st_ref_put(v_a_4923_, v___y_5124_);
lean_inc(v_discr_5117_);
v___x_5127_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_discr_5117_, v_a_4922_, v_a_4923_);
if (lean_obj_tag(v___x_5127_) == 0)
{
size_t v_sz_5128_; lean_object* v___x_5129_; 
lean_dec_ref_known(v___x_5127_, 1);
v_sz_5128_ = lean_array_size(v_a_5122_);
lean_inc(v_discr_5117_);
v___x_5129_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(v_discr_5117_, v_sz_5128_, v___x_5120_, v_a_5122_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5152_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5132_ = v___x_5129_;
v_isShared_5133_ = v_isSharedCheck_5152_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_a_5130_);
lean_dec(v___x_5129_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5152_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
size_t v___x_5134_; size_t v___x_5135_; uint8_t v___x_5136_; 
v___x_5134_ = lean_ptr_addr(v_alts_5118_);
v___x_5135_ = lean_ptr_addr(v_a_5130_);
v___x_5136_ = lean_usize_dec_eq(v___x_5134_, v___x_5135_);
if (v___x_5136_ == 0)
{
lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5147_; 
lean_inc(v_discr_5117_);
lean_inc_ref(v_resultType_5116_);
lean_inc(v_typeName_5115_);
v_isSharedCheck_5147_ = !lean_is_exclusive(v_code_4921_);
if (v_isSharedCheck_5147_ == 0)
{
lean_object* v_unused_5148_; 
v_unused_5148_ = lean_ctor_get(v_code_4921_, 0);
lean_dec(v_unused_5148_);
v___x_5138_ = v_code_4921_;
v_isShared_5139_ = v_isSharedCheck_5147_;
goto v_resetjp_5137_;
}
else
{
lean_dec(v_code_4921_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5147_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5140_; lean_object* v___x_5142_; 
v___x_5140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5140_, 0, v_typeName_5115_);
lean_ctor_set(v___x_5140_, 1, v_resultType_5116_);
lean_ctor_set(v___x_5140_, 2, v_discr_5117_);
lean_ctor_set(v___x_5140_, 3, v_a_5130_);
if (v_isShared_5139_ == 0)
{
lean_ctor_set(v___x_5138_, 0, v___x_5140_);
v___x_5142_ = v___x_5138_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v___x_5140_);
v___x_5142_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
lean_object* v___x_5144_; 
if (v_isShared_5133_ == 0)
{
lean_ctor_set(v___x_5132_, 0, v___x_5142_);
v___x_5144_ = v___x_5132_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5145_; 
v_reuseFailAlloc_5145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5145_, 0, v___x_5142_);
v___x_5144_ = v_reuseFailAlloc_5145_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
return v___x_5144_;
}
}
}
}
else
{
lean_object* v___x_5150_; 
lean_dec(v_a_5130_);
if (v_isShared_5133_ == 0)
{
lean_ctor_set(v___x_5132_, 0, v_code_4921_);
v___x_5150_ = v___x_5132_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_code_4921_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
}
else
{
lean_object* v_a_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5160_; 
lean_dec_ref_known(v_code_4921_, 1);
v_a_5153_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5155_ = v___x_5129_;
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_a_5153_);
lean_dec(v___x_5129_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
lean_object* v___x_5158_; 
if (v_isShared_5156_ == 0)
{
v___x_5158_ = v___x_5155_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v_a_5153_);
v___x_5158_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
return v___x_5158_;
}
}
}
}
else
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5168_; 
lean_dec(v_a_5122_);
lean_dec_ref_known(v_code_4921_, 1);
v_a_5161_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5163_ = v___x_5127_;
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v___x_5127_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5166_; 
if (v_isShared_5164_ == 0)
{
v___x_5166_ = v___x_5163_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5161_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
}
else
{
lean_object* v_a_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5185_; 
lean_dec_ref_known(v_code_4921_, 1);
v_a_5178_ = lean_ctor_get(v___x_5121_, 0);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5121_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5180_ = v___x_5121_;
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_a_5178_);
lean_dec(v___x_5121_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5183_; 
if (v_isShared_5181_ == 0)
{
v___x_5183_ = v___x_5180_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5178_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
return v___x_5183_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
v_fvarId_5186_ = lean_ctor_get(v_code_4921_, 0);
v___x_5187_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5188_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_5187_, v_a_4922_);
if (lean_obj_tag(v___x_5188_) == 0)
{
lean_object* v_a_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v_varMap_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; 
v_a_5189_ = lean_ctor_get(v___x_5188_, 0);
lean_inc(v_a_5189_);
lean_dec_ref_known(v___x_5188_, 1);
v___x_5190_ = lean_st_ref_take(v_a_4923_);
lean_dec(v___x_5190_);
v___x_5191_ = lean_st_ref_put(v_a_4923_, v_a_5189_);
v_varMap_5192_ = lean_ctor_get(v_a_4922_, 3);
v___x_5193_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_5192_, v_fvarId_5186_);
lean_inc(v_fvarId_5186_);
v___x_5194_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_5186_, v_a_4922_, v_a_4923_);
if (lean_obj_tag(v___x_5194_) == 0)
{
lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5218_; 
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5194_);
if (v_isSharedCheck_5218_ == 0)
{
lean_object* v_unused_5219_; 
v_unused_5219_ = lean_ctor_get(v___x_5194_, 0);
lean_dec(v_unused_5219_);
v___x_5196_ = v___x_5194_;
v_isShared_5197_ = v_isSharedCheck_5218_;
goto v_resetjp_5195_;
}
else
{
lean_dec(v___x_5194_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5218_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5198_; uint8_t v_isPossibleRef_5199_; 
v___x_5198_ = lean_st_ref_get(v_a_4923_);
v_isPossibleRef_5199_ = lean_ctor_get_uint8(v___x_5193_, sizeof(void*)*2);
if (v_isPossibleRef_5199_ == 0)
{
lean_object* v___x_5201_; 
lean_dec(v___x_5198_);
lean_dec_ref(v___x_5193_);
if (v_isShared_5197_ == 0)
{
lean_ctor_set(v___x_5196_, 0, v_code_4921_);
v___x_5201_ = v___x_5196_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_code_4921_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
else
{
uint8_t v_isDefiniteRef_5203_; uint8_t v_persistent_5204_; lean_object* v_borrows_5205_; uint8_t v___x_5206_; 
v_isDefiniteRef_5203_ = lean_ctor_get_uint8(v___x_5193_, sizeof(void*)*2 + 1);
v_persistent_5204_ = lean_ctor_get_uint8(v___x_5193_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_5193_);
v_borrows_5205_ = lean_ctor_get(v___x_5198_, 1);
lean_inc_ref(v_borrows_5205_);
lean_dec(v___x_5198_);
v___x_5206_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_5205_, v_fvarId_5186_);
lean_dec_ref(v_borrows_5205_);
if (v___x_5206_ == 0)
{
lean_object* v___x_5208_; 
if (v_isShared_5197_ == 0)
{
lean_ctor_set(v___x_5196_, 0, v_code_4921_);
v___x_5208_ = v___x_5196_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_code_4921_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
else
{
lean_object* v___x_5210_; uint8_t v___y_5212_; 
lean_inc(v_fvarId_5186_);
v___x_5210_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_5203_ == 0)
{
v___y_5212_ = v___x_5206_;
goto v___jp_5211_;
}
else
{
uint8_t v___x_5217_; 
v___x_5217_ = 0;
v___y_5212_ = v___x_5217_;
goto v___jp_5211_;
}
v___jp_5211_:
{
lean_object* v___x_5213_; lean_object* v___x_5215_; 
v___x_5213_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_5213_, 0, v_fvarId_5186_);
lean_ctor_set(v___x_5213_, 1, v___x_5210_);
lean_ctor_set(v___x_5213_, 2, v_code_4921_);
lean_ctor_set_uint8(v___x_5213_, sizeof(void*)*3, v___y_5212_);
lean_ctor_set_uint8(v___x_5213_, sizeof(void*)*3 + 1, v_persistent_5204_);
if (v_isShared_5197_ == 0)
{
lean_ctor_set(v___x_5196_, 0, v___x_5213_);
v___x_5215_ = v___x_5196_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v___x_5213_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
}
}
}
else
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5227_; 
lean_dec_ref(v___x_5193_);
lean_dec_ref_known(v_code_4921_, 1);
v_a_5220_ = lean_ctor_get(v___x_5194_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5194_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5222_ = v___x_5194_;
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v___x_5194_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5225_; 
if (v_isShared_5223_ == 0)
{
v___x_5225_ = v___x_5222_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_a_5220_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
}
}
else
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
lean_dec_ref_known(v_code_4921_, 1);
v_a_5228_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5230_ = v___x_5188_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5188_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5233_; 
if (v_isShared_5231_ == 0)
{
v___x_5233_ = v___x_5230_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_a_5228_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
}
case 6:
{
lean_object* v___x_5236_; lean_object* v___x_5237_; 
v___x_5236_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5237_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_5236_, v_a_4922_);
if (lean_obj_tag(v___x_5237_) == 0)
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5247_; 
v_a_5238_ = lean_ctor_get(v___x_5237_, 0);
v_isSharedCheck_5247_ = !lean_is_exclusive(v___x_5237_);
if (v_isSharedCheck_5247_ == 0)
{
v___x_5240_ = v___x_5237_;
v_isShared_5241_ = v_isSharedCheck_5247_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5237_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5247_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5245_; 
v___x_5242_ = lean_st_ref_take(v_a_4923_);
lean_dec(v___x_5242_);
v___x_5243_ = lean_st_ref_put(v_a_4923_, v_a_5238_);
if (v_isShared_5241_ == 0)
{
lean_ctor_set(v___x_5240_, 0, v_code_4921_);
v___x_5245_ = v___x_5240_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_code_4921_);
v___x_5245_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
return v___x_5245_;
}
}
}
else
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5255_; 
lean_dec_ref_known(v_code_4921_, 1);
v_a_5248_ = lean_ctor_get(v___x_5237_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5237_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5250_ = v___x_5237_;
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v___x_5237_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5251_ == 0)
{
v___x_5253_ = v___x_5250_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
}
case 8:
{
lean_object* v_fvarId_5256_; lean_object* v_i_5257_; lean_object* v_y_5258_; lean_object* v_k_5259_; lean_object* v___x_5260_; 
v_fvarId_5256_ = lean_ctor_get(v_code_4921_, 0);
v_i_5257_ = lean_ctor_get(v_code_4921_, 1);
v_y_5258_ = lean_ctor_get(v_code_4921_, 2);
v_k_5259_ = lean_ctor_get(v_code_4921_, 3);
lean_inc_ref(v_k_5259_);
v___x_5260_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5259_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
if (lean_obj_tag(v___x_5260_) == 0)
{
lean_object* v_a_5261_; lean_object* v___x_5262_; 
v_a_5261_ = lean_ctor_get(v___x_5260_, 0);
lean_inc(v_a_5261_);
lean_dec_ref_known(v___x_5260_, 1);
lean_inc(v_fvarId_5256_);
v___x_5262_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_5256_, v_a_4922_, v_a_4923_);
if (lean_obj_tag(v___x_5262_) == 0)
{
lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5286_; 
v_isSharedCheck_5286_ = !lean_is_exclusive(v___x_5262_);
if (v_isSharedCheck_5286_ == 0)
{
lean_object* v_unused_5287_; 
v_unused_5287_ = lean_ctor_get(v___x_5262_, 0);
lean_dec(v_unused_5287_);
v___x_5264_ = v___x_5262_;
v_isShared_5265_ = v_isSharedCheck_5286_;
goto v_resetjp_5263_;
}
else
{
lean_dec(v___x_5262_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5286_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
size_t v___x_5266_; size_t v___x_5267_; uint8_t v___x_5268_; 
v___x_5266_ = lean_ptr_addr(v_k_5259_);
v___x_5267_ = lean_ptr_addr(v_a_5261_);
v___x_5268_ = lean_usize_dec_eq(v___x_5266_, v___x_5267_);
if (v___x_5268_ == 0)
{
lean_object* v___x_5270_; uint8_t v_isShared_5271_; uint8_t v_isSharedCheck_5278_; 
lean_inc(v_y_5258_);
lean_inc(v_i_5257_);
lean_inc(v_fvarId_5256_);
v_isSharedCheck_5278_ = !lean_is_exclusive(v_code_4921_);
if (v_isSharedCheck_5278_ == 0)
{
lean_object* v_unused_5279_; lean_object* v_unused_5280_; lean_object* v_unused_5281_; lean_object* v_unused_5282_; 
v_unused_5279_ = lean_ctor_get(v_code_4921_, 3);
lean_dec(v_unused_5279_);
v_unused_5280_ = lean_ctor_get(v_code_4921_, 2);
lean_dec(v_unused_5280_);
v_unused_5281_ = lean_ctor_get(v_code_4921_, 1);
lean_dec(v_unused_5281_);
v_unused_5282_ = lean_ctor_get(v_code_4921_, 0);
lean_dec(v_unused_5282_);
v___x_5270_ = v_code_4921_;
v_isShared_5271_ = v_isSharedCheck_5278_;
goto v_resetjp_5269_;
}
else
{
lean_dec(v_code_4921_);
v___x_5270_ = lean_box(0);
v_isShared_5271_ = v_isSharedCheck_5278_;
goto v_resetjp_5269_;
}
v_resetjp_5269_:
{
lean_object* v___x_5273_; 
if (v_isShared_5271_ == 0)
{
lean_ctor_set(v___x_5270_, 3, v_a_5261_);
v___x_5273_ = v___x_5270_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5277_; 
v_reuseFailAlloc_5277_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5277_, 0, v_fvarId_5256_);
lean_ctor_set(v_reuseFailAlloc_5277_, 1, v_i_5257_);
lean_ctor_set(v_reuseFailAlloc_5277_, 2, v_y_5258_);
lean_ctor_set(v_reuseFailAlloc_5277_, 3, v_a_5261_);
v___x_5273_ = v_reuseFailAlloc_5277_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
lean_object* v___x_5275_; 
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 0, v___x_5273_);
v___x_5275_ = v___x_5264_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v___x_5273_);
v___x_5275_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
return v___x_5275_;
}
}
}
}
else
{
lean_object* v___x_5284_; 
lean_dec(v_a_5261_);
if (v_isShared_5265_ == 0)
{
lean_ctor_set(v___x_5264_, 0, v_code_4921_);
v___x_5284_ = v___x_5264_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_code_4921_);
v___x_5284_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
return v___x_5284_;
}
}
}
}
else
{
lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5295_; 
lean_dec(v_a_5261_);
lean_dec_ref_known(v_code_4921_, 4);
v_a_5288_ = lean_ctor_get(v___x_5262_, 0);
v_isSharedCheck_5295_ = !lean_is_exclusive(v___x_5262_);
if (v_isSharedCheck_5295_ == 0)
{
v___x_5290_ = v___x_5262_;
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___x_5262_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5293_; 
if (v_isShared_5291_ == 0)
{
v___x_5293_ = v___x_5290_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_a_5288_);
v___x_5293_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
return v___x_5293_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_4921_, 4);
return v___x_5260_;
}
}
case 9:
{
lean_object* v_fvarId_5296_; lean_object* v_i_5297_; lean_object* v_offset_5298_; lean_object* v_y_5299_; lean_object* v_ty_5300_; lean_object* v_k_5301_; lean_object* v___x_5302_; 
v_fvarId_5296_ = lean_ctor_get(v_code_4921_, 0);
v_i_5297_ = lean_ctor_get(v_code_4921_, 1);
v_offset_5298_ = lean_ctor_get(v_code_4921_, 2);
v_y_5299_ = lean_ctor_get(v_code_4921_, 3);
v_ty_5300_ = lean_ctor_get(v_code_4921_, 4);
v_k_5301_ = lean_ctor_get(v_code_4921_, 5);
lean_inc_ref(v_k_5301_);
v___x_5302_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5301_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
if (lean_obj_tag(v___x_5302_) == 0)
{
lean_object* v_a_5303_; lean_object* v___x_5304_; 
v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
lean_inc(v_a_5303_);
lean_dec_ref_known(v___x_5302_, 1);
lean_inc(v_fvarId_5296_);
v___x_5304_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_5296_, v_a_4922_, v_a_4923_);
if (lean_obj_tag(v___x_5304_) == 0)
{
lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5330_; 
v_isSharedCheck_5330_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5330_ == 0)
{
lean_object* v_unused_5331_; 
v_unused_5331_ = lean_ctor_get(v___x_5304_, 0);
lean_dec(v_unused_5331_);
v___x_5306_ = v___x_5304_;
v_isShared_5307_ = v_isSharedCheck_5330_;
goto v_resetjp_5305_;
}
else
{
lean_dec(v___x_5304_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5330_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
size_t v___x_5308_; size_t v___x_5309_; uint8_t v___x_5310_; 
v___x_5308_ = lean_ptr_addr(v_k_5301_);
v___x_5309_ = lean_ptr_addr(v_a_5303_);
v___x_5310_ = lean_usize_dec_eq(v___x_5308_, v___x_5309_);
if (v___x_5310_ == 0)
{
lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5320_; 
lean_inc_ref(v_ty_5300_);
lean_inc(v_y_5299_);
lean_inc(v_offset_5298_);
lean_inc(v_i_5297_);
lean_inc(v_fvarId_5296_);
v_isSharedCheck_5320_ = !lean_is_exclusive(v_code_4921_);
if (v_isSharedCheck_5320_ == 0)
{
lean_object* v_unused_5321_; lean_object* v_unused_5322_; lean_object* v_unused_5323_; lean_object* v_unused_5324_; lean_object* v_unused_5325_; lean_object* v_unused_5326_; 
v_unused_5321_ = lean_ctor_get(v_code_4921_, 5);
lean_dec(v_unused_5321_);
v_unused_5322_ = lean_ctor_get(v_code_4921_, 4);
lean_dec(v_unused_5322_);
v_unused_5323_ = lean_ctor_get(v_code_4921_, 3);
lean_dec(v_unused_5323_);
v_unused_5324_ = lean_ctor_get(v_code_4921_, 2);
lean_dec(v_unused_5324_);
v_unused_5325_ = lean_ctor_get(v_code_4921_, 1);
lean_dec(v_unused_5325_);
v_unused_5326_ = lean_ctor_get(v_code_4921_, 0);
lean_dec(v_unused_5326_);
v___x_5312_ = v_code_4921_;
v_isShared_5313_ = v_isSharedCheck_5320_;
goto v_resetjp_5311_;
}
else
{
lean_dec(v_code_4921_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5320_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v___x_5315_; 
if (v_isShared_5313_ == 0)
{
lean_ctor_set(v___x_5312_, 5, v_a_5303_);
v___x_5315_ = v___x_5312_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v_fvarId_5296_);
lean_ctor_set(v_reuseFailAlloc_5319_, 1, v_i_5297_);
lean_ctor_set(v_reuseFailAlloc_5319_, 2, v_offset_5298_);
lean_ctor_set(v_reuseFailAlloc_5319_, 3, v_y_5299_);
lean_ctor_set(v_reuseFailAlloc_5319_, 4, v_ty_5300_);
lean_ctor_set(v_reuseFailAlloc_5319_, 5, v_a_5303_);
v___x_5315_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
lean_object* v___x_5317_; 
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 0, v___x_5315_);
v___x_5317_ = v___x_5306_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v___x_5315_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
}
else
{
lean_object* v___x_5328_; 
lean_dec(v_a_5303_);
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 0, v_code_4921_);
v___x_5328_ = v___x_5306_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_code_4921_);
v___x_5328_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
return v___x_5328_;
}
}
}
}
else
{
lean_object* v_a_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5339_; 
lean_dec(v_a_5303_);
lean_dec_ref_known(v_code_4921_, 6);
v_a_5332_ = lean_ctor_get(v___x_5304_, 0);
v_isSharedCheck_5339_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5339_ == 0)
{
v___x_5334_ = v___x_5304_;
v_isShared_5335_ = v_isSharedCheck_5339_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_a_5332_);
lean_dec(v___x_5304_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5339_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
lean_object* v___x_5337_; 
if (v_isShared_5335_ == 0)
{
v___x_5337_ = v___x_5334_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5338_; 
v_reuseFailAlloc_5338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5338_, 0, v_a_5332_);
v___x_5337_ = v_reuseFailAlloc_5338_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
return v___x_5337_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_4921_, 6);
return v___x_5302_;
}
}
default: 
{
lean_object* v___x_5340_; lean_object* v___x_5341_; 
lean_dec_ref(v_code_4921_);
v___x_5340_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1);
v___x_5341_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v___x_5340_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
return v___x_5341_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(lean_object* v_cases_5342_, size_t v_sz_5343_, size_t v_i_5344_, lean_object* v_bs_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_){
_start:
{
uint8_t v___x_5353_; 
v___x_5353_ = lean_usize_dec_lt(v_i_5344_, v_sz_5343_);
if (v___x_5353_ == 0)
{
lean_object* v___x_5354_; 
lean_dec_ref(v_cases_5342_);
v___x_5354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5354_, 0, v_bs_5345_);
return v___x_5354_;
}
else
{
lean_object* v_v_5355_; lean_object* v___x_5356_; lean_object* v_bs_x27_5357_; lean_object* v___x_5358_; lean_object* v_a_5360_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; 
v_v_5355_ = lean_array_uget(v_bs_5345_, v_i_5344_);
v___x_5356_ = lean_unsigned_to_nat(0u);
v_bs_x27_5357_ = lean_array_uset(v_bs_5345_, v_i_5344_, v___x_5356_);
v___x_5358_ = lean_st_ref_get(v___y_5347_);
v___x_5369_ = lean_st_ref_take(v___y_5347_);
lean_dec(v___x_5369_);
v___x_5370_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5371_ = lean_st_ref_put(v___y_5347_, v___x_5370_);
if (lean_obj_tag(v_v_5355_) == 1)
{
lean_object* v_info_5372_; lean_object* v_code_5373_; lean_object* v_discr_5374_; lean_object* v_resetTargets_5375_; lean_object* v_unconditionalBorrows_5376_; lean_object* v_derivedValMap_5377_; lean_object* v_varMap_5378_; lean_object* v_jpLiveVarMap_5379_; lean_object* v_idx_5380_; lean_object* v___y_5382_; lean_object* v___x_5397_; 
v_info_5372_ = lean_ctor_get(v_v_5355_, 0);
v_code_5373_ = lean_ctor_get(v_v_5355_, 1);
v_discr_5374_ = lean_ctor_get(v_cases_5342_, 2);
v_resetTargets_5375_ = lean_ctor_get(v___y_5346_, 0);
v_unconditionalBorrows_5376_ = lean_ctor_get(v___y_5346_, 1);
v_derivedValMap_5377_ = lean_ctor_get(v___y_5346_, 2);
v_varMap_5378_ = lean_ctor_get(v___y_5346_, 3);
v_jpLiveVarMap_5379_ = lean_ctor_get(v___y_5346_, 4);
v_idx_5380_ = lean_ctor_get(v___y_5346_, 5);
v___x_5397_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_varMap_5378_, v_discr_5374_);
if (lean_obj_tag(v___x_5397_) == 0)
{
lean_inc(v_varMap_5378_);
v___y_5382_ = v_varMap_5378_;
goto v___jp_5381_;
}
else
{
lean_object* v_val_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5419_; 
v_val_5398_ = lean_ctor_get(v___x_5397_, 0);
v_isSharedCheck_5419_ = !lean_is_exclusive(v___x_5397_);
if (v_isSharedCheck_5419_ == 0)
{
v___x_5400_ = v___x_5397_;
v_isShared_5401_ = v_isSharedCheck_5419_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_val_5398_);
lean_dec(v___x_5397_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5419_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
uint8_t v_persistent_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5416_; 
v_persistent_5402_ = lean_ctor_get_uint8(v_val_5398_, sizeof(void*)*2 + 2);
v_isSharedCheck_5416_ = !lean_is_exclusive(v_val_5398_);
if (v_isSharedCheck_5416_ == 0)
{
lean_object* v_unused_5417_; lean_object* v_unused_5418_; 
v_unused_5417_ = lean_ctor_get(v_val_5398_, 1);
lean_dec(v_unused_5417_);
v_unused_5418_ = lean_ctor_get(v_val_5398_, 0);
lean_dec(v_unused_5418_);
v___x_5404_ = v_val_5398_;
v_isShared_5405_ = v_isSharedCheck_5416_;
goto v_resetjp_5403_;
}
else
{
lean_dec(v_val_5398_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5416_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
uint8_t v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5410_; 
v___x_5406_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_info_5372_);
v___x_5407_ = lean_unsigned_to_nat(1u);
v___x_5408_ = lean_nat_add(v_idx_5380_, v___x_5407_);
lean_inc_ref(v_info_5372_);
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 0, v_info_5372_);
v___x_5410_ = v___x_5400_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_info_5372_);
v___x_5410_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
lean_object* v___x_5412_; 
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 1, v___x_5410_);
lean_ctor_set(v___x_5404_, 0, v___x_5408_);
v___x_5412_ = v___x_5404_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v___x_5408_);
lean_ctor_set(v_reuseFailAlloc_5414_, 1, v___x_5410_);
lean_ctor_set_uint8(v_reuseFailAlloc_5414_, sizeof(void*)*2 + 2, v_persistent_5402_);
v___x_5412_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
lean_object* v___x_5413_; 
lean_ctor_set_uint8(v___x_5412_, sizeof(void*)*2, v___x_5406_);
lean_ctor_set_uint8(v___x_5412_, sizeof(void*)*2 + 1, v___x_5406_);
lean_inc(v_varMap_5378_);
lean_inc(v_discr_5374_);
v___x_5413_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_5374_, v___x_5412_, v_varMap_5378_);
v___y_5382_ = v___x_5413_;
goto v___jp_5381_;
}
}
}
}
}
v___jp_5381_:
{
lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; 
v___x_5383_ = lean_unsigned_to_nat(1u);
v___x_5384_ = lean_nat_add(v_idx_5380_, v___x_5383_);
lean_inc(v_jpLiveVarMap_5379_);
lean_inc(v_derivedValMap_5377_);
lean_inc(v_unconditionalBorrows_5376_);
lean_inc_ref(v_resetTargets_5375_);
v___x_5385_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5385_, 0, v_resetTargets_5375_);
lean_ctor_set(v___x_5385_, 1, v_unconditionalBorrows_5376_);
lean_ctor_set(v___x_5385_, 2, v_derivedValMap_5377_);
lean_ctor_set(v___x_5385_, 3, v___y_5382_);
lean_ctor_set(v___x_5385_, 4, v_jpLiveVarMap_5379_);
lean_ctor_set(v___x_5385_, 5, v___x_5384_);
lean_inc_ref(v_code_5373_);
v___x_5386_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5373_, v___x_5385_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
lean_dec_ref_known(v___x_5385_, 6);
if (lean_obj_tag(v___x_5386_) == 0)
{
lean_object* v_a_5387_; lean_object* v___x_5388_; 
v_a_5387_ = lean_ctor_get(v___x_5386_, 0);
lean_inc(v_a_5387_);
lean_dec_ref_known(v___x_5386_, 1);
v___x_5388_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_5355_, v_a_5387_);
v_a_5360_ = v___x_5388_;
goto v___jp_5359_;
}
else
{
lean_object* v_a_5389_; lean_object* v___x_5391_; uint8_t v_isShared_5392_; uint8_t v_isSharedCheck_5396_; 
lean_dec_ref_known(v_v_5355_, 2);
lean_dec(v___x_5358_);
lean_dec_ref(v_bs_x27_5357_);
lean_dec_ref(v_cases_5342_);
v_a_5389_ = lean_ctor_get(v___x_5386_, 0);
v_isSharedCheck_5396_ = !lean_is_exclusive(v___x_5386_);
if (v_isSharedCheck_5396_ == 0)
{
v___x_5391_ = v___x_5386_;
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
else
{
lean_inc(v_a_5389_);
lean_dec(v___x_5386_);
v___x_5391_ = lean_box(0);
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
v_resetjp_5390_:
{
lean_object* v___x_5394_; 
if (v_isShared_5392_ == 0)
{
v___x_5394_ = v___x_5391_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_a_5389_);
v___x_5394_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
return v___x_5394_;
}
}
}
}
}
else
{
lean_object* v_code_5420_; lean_object* v___x_5421_; 
v_code_5420_ = lean_ctor_get(v_v_5355_, 0);
lean_inc_ref(v_code_5420_);
v___x_5421_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5420_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5421_) == 0)
{
lean_object* v_a_5422_; lean_object* v___x_5423_; 
v_a_5422_ = lean_ctor_get(v___x_5421_, 0);
lean_inc(v_a_5422_);
lean_dec_ref_known(v___x_5421_, 1);
v___x_5423_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_5355_, v_a_5422_);
v_a_5360_ = v___x_5423_;
goto v___jp_5359_;
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
lean_dec_ref_known(v_v_5355_, 1);
lean_dec(v___x_5358_);
lean_dec_ref(v_bs_x27_5357_);
lean_dec_ref(v_cases_5342_);
v_a_5424_ = lean_ctor_get(v___x_5421_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5421_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___x_5421_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5421_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
v___x_5429_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
return v___x_5429_;
}
}
}
}
v___jp_5359_:
{
lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; size_t v___x_5365_; size_t v___x_5366_; lean_object* v___x_5367_; 
v___x_5361_ = lean_st_ref_get(v___y_5347_);
v___x_5362_ = lean_st_ref_take(v___y_5347_);
lean_dec(v___x_5362_);
v___x_5363_ = lean_st_ref_put(v___y_5347_, v___x_5358_);
v___x_5364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5364_, 0, v_a_5360_);
lean_ctor_set(v___x_5364_, 1, v___x_5361_);
v___x_5365_ = ((size_t)1ULL);
v___x_5366_ = lean_usize_add(v_i_5344_, v___x_5365_);
v___x_5367_ = lean_array_uset(v_bs_x27_5357_, v_i_5344_, v___x_5364_);
v_i_5344_ = v___x_5366_;
v_bs_5345_ = v___x_5367_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6___boxed(lean_object* v_cases_5432_, lean_object* v_sz_5433_, lean_object* v_i_5434_, lean_object* v_bs_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_){
_start:
{
size_t v_sz_boxed_5443_; size_t v_i_boxed_5444_; lean_object* v_res_5445_; 
v_sz_boxed_5443_ = lean_unbox_usize(v_sz_5433_);
lean_dec(v_sz_5433_);
v_i_boxed_5444_ = lean_unbox_usize(v_i_5434_);
lean_dec(v_i_5434_);
v_res_5445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(v_cases_5432_, v_sz_boxed_5443_, v_i_boxed_5444_, v_bs_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_);
lean_dec(v___y_5441_);
lean_dec_ref(v___y_5440_);
lean_dec(v___y_5439_);
lean_dec_ref(v___y_5438_);
lean_dec(v___y_5437_);
lean_dec_ref(v___y_5436_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___boxed(lean_object* v_code_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_){
_start:
{
lean_object* v_res_5454_; 
v_res_5454_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_, v_a_5452_);
lean_dec(v_a_5452_);
lean_dec_ref(v_a_5451_);
lean_dec(v_a_5450_);
lean_dec_ref(v_a_5449_);
lean_dec(v_a_5448_);
lean_dec_ref(v_a_5447_);
return v_res_5454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1(lean_object* v_00_u03b2_5455_, lean_object* v_m_5456_, lean_object* v_a_5457_, lean_object* v_b_5458_){
_start:
{
lean_object* v___x_5459_; 
v___x_5459_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(v_m_5456_, v_a_5457_, v_b_5458_);
return v___x_5459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_5460_, lean_object* v_a_5461_, lean_object* v_b_5462_, lean_object* v_x_5463_){
_start:
{
lean_object* v___x_5464_; 
v___x_5464_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(v_a_5461_, v_b_5462_, v_x_5463_);
return v___x_5464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(lean_object* v_decl_5465_, lean_object* v_code_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_){
_start:
{
lean_object* v_toSignature_5474_; lean_object* v_params_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; uint8_t v___x_5478_; 
v_toSignature_5474_ = lean_ctor_get(v_decl_5465_, 0);
v_params_5475_ = lean_ctor_get(v_toSignature_5474_, 3);
v___x_5476_ = lean_unsigned_to_nat(0u);
v___x_5477_ = lean_array_get_size(v_params_5475_);
v___x_5478_ = lean_nat_dec_lt(v___x_5476_, v___x_5477_);
if (v___x_5478_ == 0)
{
lean_object* v___x_5479_; 
v___x_5479_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_);
if (lean_obj_tag(v___x_5479_) == 0)
{
lean_object* v_a_5480_; lean_object* v___x_5481_; 
v_a_5480_ = lean_ctor_get(v___x_5479_, 0);
lean_inc(v_a_5480_);
lean_dec_ref_known(v___x_5479_, 1);
v___x_5481_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5475_, v_a_5480_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_);
return v___x_5481_;
}
else
{
return v___x_5479_;
}
}
else
{
size_t v___x_5482_; size_t v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; 
v___x_5482_ = ((size_t)0ULL);
v___x_5483_ = lean_usize_of_nat(v___x_5477_);
lean_inc_ref(v_a_5467_);
v___x_5484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_params_5475_, v___x_5482_, v___x_5483_, v_a_5467_);
v___x_5485_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5466_, v___x_5484_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v_a_5486_; lean_object* v___x_5487_; 
v_a_5486_ = lean_ctor_get(v___x_5485_, 0);
lean_inc(v_a_5486_);
lean_dec_ref_known(v___x_5485_, 1);
v___x_5487_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5475_, v_a_5486_, v___x_5484_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_);
lean_dec_ref(v___x_5484_);
return v___x_5487_;
}
else
{
lean_dec_ref(v___x_5484_);
return v___x_5485_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go___boxed(lean_object* v_decl_5488_, lean_object* v_code_5489_, lean_object* v_a_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_){
_start:
{
lean_object* v_res_5497_; 
v_res_5497_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(v_decl_5488_, v_code_5489_, v_a_5490_, v_a_5491_, v_a_5492_, v_a_5493_, v_a_5494_, v_a_5495_);
lean_dec(v_a_5495_);
lean_dec_ref(v_a_5494_);
lean_dec(v_a_5493_);
lean_dec_ref(v_a_5492_);
lean_dec(v_a_5491_);
lean_dec_ref(v_a_5490_);
lean_dec_ref(v_decl_5488_);
return v_res_5497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(lean_object* v_f_5498_, lean_object* v_v_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_){
_start:
{
if (lean_obj_tag(v_v_5499_) == 0)
{
lean_object* v_code_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5529_; 
v_code_5505_ = lean_ctor_get(v_v_5499_, 0);
v_isSharedCheck_5529_ = !lean_is_exclusive(v_v_5499_);
if (v_isSharedCheck_5529_ == 0)
{
v___x_5507_ = v_v_5499_;
v_isShared_5508_ = v_isSharedCheck_5529_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_code_5505_);
lean_dec(v_v_5499_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5529_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5509_; 
lean_inc(v___y_5503_);
lean_inc_ref(v___y_5502_);
lean_inc(v___y_5501_);
lean_inc_ref(v___y_5500_);
v___x_5509_ = lean_apply_6(v_f_5498_, v_code_5505_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, lean_box(0));
if (lean_obj_tag(v___x_5509_) == 0)
{
lean_object* v_a_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5520_; 
v_a_5510_ = lean_ctor_get(v___x_5509_, 0);
v_isSharedCheck_5520_ = !lean_is_exclusive(v___x_5509_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5512_ = v___x_5509_;
v_isShared_5513_ = v_isSharedCheck_5520_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_a_5510_);
lean_dec(v___x_5509_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5520_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5515_; 
if (v_isShared_5508_ == 0)
{
lean_ctor_set(v___x_5507_, 0, v_a_5510_);
v___x_5515_ = v___x_5507_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5510_);
v___x_5515_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
lean_object* v___x_5517_; 
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 0, v___x_5515_);
v___x_5517_ = v___x_5512_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5515_);
v___x_5517_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
return v___x_5517_;
}
}
}
}
else
{
lean_object* v_a_5521_; lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5528_; 
lean_del_object(v___x_5507_);
v_a_5521_ = lean_ctor_get(v___x_5509_, 0);
v_isSharedCheck_5528_ = !lean_is_exclusive(v___x_5509_);
if (v_isSharedCheck_5528_ == 0)
{
v___x_5523_ = v___x_5509_;
v_isShared_5524_ = v_isSharedCheck_5528_;
goto v_resetjp_5522_;
}
else
{
lean_inc(v_a_5521_);
lean_dec(v___x_5509_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5528_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v___x_5526_; 
if (v_isShared_5524_ == 0)
{
v___x_5526_ = v___x_5523_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_a_5521_);
v___x_5526_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
return v___x_5526_;
}
}
}
}
}
else
{
lean_object* v___x_5530_; 
lean_dec_ref(v_f_5498_);
v___x_5530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5530_, 0, v_v_5499_);
return v___x_5530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg___boxed(lean_object* v_f_5531_, lean_object* v_v_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_){
_start:
{
lean_object* v_res_5538_; 
v_res_5538_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v_f_5531_, v_v_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_);
lean_dec(v___y_5536_);
lean_dec_ref(v___y_5535_);
lean_dec(v___y_5534_);
lean_dec_ref(v___y_5533_);
return v_res_5538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(uint8_t v_pu_5539_, lean_object* v_f_5540_, lean_object* v_v_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_){
_start:
{
lean_object* v___x_5547_; 
v___x_5547_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v_f_5540_, v_v_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_);
return v___x_5547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___boxed(lean_object* v_pu_5548_, lean_object* v_f_5549_, lean_object* v_v_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_){
_start:
{
uint8_t v_pu_boxed_5556_; lean_object* v_res_5557_; 
v_pu_boxed_5556_ = lean_unbox(v_pu_5548_);
v_res_5557_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(v_pu_boxed_5556_, v_f_5549_, v_v_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_);
lean_dec(v___y_5554_);
lean_dec_ref(v___y_5553_);
lean_dec(v___y_5552_);
lean_dec_ref(v___y_5551_);
return v_res_5557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(lean_object* v_decl_5558_, lean_object* v_code_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_){
_start:
{
lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; 
lean_inc_ref(v_code_5559_);
v___x_5565_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets(v_code_5559_);
v___x_5566_ = lean_box(0);
v___x_5567_ = lean_box(1);
v___x_5568_ = lean_unsigned_to_nat(0u);
v___x_5569_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5569_, 0, v___x_5565_);
lean_ctor_set(v___x_5569_, 1, v___x_5566_);
lean_ctor_set(v___x_5569_, 2, v___x_5567_);
lean_ctor_set(v___x_5569_, 3, v___x_5567_);
lean_ctor_set(v___x_5569_, 4, v___x_5567_);
lean_ctor_set(v___x_5569_, 5, v___x_5568_);
v___x_5570_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5571_ = lean_st_mk_ref(v___x_5570_);
v___x_5572_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(v_decl_5558_, v_code_5559_, v___x_5569_, v___x_5571_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_);
lean_dec_ref_known(v___x_5569_, 6);
if (lean_obj_tag(v___x_5572_) == 0)
{
lean_object* v_a_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5581_; 
v_a_5573_ = lean_ctor_get(v___x_5572_, 0);
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5581_ == 0)
{
v___x_5575_ = v___x_5572_;
v_isShared_5576_ = v_isSharedCheck_5581_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_a_5573_);
lean_dec(v___x_5572_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5581_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___x_5577_; lean_object* v___x_5579_; 
v___x_5577_ = lean_st_ref_get(v___x_5571_);
lean_dec(v___x_5571_);
lean_dec(v___x_5577_);
if (v_isShared_5576_ == 0)
{
v___x_5579_ = v___x_5575_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5573_);
v___x_5579_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
return v___x_5579_;
}
}
}
else
{
lean_dec(v___x_5571_);
return v___x_5572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0___boxed(lean_object* v_decl_5582_, lean_object* v_code_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_){
_start:
{
lean_object* v_res_5589_; 
v_res_5589_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(v_decl_5582_, v_code_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_);
lean_dec(v___y_5587_);
lean_dec_ref(v___y_5586_);
lean_dec(v___y_5585_);
lean_dec_ref(v___y_5584_);
lean_dec_ref(v_decl_5582_);
return v_res_5589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(lean_object* v_decl_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_){
_start:
{
lean_object* v_toSignature_5596_; lean_object* v_value_5597_; uint8_t v_recursive_5598_; lean_object* v_inlineAttr_x3f_5599_; lean_object* v___f_5600_; lean_object* v___x_5601_; 
v_toSignature_5596_ = lean_ctor_get(v_decl_5590_, 0);
lean_inc_ref(v_toSignature_5596_);
v_value_5597_ = lean_ctor_get(v_decl_5590_, 1);
lean_inc_ref(v_value_5597_);
v_recursive_5598_ = lean_ctor_get_uint8(v_decl_5590_, sizeof(void*)*3);
v_inlineAttr_x3f_5599_ = lean_ctor_get(v_decl_5590_, 2);
lean_inc(v_inlineAttr_x3f_5599_);
v___f_5600_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5600_, 0, v_decl_5590_);
v___x_5601_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v___f_5600_, v_value_5597_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_);
if (lean_obj_tag(v___x_5601_) == 0)
{
lean_object* v_a_5602_; lean_object* v___x_5604_; uint8_t v_isShared_5605_; uint8_t v_isSharedCheck_5610_; 
v_a_5602_ = lean_ctor_get(v___x_5601_, 0);
v_isSharedCheck_5610_ = !lean_is_exclusive(v___x_5601_);
if (v_isSharedCheck_5610_ == 0)
{
v___x_5604_ = v___x_5601_;
v_isShared_5605_ = v_isSharedCheck_5610_;
goto v_resetjp_5603_;
}
else
{
lean_inc(v_a_5602_);
lean_dec(v___x_5601_);
v___x_5604_ = lean_box(0);
v_isShared_5605_ = v_isSharedCheck_5610_;
goto v_resetjp_5603_;
}
v_resetjp_5603_:
{
lean_object* v___x_5606_; lean_object* v___x_5608_; 
v___x_5606_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_5606_, 0, v_toSignature_5596_);
lean_ctor_set(v___x_5606_, 1, v_a_5602_);
lean_ctor_set(v___x_5606_, 2, v_inlineAttr_x3f_5599_);
lean_ctor_set_uint8(v___x_5606_, sizeof(void*)*3, v_recursive_5598_);
if (v_isShared_5605_ == 0)
{
lean_ctor_set(v___x_5604_, 0, v___x_5606_);
v___x_5608_ = v___x_5604_;
goto v_reusejp_5607_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v___x_5606_);
v___x_5608_ = v_reuseFailAlloc_5609_;
goto v_reusejp_5607_;
}
v_reusejp_5607_:
{
return v___x_5608_;
}
}
}
else
{
lean_object* v_a_5611_; lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5618_; 
lean_dec(v_inlineAttr_x3f_5599_);
lean_dec_ref(v_toSignature_5596_);
v_a_5611_ = lean_ctor_get(v___x_5601_, 0);
v_isSharedCheck_5618_ = !lean_is_exclusive(v___x_5601_);
if (v_isSharedCheck_5618_ == 0)
{
v___x_5613_ = v___x_5601_;
v_isShared_5614_ = v_isSharedCheck_5618_;
goto v_resetjp_5612_;
}
else
{
lean_inc(v_a_5611_);
lean_dec(v___x_5601_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5618_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
lean_object* v___x_5616_; 
if (v_isShared_5614_ == 0)
{
v___x_5616_ = v___x_5613_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5617_; 
v_reuseFailAlloc_5617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5617_, 0, v_a_5611_);
v___x_5616_ = v_reuseFailAlloc_5617_;
goto v_reusejp_5615_;
}
v_reusejp_5615_:
{
return v___x_5616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___boxed(lean_object* v_decl_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_){
_start:
{
lean_object* v_res_5625_; 
v_res_5625_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(v_decl_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_);
lean_dec(v_a_5623_);
lean_dec_ref(v_a_5622_);
lean_dec(v_a_5621_);
lean_dec_ref(v_a_5620_);
return v_res_5625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(size_t v_sz_5626_, size_t v_i_5627_, lean_object* v_bs_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_){
_start:
{
uint8_t v___x_5634_; 
v___x_5634_ = lean_usize_dec_lt(v_i_5627_, v_sz_5626_);
if (v___x_5634_ == 0)
{
lean_object* v___x_5635_; 
v___x_5635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5635_, 0, v_bs_5628_);
return v___x_5635_;
}
else
{
lean_object* v_v_5636_; lean_object* v___x_5637_; lean_object* v_bs_x27_5638_; lean_object* v___x_5639_; 
v_v_5636_ = lean_array_uget(v_bs_5628_, v_i_5627_);
v___x_5637_ = lean_unsigned_to_nat(0u);
v_bs_x27_5638_ = lean_array_uset(v_bs_5628_, v_i_5627_, v___x_5637_);
v___x_5639_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(v_v_5636_, v___y_5629_, v___y_5630_, v___y_5631_, v___y_5632_);
if (lean_obj_tag(v___x_5639_) == 0)
{
lean_object* v_a_5640_; size_t v___x_5641_; size_t v___x_5642_; lean_object* v___x_5643_; 
v_a_5640_ = lean_ctor_get(v___x_5639_, 0);
lean_inc(v_a_5640_);
lean_dec_ref_known(v___x_5639_, 1);
v___x_5641_ = ((size_t)1ULL);
v___x_5642_ = lean_usize_add(v_i_5627_, v___x_5641_);
v___x_5643_ = lean_array_uset(v_bs_x27_5638_, v_i_5627_, v_a_5640_);
v_i_5627_ = v___x_5642_;
v_bs_5628_ = v___x_5643_;
goto _start;
}
else
{
lean_object* v_a_5645_; lean_object* v___x_5647_; uint8_t v_isShared_5648_; uint8_t v_isSharedCheck_5652_; 
lean_dec_ref(v_bs_x27_5638_);
v_a_5645_ = lean_ctor_get(v___x_5639_, 0);
v_isSharedCheck_5652_ = !lean_is_exclusive(v___x_5639_);
if (v_isSharedCheck_5652_ == 0)
{
v___x_5647_ = v___x_5639_;
v_isShared_5648_ = v_isSharedCheck_5652_;
goto v_resetjp_5646_;
}
else
{
lean_inc(v_a_5645_);
lean_dec(v___x_5639_);
v___x_5647_ = lean_box(0);
v_isShared_5648_ = v_isSharedCheck_5652_;
goto v_resetjp_5646_;
}
v_resetjp_5646_:
{
lean_object* v___x_5650_; 
if (v_isShared_5648_ == 0)
{
v___x_5650_ = v___x_5647_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v_a_5645_);
v___x_5650_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
return v___x_5650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0___boxed(lean_object* v_sz_5653_, lean_object* v_i_5654_, lean_object* v_bs_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_){
_start:
{
size_t v_sz_boxed_5661_; size_t v_i_boxed_5662_; lean_object* v_res_5663_; 
v_sz_boxed_5661_ = lean_unbox_usize(v_sz_5653_);
lean_dec(v_sz_5653_);
v_i_boxed_5662_ = lean_unbox_usize(v_i_5654_);
lean_dec(v_i_5654_);
v_res_5663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(v_sz_boxed_5661_, v_i_boxed_5662_, v_bs_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_);
lean_dec(v___y_5659_);
lean_dec_ref(v___y_5658_);
lean_dec(v___y_5657_);
lean_dec_ref(v___y_5656_);
return v_res_5663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc(lean_object* v_decls_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_){
_start:
{
size_t v_sz_5670_; size_t v___x_5671_; lean_object* v___x_5672_; 
v_sz_5670_ = lean_array_size(v_decls_5664_);
v___x_5671_ = ((size_t)0ULL);
v___x_5672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(v_sz_5670_, v___x_5671_, v_decls_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_);
return v___x_5672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc___boxed(lean_object* v_decls_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_){
_start:
{
lean_object* v_res_5679_; 
v_res_5679_ = l_Lean_Compiler_LCNF_runExplicitRc(v_decls_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_);
lean_dec(v_a_5677_);
lean_dec_ref(v_a_5676_);
lean_dec(v_a_5675_);
lean_dec_ref(v_a_5674_);
return v_res_5679_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_explicitRc___closed__3(void){
_start:
{
lean_object* v___x_5684_; lean_object* v___x_5685_; uint8_t v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; 
v___x_5684_ = lean_unsigned_to_nat(0u);
v___x_5685_ = ((lean_object*)(l_Lean_Compiler_LCNF_explicitRc___closed__2));
v___x_5686_ = 2;
v___x_5687_ = ((lean_object*)(l_Lean_Compiler_LCNF_explicitRc___closed__1));
v___x_5688_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_5687_, v___x_5686_, v___x_5685_, v___x_5684_);
return v___x_5688_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_explicitRc(void){
_start:
{
lean_object* v___x_5689_; 
v___x_5689_ = lean_obj_once(&l_Lean_Compiler_LCNF_explicitRc___closed__3, &l_Lean_Compiler_LCNF_explicitRc___closed__3_once, _init_l_Lean_Compiler_LCNF_explicitRc___closed__3);
return v___x_5689_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; 
v___x_5745_ = lean_unsigned_to_nat(3791338971u);
v___x_5746_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5747_ = l_Lean_Name_num___override(v___x_5746_, v___x_5745_);
return v___x_5747_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; 
v___x_5749_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5750_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5751_ = l_Lean_Name_str___override(v___x_5750_, v___x_5749_);
return v___x_5751_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; 
v___x_5753_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5754_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5755_ = l_Lean_Name_str___override(v___x_5754_, v___x_5753_);
return v___x_5755_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; 
v___x_5756_ = lean_unsigned_to_nat(2u);
v___x_5757_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5758_ = l_Lean_Name_num___override(v___x_5757_, v___x_5756_);
return v___x_5758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5760_; uint8_t v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; 
v___x_5760_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5761_ = 1;
v___x_5762_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5763_ = l_Lean_registerTraceClass(v___x_5760_, v___x_5761_, v___x_5762_);
return v___x_5763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2____boxed(lean_object* v_a_5764_){
_start:
{
lean_object* v_res_5765_; 
v_res_5765_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_();
return v_res_5765_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instInhabitedLiveVars_default = _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedLiveVars_default);
l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars = _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars);
l_Lean_Compiler_LCNF_explicitRc = _init_l_Lean_Compiler_LCNF_explicitRc();
lean_mark_persistent(l_Lean_Compiler_LCNF_explicitRc);
res = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
}
#ifdef __cplusplus
}
#endif
