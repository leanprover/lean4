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
case 7:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec_ref_known(v_code_116_, 4);
lean_dec_ref(v_s_117_);
v___x_144_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3);
v___x_145_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__2(v___x_144_);
return v___x_145_;
}
case 8:
{
lean_object* v_k_146_; 
v_k_146_ = lean_ctor_get(v_code_116_, 3);
lean_inc_ref(v_k_146_);
lean_dec_ref_known(v_code_116_, 4);
v_code_116_ = v_k_146_;
goto _start;
}
case 9:
{
lean_object* v_k_148_; 
v_k_148_ = lean_ctor_get(v_code_116_, 5);
lean_inc_ref(v_k_148_);
lean_dec_ref_known(v_code_116_, 6);
v_code_116_ = v_k_148_;
goto _start;
}
case 10:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec_ref_known(v_code_116_, 3);
lean_dec_ref(v_s_117_);
v___x_150_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3);
v___x_151_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__2(v___x_150_);
return v___x_151_;
}
case 11:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec_ref_known(v_code_116_, 3);
lean_dec_ref(v_s_117_);
v___x_152_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3);
v___x_153_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__2(v___x_152_);
return v___x_153_;
}
case 12:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec_ref_known(v_code_116_, 4);
lean_dec_ref(v_s_117_);
v___x_154_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3);
v___x_155_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__2(v___x_154_);
return v___x_155_;
}
case 13:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec_ref_known(v_code_116_, 2);
lean_dec_ref(v_s_117_);
v___x_156_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3);
v___x_157_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__2(v___x_156_);
return v___x_157_;
}
default: 
{
lean_dec_ref(v_code_116_);
return v_s_117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(lean_object* v_as_158_, size_t v_i_159_, size_t v_stop_160_, lean_object* v_b_161_){
_start:
{
lean_object* v___y_163_; uint8_t v___x_168_; 
v___x_168_ = lean_usize_dec_eq(v_i_159_, v_stop_160_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
v___x_169_ = lean_array_uget_borrowed(v_as_158_, v_i_159_);
switch(lean_obj_tag(v___x_169_))
{
case 0:
{
lean_object* v_code_170_; 
v_code_170_ = lean_ctor_get(v___x_169_, 2);
lean_inc_ref(v_code_170_);
v___y_163_ = v_code_170_;
goto v___jp_162_;
}
case 1:
{
lean_object* v_code_171_; 
v_code_171_ = lean_ctor_get(v___x_169_, 1);
lean_inc_ref(v_code_171_);
v___y_163_ = v_code_171_;
goto v___jp_162_;
}
default: 
{
lean_object* v_code_172_; 
v_code_172_ = lean_ctor_get(v___x_169_, 0);
lean_inc_ref(v_code_172_);
v___y_163_ = v_code_172_;
goto v___jp_162_;
}
}
}
else
{
return v_b_161_;
}
v___jp_162_:
{
lean_object* v___x_164_; size_t v___x_165_; size_t v___x_166_; 
v___x_164_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(v___y_163_, v_b_161_);
v___x_165_ = ((size_t)1ULL);
v___x_166_ = lean_usize_add(v_i_159_, v___x_165_);
v_i_159_ = v___x_166_;
v_b_161_ = v___x_164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1___boxed(lean_object* v_as_173_, lean_object* v_i_174_, lean_object* v_stop_175_, lean_object* v_b_176_){
_start:
{
size_t v_i_boxed_177_; size_t v_stop_boxed_178_; lean_object* v_res_179_; 
v_i_boxed_177_ = lean_unbox_usize(v_i_174_);
lean_dec(v_i_174_);
v_stop_boxed_178_ = lean_unbox_usize(v_stop_175_);
lean_dec(v_stop_175_);
v_res_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(v_as_173_, v_i_boxed_177_, v_stop_boxed_178_, v_b_176_);
lean_dec_ref(v_as_173_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0(lean_object* v_00_u03b2_180_, lean_object* v_m_181_, lean_object* v_a_182_, lean_object* v_b_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_m_181_, v_a_182_, v_b_183_);
return v___x_184_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0(lean_object* v_00_u03b2_185_, lean_object* v_a_186_, lean_object* v_x_187_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_186_, v_x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_189_, lean_object* v_a_190_, lean_object* v_x_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0(v_00_u03b2_189_, v_a_190_, v_x_191_);
lean_dec(v_x_191_);
lean_dec(v_a_190_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1(lean_object* v_00_u03b2_194_, lean_object* v_data_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(v_data_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_197_, lean_object* v_i_198_, lean_object* v_source_199_, lean_object* v_target_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3___redArg(v_i_198_, v_source_199_, v_target_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_202_, lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5___redArg(v_x_203_, v_x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets(lean_object* v_code_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_208_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(v_code_206_, v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_box(0);
v___x_216_ = lean_unsigned_to_nat(16u);
v___x_217_ = lean_mk_array(v___x_216_, v___x_215_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
return v___x_223_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__0(lean_object* v___x_225_, lean_object* v___x_226_, lean_object* v_a_227_, lean_object* v_b_228_, lean_object* v_acc_229_){
_start:
{
lean_object* v_r_230_; lean_object* v___x_231_; 
v_r_230_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_225_, v___x_226_, v_acc_229_, v_a_227_, v_b_228_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v_r_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__1(lean_object* v___x_232_, lean_object* v___f_233_, lean_object* v_a_234_, lean_object* v_x_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_232_, v___f_233_, v_a_234_, v___y_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union(lean_object* v_liveVars1_267_, lean_object* v_liveVars2_268_){
_start:
{
lean_object* v_vars_269_; lean_object* v_borrows_270_; lean_object* v_vars_271_; lean_object* v_borrows_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_307_; 
v_vars_269_ = lean_ctor_get(v_liveVars1_267_, 0);
lean_inc_ref(v_vars_269_);
v_borrows_270_ = lean_ctor_get(v_liveVars1_267_, 1);
lean_inc_ref(v_borrows_270_);
lean_dec_ref(v_liveVars1_267_);
v_vars_271_ = lean_ctor_get(v_liveVars2_268_, 0);
v_borrows_272_ = lean_ctor_get(v_liveVars2_268_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_liveVars2_268_);
if (v_isSharedCheck_307_ == 0)
{
v___x_274_ = v_liveVars2_268_;
v_isShared_275_ = v_isSharedCheck_307_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_borrows_272_);
lean_inc(v_vars_271_);
lean_dec(v_liveVars2_268_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_307_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v_size_277_; lean_object* v_buckets_278_; lean_object* v_size_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___y_283_; uint8_t v___x_300_; 
v___x_276_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v_size_277_ = lean_ctor_get(v_vars_269_, 0);
v_buckets_278_ = lean_ctor_get(v_vars_269_, 1);
v_size_279_ = lean_ctor_get(v_vars_271_, 0);
v___x_280_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_281_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_300_ = lean_nat_dec_le(v_size_277_, v_size_279_);
if (v___x_300_ == 0)
{
lean_object* v___f_301_; lean_object* v___x_302_; 
v___f_301_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__13));
v___x_302_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_301_, v___x_280_, v___x_281_, v_vars_269_, v_vars_271_);
v___y_283_ = v___x_302_;
goto v___jp_282_;
}
else
{
lean_object* v___f_303_; size_t v_sz_304_; size_t v___x_305_; lean_object* v___x_306_; 
lean_inc_ref(v_buckets_278_);
lean_dec_ref(v_vars_269_);
v___f_303_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__14));
v_sz_304_ = lean_array_size(v_buckets_278_);
v___x_305_ = ((size_t)0ULL);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_276_, v_buckets_278_, v___f_303_, v_sz_304_, v___x_305_, v_vars_271_);
v___y_283_ = v___x_306_;
goto v___jp_282_;
}
v___jp_282_:
{
lean_object* v_size_284_; lean_object* v_buckets_285_; lean_object* v_size_286_; uint8_t v___x_287_; 
v_size_284_ = lean_ctor_get(v_borrows_270_, 0);
v_buckets_285_ = lean_ctor_get(v_borrows_270_, 1);
v_size_286_ = lean_ctor_get(v_borrows_272_, 0);
v___x_287_ = lean_nat_dec_le(v_size_284_, v_size_286_);
if (v___x_287_ == 0)
{
lean_object* v___f_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___f_288_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__13));
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_288_, v___x_280_, v___x_281_, v_borrows_270_, v_borrows_272_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 1, v___x_289_);
lean_ctor_set(v___x_274_, 0, v___y_283_);
v___x_291_ = v___x_274_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___y_283_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
else
{
lean_object* v___f_293_; size_t v_sz_294_; size_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
lean_inc_ref(v_buckets_285_);
lean_dec_ref(v_borrows_270_);
v___f_293_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__14));
v_sz_294_ = lean_array_size(v_buckets_285_);
v___x_295_ = ((size_t)0ULL);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_276_, v_buckets_285_, v___f_293_, v_sz_294_, v___x_295_, v_borrows_272_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 1, v___x_296_);
lean_ctor_set(v___x_274_, 0, v___y_283_);
v___x_298_ = v___x_274_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___y_283_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_erase(lean_object* v_liveVars_308_, lean_object* v_fvarId_309_){
_start:
{
lean_object* v_vars_310_; lean_object* v_borrows_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_322_; 
v_vars_310_ = lean_ctor_get(v_liveVars_308_, 0);
v_borrows_311_ = lean_ctor_get(v_liveVars_308_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v_liveVars_308_);
if (v_isSharedCheck_322_ == 0)
{
v___x_313_ = v_liveVars_308_;
v_isShared_314_ = v_isSharedCheck_322_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_borrows_311_);
lean_inc(v_vars_310_);
lean_dec(v_liveVars_308_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_322_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_vars_317_; lean_object* v_borrows_318_; lean_object* v___x_320_; 
v___x_315_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_316_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
lean_inc(v_fvarId_309_);
v_vars_317_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_315_, v___x_316_, v_vars_310_, v_fvarId_309_);
v_borrows_318_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_315_, v___x_316_, v_borrows_311_, v_fvarId_309_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v_borrows_318_);
lean_ctor_set(v___x_313_, 0, v_vars_317_);
v___x_320_ = v___x_313_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_vars_317_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_borrows_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_insertBorrow(lean_object* v_liveVars_323_, lean_object* v_fvarId_324_){
_start:
{
lean_object* v_vars_325_; lean_object* v_borrows_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_337_; 
v_vars_325_ = lean_ctor_get(v_liveVars_323_, 0);
v_borrows_326_ = lean_ctor_get(v_liveVars_323_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_liveVars_323_);
if (v_isSharedCheck_337_ == 0)
{
v___x_328_ = v_liveVars_323_;
v_isShared_329_ = v_isSharedCheck_337_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_borrows_326_);
lean_inc(v_vars_325_);
lean_dec(v_liveVars_323_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_337_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_330_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_331_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_332_ = lean_box(0);
v___x_333_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_330_, v___x_331_, v_borrows_326_, v_fvarId_324_, v___x_332_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_333_);
v___x_335_ = v___x_328_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_vars_325_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_333_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_insertLive(lean_object* v_liveVars_338_, lean_object* v_fvarId_339_){
_start:
{
lean_object* v_vars_340_; lean_object* v_borrows_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_352_; 
v_vars_340_ = lean_ctor_get(v_liveVars_338_, 0);
v_borrows_341_ = lean_ctor_get(v_liveVars_338_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_liveVars_338_);
if (v_isSharedCheck_352_ == 0)
{
v___x_343_ = v_liveVars_338_;
v_isShared_344_ = v_isSharedCheck_352_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_borrows_341_);
lean_inc(v_vars_340_);
lean_dec(v_liveVars_338_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_352_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_345_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_346_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_347_ = lean_box(0);
v___x_348_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_345_, v___x_346_, v_vars_340_, v_fvarId_339_, v___x_347_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_348_);
v___x_350_ = v___x_343_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_borrows_341_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(lean_object* v_fvarId_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_varMap_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_varMap_364_ = lean_ctor_get(v_a_362_, 3);
v___f_365_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_366_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_varMap_364_);
v___x_367_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_365_, v___x_366_, v_varMap_364_, v_fvarId_361_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___boxed(lean_object* v_fvarId_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(v_fvarId_369_, v_a_370_);
lean_dec_ref(v_a_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(lean_object* v_fvarId_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_varMap_381_; lean_object* v___f_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_varMap_381_ = lean_ctor_get(v_a_374_, 3);
v___f_382_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_383_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_varMap_381_);
v___x_384_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_382_, v___x_383_, v_varMap_381_, v_fvarId_373_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___boxed(lean_object* v_fvarId_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(v_fvarId_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(lean_object* v_fvarId_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_jpLiveVarMap_398_; lean_object* v___f_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_jpLiveVarMap_398_ = lean_ctor_get(v_a_396_, 4);
v___f_399_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_400_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
lean_inc(v_jpLiveVarMap_398_);
v___x_401_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_399_, v___x_400_, v_jpLiveVarMap_398_, v_fvarId_395_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg___boxed(lean_object* v_fvarId_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(v_fvarId_403_, v_a_404_);
lean_dec_ref(v_a_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(lean_object* v_fvarId_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_jpLiveVarMap_415_; lean_object* v___f_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_jpLiveVarMap_415_ = lean_ctor_get(v_a_408_, 4);
v___f_416_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_417_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
lean_inc(v_jpLiveVarMap_415_);
v___x_418_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_416_, v___x_417_, v_jpLiveVarMap_415_, v_fvarId_407_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___boxed(lean_object* v_fvarId_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(v_fvarId_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg(lean_object* v_fvarId_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_vars_435_; uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_432_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_433_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_434_ = lean_st_ref_get(v_a_430_);
v_vars_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc_ref(v_vars_435_);
lean_dec(v___x_434_);
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_432_, v___x_433_, v_vars_435_, v_fvarId_429_);
lean_dec_ref(v_vars_435_);
v___x_437_ = lean_box(v___x_436_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg___boxed(lean_object* v_fvarId_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg(v_fvarId_439_, v_a_440_);
lean_dec(v_a_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(lean_object* v_fvarId_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v_vars_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_451_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_452_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_453_ = lean_st_ref_get(v_a_445_);
v_vars_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc_ref(v_vars_454_);
lean_dec(v___x_453_);
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_451_, v___x_452_, v_vars_454_, v_fvarId_443_);
lean_dec_ref(v_vars_454_);
v___x_456_ = lean_box(v___x_455_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___boxed(lean_object* v_fvarId_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(v_fvarId_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(lean_object* v_fvarId_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_borrows_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_470_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_471_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_472_ = lean_st_ref_get(v_a_468_);
v_borrows_473_ = lean_ctor_get(v___x_472_, 1);
lean_inc_ref(v_borrows_473_);
lean_dec(v___x_472_);
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_470_, v___x_471_, v_borrows_473_, v_fvarId_467_);
lean_dec_ref(v_borrows_473_);
v___x_475_ = lean_box(v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg___boxed(lean_object* v_fvarId_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(v_fvarId_477_, v_a_478_);
lean_dec(v_a_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(lean_object* v_fvarId_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_borrows_492_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_490_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_491_ = lean_st_ref_get(v_a_483_);
v_borrows_492_ = lean_ctor_get(v___x_491_, 1);
lean_inc_ref(v_borrows_492_);
lean_dec(v___x_491_);
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_489_, v___x_490_, v_borrows_492_, v_fvarId_481_);
lean_dec_ref(v_borrows_492_);
v___x_494_ = lean_box(v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___boxed(lean_object* v_fvarId_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(v_fvarId_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(lean_object* v_f_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_508_ = lean_st_ref_take(v_a_506_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_apply_1(v_f_505_, v___x_508_);
v___x_511_ = lean_st_ref_put(v_a_506_, v___x_510_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_509_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg___boxed(lean_object* v_f_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(v_f_513_, v_a_514_);
lean_dec(v_a_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(lean_object* v_f_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_525_ = lean_st_ref_take(v_a_519_);
v___x_526_ = lean_box(0);
v___x_527_ = lean_apply_1(v_f_517_, v___x_525_);
v___x_528_ = lean_st_ref_put(v_a_519_, v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_526_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___boxed(lean_object* v_f_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(v_f_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(lean_object* v_child_539_, lean_object* v_k_540_, lean_object* v_t_541_){
_start:
{
if (lean_obj_tag(v_t_541_) == 0)
{
lean_object* v_size_542_; lean_object* v_k_543_; lean_object* v_v_544_; lean_object* v_l_545_; lean_object* v_r_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_572_; 
v_size_542_ = lean_ctor_get(v_t_541_, 0);
v_k_543_ = lean_ctor_get(v_t_541_, 1);
v_v_544_ = lean_ctor_get(v_t_541_, 2);
v_l_545_ = lean_ctor_get(v_t_541_, 3);
v_r_546_ = lean_ctor_get(v_t_541_, 4);
v_isSharedCheck_572_ = !lean_is_exclusive(v_t_541_);
if (v_isSharedCheck_572_ == 0)
{
v___x_548_ = v_t_541_;
v_isShared_549_ = v_isSharedCheck_572_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_r_546_);
lean_inc(v_l_545_);
lean_inc(v_v_544_);
lean_inc(v_k_543_);
lean_inc(v_size_542_);
lean_dec(v_t_541_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_572_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
uint8_t v___x_550_; 
v___x_550_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_540_, v_k_543_);
switch(v___x_550_)
{
case 0:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(v_child_539_, v_k_540_, v_l_545_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 3, v___x_551_);
v___x_553_ = v___x_548_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_size_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_k_543_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_v_544_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_r_546_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
case 1:
{
lean_object* v_parents_555_; lean_object* v_children_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_k_543_);
v_parents_555_ = lean_ctor_get(v_v_544_, 0);
v_children_556_ = lean_ctor_get(v_v_544_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_v_544_);
if (v_isSharedCheck_567_ == 0)
{
v___x_558_ = v_v_544_;
v_isShared_559_ = v_isSharedCheck_567_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_children_556_);
lean_inc(v_parents_555_);
lean_dec(v_v_544_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_567_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_560_, 0, v_child_539_);
lean_ctor_set(v___x_560_, 1, v_children_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_parents_555_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_560_);
v___x_562_ = v_reuseFailAlloc_566_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_564_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 2, v___x_562_);
lean_ctor_set(v___x_548_, 1, v_k_540_);
v___x_564_ = v___x_548_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_size_542_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_k_540_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v_l_545_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v_r_546_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
default: 
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(v_child_539_, v_k_540_, v_r_546_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 4, v___x_568_);
v___x_570_ = v___x_548_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_size_542_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_k_543_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_v_544_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_l_545_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
else
{
lean_dec(v_k_540_);
lean_dec(v_child_539_);
return v_t_541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(lean_object* v_child_573_, lean_object* v_as_574_, size_t v_i_575_, size_t v_stop_576_, lean_object* v_b_577_){
_start:
{
uint8_t v___x_578_; 
v___x_578_ = lean_usize_dec_eq(v_i_575_, v_stop_576_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; size_t v___x_581_; size_t v___x_582_; 
v___x_579_ = lean_array_uget_borrowed(v_as_574_, v_i_575_);
lean_inc(v___x_579_);
lean_inc(v_child_573_);
v___x_580_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(v_child_573_, v___x_579_, v_b_577_);
v___x_581_ = ((size_t)1ULL);
v___x_582_ = lean_usize_add(v_i_575_, v___x_581_);
v_i_575_ = v___x_582_;
v_b_577_ = v___x_580_;
goto _start;
}
else
{
lean_dec(v_child_573_);
return v_b_577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3___boxed(lean_object* v_child_584_, lean_object* v_as_585_, lean_object* v_i_586_, lean_object* v_stop_587_, lean_object* v_b_588_){
_start:
{
size_t v_i_boxed_589_; size_t v_stop_boxed_590_; lean_object* v_res_591_; 
v_i_boxed_589_ = lean_unbox_usize(v_i_586_);
lean_dec(v_i_586_);
v_stop_boxed_590_ = lean_unbox_usize(v_stop_587_);
lean_dec(v_stop_587_);
v_res_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(v_child_584_, v_as_585_, v_i_boxed_589_, v_stop_boxed_590_, v_b_588_);
lean_dec_ref(v_as_585_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(lean_object* v_k_592_, lean_object* v_v_593_, lean_object* v_t_594_){
_start:
{
if (lean_obj_tag(v_t_594_) == 0)
{
lean_object* v_size_595_; lean_object* v_k_596_; lean_object* v_v_597_; lean_object* v_l_598_; lean_object* v_r_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_879_; 
v_size_595_ = lean_ctor_get(v_t_594_, 0);
v_k_596_ = lean_ctor_get(v_t_594_, 1);
v_v_597_ = lean_ctor_get(v_t_594_, 2);
v_l_598_ = lean_ctor_get(v_t_594_, 3);
v_r_599_ = lean_ctor_get(v_t_594_, 4);
v_isSharedCheck_879_ = !lean_is_exclusive(v_t_594_);
if (v_isSharedCheck_879_ == 0)
{
v___x_601_ = v_t_594_;
v_isShared_602_ = v_isSharedCheck_879_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_r_599_);
lean_inc(v_l_598_);
lean_inc(v_v_597_);
lean_inc(v_k_596_);
lean_inc(v_size_595_);
lean_dec(v_t_594_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_879_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
uint8_t v___x_603_; 
v___x_603_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_592_, v_k_596_);
switch(v___x_603_)
{
case 0:
{
lean_object* v_impl_604_; lean_object* v___x_605_; 
lean_dec(v_size_595_);
v_impl_604_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_k_592_, v_v_593_, v_l_598_);
v___x_605_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_599_) == 0)
{
lean_object* v_size_606_; lean_object* v_size_607_; lean_object* v_k_608_; lean_object* v_v_609_; lean_object* v_l_610_; lean_object* v_r_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_size_606_ = lean_ctor_get(v_r_599_, 0);
v_size_607_ = lean_ctor_get(v_impl_604_, 0);
lean_inc(v_size_607_);
v_k_608_ = lean_ctor_get(v_impl_604_, 1);
lean_inc(v_k_608_);
v_v_609_ = lean_ctor_get(v_impl_604_, 2);
lean_inc(v_v_609_);
v_l_610_ = lean_ctor_get(v_impl_604_, 3);
lean_inc(v_l_610_);
v_r_611_ = lean_ctor_get(v_impl_604_, 4);
lean_inc(v_r_611_);
v___x_612_ = lean_unsigned_to_nat(3u);
v___x_613_ = lean_nat_mul(v___x_612_, v_size_606_);
v___x_614_ = lean_nat_dec_lt(v___x_613_, v_size_607_);
lean_dec(v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
lean_dec(v_r_611_);
lean_dec(v_l_610_);
lean_dec(v_v_609_);
lean_dec(v_k_608_);
v___x_615_ = lean_nat_add(v___x_605_, v_size_607_);
lean_dec(v_size_607_);
v___x_616_ = lean_nat_add(v___x_615_, v_size_606_);
lean_dec(v___x_615_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 3, v_impl_604_);
lean_ctor_set(v___x_601_, 0, v___x_616_);
v___x_618_ = v___x_601_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_impl_604_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v_r_599_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_685_; 
v_isSharedCheck_685_ = !lean_is_exclusive(v_impl_604_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; lean_object* v_unused_687_; lean_object* v_unused_688_; lean_object* v_unused_689_; lean_object* v_unused_690_; 
v_unused_686_ = lean_ctor_get(v_impl_604_, 4);
lean_dec(v_unused_686_);
v_unused_687_ = lean_ctor_get(v_impl_604_, 3);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_impl_604_, 2);
lean_dec(v_unused_688_);
v_unused_689_ = lean_ctor_get(v_impl_604_, 1);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_impl_604_, 0);
lean_dec(v_unused_690_);
v___x_621_ = v_impl_604_;
v_isShared_622_ = v_isSharedCheck_685_;
goto v_resetjp_620_;
}
else
{
lean_dec(v_impl_604_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_685_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_size_623_; lean_object* v_size_624_; lean_object* v_k_625_; lean_object* v_v_626_; lean_object* v_l_627_; lean_object* v_r_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_size_623_ = lean_ctor_get(v_l_610_, 0);
v_size_624_ = lean_ctor_get(v_r_611_, 0);
v_k_625_ = lean_ctor_get(v_r_611_, 1);
v_v_626_ = lean_ctor_get(v_r_611_, 2);
v_l_627_ = lean_ctor_get(v_r_611_, 3);
v_r_628_ = lean_ctor_get(v_r_611_, 4);
v___x_629_ = lean_unsigned_to_nat(2u);
v___x_630_ = lean_nat_mul(v___x_629_, v_size_623_);
v___x_631_ = lean_nat_dec_lt(v_size_624_, v___x_630_);
lean_dec(v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_660_; 
lean_inc(v_r_628_);
lean_inc(v_l_627_);
lean_inc(v_v_626_);
lean_inc(v_k_625_);
v_isSharedCheck_660_ = !lean_is_exclusive(v_r_611_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; lean_object* v_unused_662_; lean_object* v_unused_663_; lean_object* v_unused_664_; lean_object* v_unused_665_; 
v_unused_661_ = lean_ctor_get(v_r_611_, 4);
lean_dec(v_unused_661_);
v_unused_662_ = lean_ctor_get(v_r_611_, 3);
lean_dec(v_unused_662_);
v_unused_663_ = lean_ctor_get(v_r_611_, 2);
lean_dec(v_unused_663_);
v_unused_664_ = lean_ctor_get(v_r_611_, 1);
lean_dec(v_unused_664_);
v_unused_665_ = lean_ctor_get(v_r_611_, 0);
lean_dec(v_unused_665_);
v___x_633_ = v_r_611_;
v_isShared_634_ = v_isSharedCheck_660_;
goto v_resetjp_632_;
}
else
{
lean_dec(v_r_611_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_660_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___x_648_; lean_object* v___y_650_; 
v___x_635_ = lean_nat_add(v___x_605_, v_size_607_);
lean_dec(v_size_607_);
v___x_636_ = lean_nat_add(v___x_635_, v_size_606_);
lean_dec(v___x_635_);
v___x_648_ = lean_nat_add(v___x_605_, v_size_623_);
if (lean_obj_tag(v_l_627_) == 0)
{
lean_object* v_size_658_; 
v_size_658_ = lean_ctor_get(v_l_627_, 0);
lean_inc(v_size_658_);
v___y_650_ = v_size_658_;
goto v___jp_649_;
}
else
{
lean_object* v___x_659_; 
v___x_659_ = lean_unsigned_to_nat(0u);
v___y_650_ = v___x_659_;
goto v___jp_649_;
}
v___jp_637_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = lean_nat_add(v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec(v___y_639_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_r_599_);
lean_ctor_set(v___x_633_, 3, v_r_628_);
lean_ctor_set(v___x_633_, 2, v_v_597_);
lean_ctor_set(v___x_633_, 1, v_k_596_);
lean_ctor_set(v___x_633_, 0, v___x_641_);
v___x_643_ = v___x_633_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_r_628_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v_r_599_);
v___x_643_ = v_reuseFailAlloc_647_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v___x_643_);
lean_ctor_set(v___x_621_, 3, v___y_638_);
lean_ctor_set(v___x_621_, 2, v_v_626_);
lean_ctor_set(v___x_621_, 1, v_k_625_);
lean_ctor_set(v___x_621_, 0, v___x_636_);
v___x_645_ = v___x_621_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_k_625_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_v_626_);
lean_ctor_set(v_reuseFailAlloc_646_, 3, v___y_638_);
lean_ctor_set(v_reuseFailAlloc_646_, 4, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
v___jp_649_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = lean_nat_add(v___x_648_, v___y_650_);
lean_dec(v___y_650_);
lean_dec(v___x_648_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v_l_627_);
lean_ctor_set(v___x_601_, 3, v_l_610_);
lean_ctor_set(v___x_601_, 2, v_v_609_);
lean_ctor_set(v___x_601_, 1, v_k_608_);
lean_ctor_set(v___x_601_, 0, v___x_651_);
v___x_653_ = v___x_601_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_k_608_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_v_609_);
lean_ctor_set(v_reuseFailAlloc_657_, 3, v_l_610_);
lean_ctor_set(v_reuseFailAlloc_657_, 4, v_l_627_);
v___x_653_ = v_reuseFailAlloc_657_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; 
v___x_654_ = lean_nat_add(v___x_605_, v_size_606_);
if (lean_obj_tag(v_r_628_) == 0)
{
lean_object* v_size_655_; 
v_size_655_ = lean_ctor_get(v_r_628_, 0);
lean_inc(v_size_655_);
v___y_638_ = v___x_653_;
v___y_639_ = v___x_654_;
v___y_640_ = v_size_655_;
goto v___jp_637_;
}
else
{
lean_object* v___x_656_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___y_638_ = v___x_653_;
v___y_639_ = v___x_654_;
v___y_640_ = v___x_656_;
goto v___jp_637_;
}
}
}
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
lean_del_object(v___x_601_);
v___x_666_ = lean_nat_add(v___x_605_, v_size_607_);
lean_dec(v_size_607_);
v___x_667_ = lean_nat_add(v___x_666_, v_size_606_);
lean_dec(v___x_666_);
v___x_668_ = lean_nat_add(v___x_605_, v_size_606_);
v___x_669_ = lean_nat_add(v___x_668_, v_size_624_);
lean_dec(v___x_668_);
lean_inc_ref(v_r_599_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v_r_599_);
lean_ctor_set(v___x_621_, 3, v_r_611_);
lean_ctor_set(v___x_621_, 2, v_v_597_);
lean_ctor_set(v___x_621_, 1, v_k_596_);
lean_ctor_set(v___x_621_, 0, v___x_669_);
v___x_671_ = v___x_621_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_r_611_);
lean_ctor_set(v_reuseFailAlloc_684_, 4, v_r_599_);
v___x_671_ = v_reuseFailAlloc_684_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
v_isSharedCheck_678_ = !lean_is_exclusive(v_r_599_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; lean_object* v_unused_680_; lean_object* v_unused_681_; lean_object* v_unused_682_; lean_object* v_unused_683_; 
v_unused_679_ = lean_ctor_get(v_r_599_, 4);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_r_599_, 3);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_r_599_, 2);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_r_599_, 1);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_r_599_, 0);
lean_dec(v_unused_683_);
v___x_673_ = v_r_599_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_dec(v_r_599_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 4, v___x_671_);
lean_ctor_set(v___x_673_, 3, v_l_610_);
lean_ctor_set(v___x_673_, 2, v_v_609_);
lean_ctor_set(v___x_673_, 1, v_k_608_);
lean_ctor_set(v___x_673_, 0, v___x_667_);
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_k_608_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_v_609_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_l_610_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v___x_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_691_; 
v_l_691_ = lean_ctor_get(v_impl_604_, 3);
lean_inc(v_l_691_);
if (lean_obj_tag(v_l_691_) == 0)
{
lean_object* v_r_692_; lean_object* v_k_693_; lean_object* v_v_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_705_; 
v_r_692_ = lean_ctor_get(v_impl_604_, 4);
v_k_693_ = lean_ctor_get(v_impl_604_, 1);
v_v_694_ = lean_ctor_get(v_impl_604_, 2);
v_isSharedCheck_705_ = !lean_is_exclusive(v_impl_604_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; lean_object* v_unused_707_; 
v_unused_706_ = lean_ctor_get(v_impl_604_, 3);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_impl_604_, 0);
lean_dec(v_unused_707_);
v___x_696_ = v_impl_604_;
v_isShared_697_ = v_isSharedCheck_705_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_r_692_);
lean_inc(v_v_694_);
lean_inc(v_k_693_);
lean_dec(v_impl_604_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_705_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_692_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 3, v_r_692_);
lean_ctor_set(v___x_696_, 2, v_v_597_);
lean_ctor_set(v___x_696_, 1, v_k_596_);
lean_ctor_set(v___x_696_, 0, v___x_605_);
v___x_700_ = v___x_696_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_r_692_);
lean_ctor_set(v_reuseFailAlloc_704_, 4, v_r_692_);
v___x_700_ = v_reuseFailAlloc_704_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v___x_700_);
lean_ctor_set(v___x_601_, 3, v_l_691_);
lean_ctor_set(v___x_601_, 2, v_v_694_);
lean_ctor_set(v___x_601_, 1, v_k_693_);
lean_ctor_set(v___x_601_, 0, v___x_698_);
v___x_702_ = v___x_601_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_k_693_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_v_694_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_l_691_);
lean_ctor_set(v_reuseFailAlloc_703_, 4, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v_r_708_; 
v_r_708_ = lean_ctor_get(v_impl_604_, 4);
lean_inc(v_r_708_);
if (lean_obj_tag(v_r_708_) == 0)
{
lean_object* v_k_709_; lean_object* v_v_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_733_; 
v_k_709_ = lean_ctor_get(v_impl_604_, 1);
v_v_710_ = lean_ctor_get(v_impl_604_, 2);
v_isSharedCheck_733_ = !lean_is_exclusive(v_impl_604_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_734_ = lean_ctor_get(v_impl_604_, 4);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_impl_604_, 3);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_impl_604_, 0);
lean_dec(v_unused_736_);
v___x_712_ = v_impl_604_;
v_isShared_713_ = v_isSharedCheck_733_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_v_710_);
lean_inc(v_k_709_);
lean_dec(v_impl_604_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_733_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_k_714_; lean_object* v_v_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_729_; 
v_k_714_ = lean_ctor_get(v_r_708_, 1);
v_v_715_ = lean_ctor_get(v_r_708_, 2);
v_isSharedCheck_729_ = !lean_is_exclusive(v_r_708_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; lean_object* v_unused_731_; lean_object* v_unused_732_; 
v_unused_730_ = lean_ctor_get(v_r_708_, 4);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_r_708_, 3);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_r_708_, 0);
lean_dec(v_unused_732_);
v___x_717_ = v_r_708_;
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_v_715_);
lean_inc(v_k_714_);
lean_dec(v_r_708_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_unsigned_to_nat(3u);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 4, v_l_691_);
lean_ctor_set(v___x_717_, 3, v_l_691_);
lean_ctor_set(v___x_717_, 2, v_v_710_);
lean_ctor_set(v___x_717_, 1, v_k_709_);
lean_ctor_set(v___x_717_, 0, v___x_605_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_k_709_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_v_710_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_l_691_);
lean_ctor_set(v_reuseFailAlloc_728_, 4, v_l_691_);
v___x_721_ = v_reuseFailAlloc_728_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 4, v_l_691_);
lean_ctor_set(v___x_712_, 2, v_v_597_);
lean_ctor_set(v___x_712_, 1, v_k_596_);
lean_ctor_set(v___x_712_, 0, v___x_605_);
v___x_723_ = v___x_712_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_727_, 3, v_l_691_);
lean_ctor_set(v_reuseFailAlloc_727_, 4, v_l_691_);
v___x_723_ = v_reuseFailAlloc_727_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v___x_723_);
lean_ctor_set(v___x_601_, 3, v___x_721_);
lean_ctor_set(v___x_601_, 2, v_v_715_);
lean_ctor_set(v___x_601_, 1, v_k_714_);
lean_ctor_set(v___x_601_, 0, v___x_719_);
v___x_725_ = v___x_601_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_k_714_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_v_715_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(2u);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v_r_708_);
lean_ctor_set(v___x_601_, 3, v_impl_604_);
lean_ctor_set(v___x_601_, 0, v___x_737_);
v___x_739_ = v___x_601_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_impl_604_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v_r_708_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
case 1:
{
lean_object* v___x_742_; 
lean_dec(v_v_597_);
lean_dec(v_k_596_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 2, v_v_593_);
lean_ctor_set(v___x_601_, 1, v_k_592_);
v___x_742_ = v___x_601_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_size_595_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_k_592_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_v_593_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_l_598_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v_r_599_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
default: 
{
lean_object* v_impl_744_; lean_object* v___x_745_; 
lean_dec(v_size_595_);
v_impl_744_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_k_592_, v_v_593_, v_r_599_);
v___x_745_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_598_) == 0)
{
lean_object* v_size_746_; lean_object* v_size_747_; lean_object* v_k_748_; lean_object* v_v_749_; lean_object* v_l_750_; lean_object* v_r_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v_size_746_ = lean_ctor_get(v_l_598_, 0);
v_size_747_ = lean_ctor_get(v_impl_744_, 0);
lean_inc(v_size_747_);
v_k_748_ = lean_ctor_get(v_impl_744_, 1);
lean_inc(v_k_748_);
v_v_749_ = lean_ctor_get(v_impl_744_, 2);
lean_inc(v_v_749_);
v_l_750_ = lean_ctor_get(v_impl_744_, 3);
lean_inc(v_l_750_);
v_r_751_ = lean_ctor_get(v_impl_744_, 4);
lean_inc(v_r_751_);
v___x_752_ = lean_unsigned_to_nat(3u);
v___x_753_ = lean_nat_mul(v___x_752_, v_size_746_);
v___x_754_ = lean_nat_dec_lt(v___x_753_, v_size_747_);
lean_dec(v___x_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
lean_dec(v_r_751_);
lean_dec(v_l_750_);
lean_dec(v_v_749_);
lean_dec(v_k_748_);
v___x_755_ = lean_nat_add(v___x_745_, v_size_746_);
v___x_756_ = lean_nat_add(v___x_755_, v_size_747_);
lean_dec(v_size_747_);
lean_dec(v___x_755_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v_impl_744_);
lean_ctor_set(v___x_601_, 0, v___x_756_);
v___x_758_ = v___x_601_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_l_598_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_impl_744_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
else
{
lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_823_; 
v_isSharedCheck_823_ = !lean_is_exclusive(v_impl_744_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; lean_object* v_unused_825_; lean_object* v_unused_826_; lean_object* v_unused_827_; lean_object* v_unused_828_; 
v_unused_824_ = lean_ctor_get(v_impl_744_, 4);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_impl_744_, 3);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_impl_744_, 2);
lean_dec(v_unused_826_);
v_unused_827_ = lean_ctor_get(v_impl_744_, 1);
lean_dec(v_unused_827_);
v_unused_828_ = lean_ctor_get(v_impl_744_, 0);
lean_dec(v_unused_828_);
v___x_761_ = v_impl_744_;
v_isShared_762_ = v_isSharedCheck_823_;
goto v_resetjp_760_;
}
else
{
lean_dec(v_impl_744_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_823_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_size_763_; lean_object* v_k_764_; lean_object* v_v_765_; lean_object* v_l_766_; lean_object* v_r_767_; lean_object* v_size_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_size_763_ = lean_ctor_get(v_l_750_, 0);
v_k_764_ = lean_ctor_get(v_l_750_, 1);
v_v_765_ = lean_ctor_get(v_l_750_, 2);
v_l_766_ = lean_ctor_get(v_l_750_, 3);
v_r_767_ = lean_ctor_get(v_l_750_, 4);
v_size_768_ = lean_ctor_get(v_r_751_, 0);
v___x_769_ = lean_unsigned_to_nat(2u);
v___x_770_ = lean_nat_mul(v___x_769_, v_size_768_);
v___x_771_ = lean_nat_dec_lt(v_size_763_, v___x_770_);
lean_dec(v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_799_; 
lean_inc(v_r_767_);
lean_inc(v_l_766_);
lean_inc(v_v_765_);
lean_inc(v_k_764_);
v_isSharedCheck_799_ = !lean_is_exclusive(v_l_750_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; lean_object* v_unused_804_; 
v_unused_800_ = lean_ctor_get(v_l_750_, 4);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_l_750_, 3);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_l_750_, 2);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_l_750_, 1);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_l_750_, 0);
lean_dec(v_unused_804_);
v___x_773_ = v_l_750_;
v_isShared_774_ = v_isSharedCheck_799_;
goto v_resetjp_772_;
}
else
{
lean_dec(v_l_750_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_799_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_789_; 
v___x_775_ = lean_nat_add(v___x_745_, v_size_746_);
v___x_776_ = lean_nat_add(v___x_775_, v_size_747_);
lean_dec(v_size_747_);
if (lean_obj_tag(v_l_766_) == 0)
{
lean_object* v_size_797_; 
v_size_797_ = lean_ctor_get(v_l_766_, 0);
lean_inc(v_size_797_);
v___y_789_ = v_size_797_;
goto v___jp_788_;
}
else
{
lean_object* v___x_798_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___y_789_ = v___x_798_;
goto v___jp_788_;
}
v___jp_777_:
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = lean_nat_add(v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec(v___y_779_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 4, v_r_751_);
lean_ctor_set(v___x_773_, 3, v_r_767_);
lean_ctor_set(v___x_773_, 2, v_v_749_);
lean_ctor_set(v___x_773_, 1, v_k_748_);
lean_ctor_set(v___x_773_, 0, v___x_781_);
v___x_783_ = v___x_773_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_k_748_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_v_749_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v_r_767_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v_r_751_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 4, v___x_783_);
lean_ctor_set(v___x_761_, 3, v___y_778_);
lean_ctor_set(v___x_761_, 2, v_v_765_);
lean_ctor_set(v___x_761_, 1, v_k_764_);
lean_ctor_set(v___x_761_, 0, v___x_776_);
v___x_785_ = v___x_761_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_k_764_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_v_765_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v___y_778_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
v___jp_788_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = lean_nat_add(v___x_775_, v___y_789_);
lean_dec(v___y_789_);
lean_dec(v___x_775_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v_l_766_);
lean_ctor_set(v___x_601_, 0, v___x_790_);
v___x_792_ = v___x_601_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_796_, 3, v_l_598_);
lean_ctor_set(v_reuseFailAlloc_796_, 4, v_l_766_);
v___x_792_ = v_reuseFailAlloc_796_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; 
v___x_793_ = lean_nat_add(v___x_745_, v_size_768_);
if (lean_obj_tag(v_r_767_) == 0)
{
lean_object* v_size_794_; 
v_size_794_ = lean_ctor_get(v_r_767_, 0);
lean_inc(v_size_794_);
v___y_778_ = v___x_792_;
v___y_779_ = v___x_793_;
v___y_780_ = v_size_794_;
goto v___jp_777_;
}
else
{
lean_object* v___x_795_; 
v___x_795_ = lean_unsigned_to_nat(0u);
v___y_778_ = v___x_792_;
v___y_779_ = v___x_793_;
v___y_780_ = v___x_795_;
goto v___jp_777_;
}
}
}
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
lean_del_object(v___x_601_);
v___x_805_ = lean_nat_add(v___x_745_, v_size_746_);
v___x_806_ = lean_nat_add(v___x_805_, v_size_747_);
lean_dec(v_size_747_);
v___x_807_ = lean_nat_add(v___x_805_, v_size_763_);
lean_dec(v___x_805_);
lean_inc_ref(v_l_598_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 4, v_l_750_);
lean_ctor_set(v___x_761_, 3, v_l_598_);
lean_ctor_set(v___x_761_, 2, v_v_597_);
lean_ctor_set(v___x_761_, 1, v_k_596_);
lean_ctor_set(v___x_761_, 0, v___x_807_);
v___x_809_ = v___x_761_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_l_598_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v_l_750_);
v___x_809_ = v_reuseFailAlloc_822_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
v_isSharedCheck_816_ = !lean_is_exclusive(v_l_598_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; lean_object* v_unused_821_; 
v_unused_817_ = lean_ctor_get(v_l_598_, 4);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_l_598_, 3);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_l_598_, 2);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_l_598_, 1);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_l_598_, 0);
lean_dec(v_unused_821_);
v___x_811_ = v_l_598_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_dec(v_l_598_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 4, v_r_751_);
lean_ctor_set(v___x_811_, 3, v___x_809_);
lean_ctor_set(v___x_811_, 2, v_v_749_);
lean_ctor_set(v___x_811_, 1, v_k_748_);
lean_ctor_set(v___x_811_, 0, v___x_806_);
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_k_748_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_v_749_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_r_751_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_829_; 
v_l_829_ = lean_ctor_get(v_impl_744_, 3);
lean_inc(v_l_829_);
if (lean_obj_tag(v_l_829_) == 0)
{
lean_object* v_r_830_; lean_object* v_k_831_; lean_object* v_v_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_855_; 
v_r_830_ = lean_ctor_get(v_impl_744_, 4);
v_k_831_ = lean_ctor_get(v_impl_744_, 1);
v_v_832_ = lean_ctor_get(v_impl_744_, 2);
v_isSharedCheck_855_ = !lean_is_exclusive(v_impl_744_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; lean_object* v_unused_857_; 
v_unused_856_ = lean_ctor_get(v_impl_744_, 3);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_impl_744_, 0);
lean_dec(v_unused_857_);
v___x_834_ = v_impl_744_;
v_isShared_835_ = v_isSharedCheck_855_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_r_830_);
lean_inc(v_v_832_);
lean_inc(v_k_831_);
lean_dec(v_impl_744_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_855_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_k_836_; lean_object* v_v_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_851_; 
v_k_836_ = lean_ctor_get(v_l_829_, 1);
v_v_837_ = lean_ctor_get(v_l_829_, 2);
v_isSharedCheck_851_ = !lean_is_exclusive(v_l_829_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; lean_object* v_unused_853_; lean_object* v_unused_854_; 
v_unused_852_ = lean_ctor_get(v_l_829_, 4);
lean_dec(v_unused_852_);
v_unused_853_ = lean_ctor_get(v_l_829_, 3);
lean_dec(v_unused_853_);
v_unused_854_ = lean_ctor_get(v_l_829_, 0);
lean_dec(v_unused_854_);
v___x_839_ = v_l_829_;
v_isShared_840_ = v_isSharedCheck_851_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_v_837_);
lean_inc(v_k_836_);
lean_dec(v_l_829_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_851_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_830_, 2);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 4, v_r_830_);
lean_ctor_set(v___x_839_, 3, v_r_830_);
lean_ctor_set(v___x_839_, 2, v_v_597_);
lean_ctor_set(v___x_839_, 1, v_k_596_);
lean_ctor_set(v___x_839_, 0, v___x_745_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v_r_830_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v_r_830_);
v___x_843_ = v_reuseFailAlloc_850_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_845_; 
lean_inc(v_r_830_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 3, v_r_830_);
lean_ctor_set(v___x_834_, 0, v___x_745_);
v___x_845_ = v___x_834_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_k_831_);
lean_ctor_set(v_reuseFailAlloc_849_, 2, v_v_832_);
lean_ctor_set(v_reuseFailAlloc_849_, 3, v_r_830_);
lean_ctor_set(v_reuseFailAlloc_849_, 4, v_r_830_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v___x_845_);
lean_ctor_set(v___x_601_, 3, v___x_843_);
lean_ctor_set(v___x_601_, 2, v_v_837_);
lean_ctor_set(v___x_601_, 1, v_k_836_);
lean_ctor_set(v___x_601_, 0, v___x_841_);
v___x_847_ = v___x_601_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_k_836_);
lean_ctor_set(v_reuseFailAlloc_848_, 2, v_v_837_);
lean_ctor_set(v_reuseFailAlloc_848_, 3, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_848_, 4, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
else
{
lean_object* v_r_858_; 
v_r_858_ = lean_ctor_get(v_impl_744_, 4);
lean_inc(v_r_858_);
if (lean_obj_tag(v_r_858_) == 0)
{
lean_object* v_k_859_; lean_object* v_v_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_871_; 
v_k_859_ = lean_ctor_get(v_impl_744_, 1);
v_v_860_ = lean_ctor_get(v_impl_744_, 2);
v_isSharedCheck_871_ = !lean_is_exclusive(v_impl_744_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; lean_object* v_unused_873_; lean_object* v_unused_874_; 
v_unused_872_ = lean_ctor_get(v_impl_744_, 4);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_impl_744_, 3);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_impl_744_, 0);
lean_dec(v_unused_874_);
v___x_862_ = v_impl_744_;
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_v_860_);
lean_inc(v_k_859_);
lean_dec(v_impl_744_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = lean_unsigned_to_nat(3u);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 4, v_l_829_);
lean_ctor_set(v___x_862_, 2, v_v_597_);
lean_ctor_set(v___x_862_, 1, v_k_596_);
lean_ctor_set(v___x_862_, 0, v___x_745_);
v___x_866_ = v___x_862_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_l_829_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_l_829_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v_r_858_);
lean_ctor_set(v___x_601_, 3, v___x_866_);
lean_ctor_set(v___x_601_, 2, v_v_860_);
lean_ctor_set(v___x_601_, 1, v_k_859_);
lean_ctor_set(v___x_601_, 0, v___x_864_);
v___x_868_ = v___x_601_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_k_859_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_v_860_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v_r_858_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = lean_unsigned_to_nat(2u);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v_impl_744_);
lean_ctor_set(v___x_601_, 3, v_r_858_);
lean_ctor_set(v___x_601_, 0, v___x_875_);
v___x_877_ = v___x_601_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v_r_858_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v_impl_744_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
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
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_unsigned_to_nat(1u);
v___x_881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v_k_592_);
lean_ctor_set(v___x_881_, 2, v_v_593_);
lean_ctor_set(v___x_881_, 3, v_t_594_);
lean_ctor_set(v___x_881_, 4, v_t_594_);
return v___x_881_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(lean_object* v_m_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_buckets_884_; lean_object* v___x_885_; uint64_t v___x_886_; uint64_t v___x_887_; uint64_t v___x_888_; uint64_t v_fold_889_; uint64_t v___x_890_; uint64_t v___x_891_; uint64_t v___x_892_; size_t v___x_893_; size_t v___x_894_; size_t v___x_895_; size_t v___x_896_; size_t v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_buckets_884_ = lean_ctor_get(v_m_882_, 1);
v___x_885_ = lean_array_get_size(v_buckets_884_);
v___x_886_ = l_Lean_instHashableFVarId_hash(v_a_883_);
v___x_887_ = 32ULL;
v___x_888_ = lean_uint64_shift_right(v___x_886_, v___x_887_);
v_fold_889_ = lean_uint64_xor(v___x_886_, v___x_888_);
v___x_890_ = 16ULL;
v___x_891_ = lean_uint64_shift_right(v_fold_889_, v___x_890_);
v___x_892_ = lean_uint64_xor(v_fold_889_, v___x_891_);
v___x_893_ = lean_uint64_to_usize(v___x_892_);
v___x_894_ = lean_usize_of_nat(v___x_885_);
v___x_895_ = ((size_t)1ULL);
v___x_896_ = lean_usize_sub(v___x_894_, v___x_895_);
v___x_897_ = lean_usize_land(v___x_893_, v___x_896_);
v___x_898_ = lean_array_uget_borrowed(v_buckets_884_, v___x_897_);
v___x_899_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_883_, v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg___boxed(lean_object* v_m_900_, lean_object* v_a_901_){
_start:
{
uint8_t v_res_902_; lean_object* v_r_903_; 
v_res_902_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_m_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec_ref(v_m_900_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(lean_object* v_ctx_904_, lean_object* v_parents_905_, lean_object* v_child_906_){
_start:
{
lean_object* v_resetTargets_907_; lean_object* v_unconditionalBorrows_908_; lean_object* v_derivedValMap_909_; lean_object* v_varMap_910_; lean_object* v_jpLiveVarMap_911_; lean_object* v_idx_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_945_; 
v_resetTargets_907_ = lean_ctor_get(v_ctx_904_, 0);
v_unconditionalBorrows_908_ = lean_ctor_get(v_ctx_904_, 1);
v_derivedValMap_909_ = lean_ctor_get(v_ctx_904_, 2);
v_varMap_910_ = lean_ctor_get(v_ctx_904_, 3);
v_jpLiveVarMap_911_ = lean_ctor_get(v_ctx_904_, 4);
v_idx_912_ = lean_ctor_get(v_ctx_904_, 5);
v_isSharedCheck_945_ = !lean_is_exclusive(v_ctx_904_);
if (v_isSharedCheck_945_ == 0)
{
v___x_914_ = v_ctx_904_;
v_isShared_915_ = v_isSharedCheck_945_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_idx_912_);
lean_inc(v_jpLiveVarMap_911_);
lean_inc(v_varMap_910_);
lean_inc(v_derivedValMap_909_);
lean_inc(v_unconditionalBorrows_908_);
lean_inc(v_resetTargets_907_);
lean_dec(v_ctx_904_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_945_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v_derivedValMap_918_; uint8_t v___x_919_; 
v___x_916_ = lean_box(0);
lean_inc_ref(v_parents_905_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_parents_905_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
lean_inc(v_child_906_);
v_derivedValMap_918_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_child_906_, v___x_917_, v_derivedValMap_909_);
v___x_919_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_resetTargets_907_, v_child_906_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_array_get_size(v_parents_905_);
v___x_922_ = lean_nat_dec_lt(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_924_; 
lean_dec(v_child_906_);
lean_dec_ref(v_parents_905_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 2, v_derivedValMap_918_);
v___x_924_ = v___x_914_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_resetTargets_907_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_unconditionalBorrows_908_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_derivedValMap_918_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_varMap_910_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v_jpLiveVarMap_911_);
lean_ctor_set(v_reuseFailAlloc_925_, 5, v_idx_912_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
else
{
uint8_t v___x_926_; 
v___x_926_ = lean_nat_dec_le(v___x_921_, v___x_921_);
if (v___x_926_ == 0)
{
if (v___x_922_ == 0)
{
lean_object* v___x_928_; 
lean_dec(v_child_906_);
lean_dec_ref(v_parents_905_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 2, v_derivedValMap_918_);
v___x_928_ = v___x_914_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_resetTargets_907_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_unconditionalBorrows_908_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_derivedValMap_918_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_varMap_910_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v_jpLiveVarMap_911_);
lean_ctor_set(v_reuseFailAlloc_929_, 5, v_idx_912_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
else
{
size_t v___x_930_; size_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_930_ = ((size_t)0ULL);
v___x_931_ = lean_usize_of_nat(v___x_921_);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(v_child_906_, v_parents_905_, v___x_930_, v___x_931_, v_derivedValMap_918_);
lean_dec_ref(v_parents_905_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 2, v___x_932_);
v___x_934_ = v___x_914_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_resetTargets_907_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_unconditionalBorrows_908_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v_varMap_910_);
lean_ctor_set(v_reuseFailAlloc_935_, 4, v_jpLiveVarMap_911_);
lean_ctor_set(v_reuseFailAlloc_935_, 5, v_idx_912_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
else
{
size_t v___x_936_; size_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_936_ = ((size_t)0ULL);
v___x_937_ = lean_usize_of_nat(v___x_921_);
v___x_938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(v_child_906_, v_parents_905_, v___x_936_, v___x_937_, v_derivedValMap_918_);
lean_dec_ref(v_parents_905_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 2, v___x_938_);
v___x_940_ = v___x_914_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_resetTargets_907_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_unconditionalBorrows_908_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_varMap_910_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_jpLiveVarMap_911_);
lean_ctor_set(v_reuseFailAlloc_941_, 5, v_idx_912_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
else
{
lean_object* v___x_943_; 
lean_dec(v_child_906_);
lean_dec_ref(v_parents_905_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 2, v_derivedValMap_918_);
v___x_943_ = v___x_914_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_resetTargets_907_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_unconditionalBorrows_908_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_derivedValMap_918_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v_varMap_910_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v_jpLiveVarMap_911_);
lean_ctor_set(v_reuseFailAlloc_944_, 5, v_idx_912_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1(lean_object* v_00_u03b2_946_, lean_object* v_k_947_, lean_object* v_v_948_, lean_object* v_t_949_, lean_object* v_hl_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_k_947_, v_v_948_, v_t_949_);
return v___x_951_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2(lean_object* v_00_u03b2_952_, lean_object* v_m_953_, lean_object* v_a_954_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_m_953_, v_a_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___boxed(lean_object* v_00_u03b2_956_, lean_object* v_m_957_, lean_object* v_a_958_){
_start:
{
uint8_t v_res_959_; lean_object* v_r_960_; 
v_res_959_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2(v_00_u03b2_956_, v_m_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec_ref(v_m_957_);
v_r_960_ = lean_box(v_res_959_);
return v_r_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(lean_object* v_ctx_961_, lean_object* v_fvarId_962_){
_start:
{
lean_object* v_resetTargets_963_; lean_object* v_unconditionalBorrows_964_; lean_object* v_derivedValMap_965_; lean_object* v_varMap_966_; lean_object* v_jpLiveVarMap_967_; lean_object* v_idx_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_976_; 
v_resetTargets_963_ = lean_ctor_get(v_ctx_961_, 0);
v_unconditionalBorrows_964_ = lean_ctor_get(v_ctx_961_, 1);
v_derivedValMap_965_ = lean_ctor_get(v_ctx_961_, 2);
v_varMap_966_ = lean_ctor_get(v_ctx_961_, 3);
v_jpLiveVarMap_967_ = lean_ctor_get(v_ctx_961_, 4);
v_idx_968_ = lean_ctor_get(v_ctx_961_, 5);
v_isSharedCheck_976_ = !lean_is_exclusive(v_ctx_961_);
if (v_isSharedCheck_976_ == 0)
{
v___x_970_ = v_ctx_961_;
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_idx_968_);
lean_inc(v_jpLiveVarMap_967_);
lean_inc(v_varMap_966_);
lean_inc(v_derivedValMap_965_);
lean_inc(v_unconditionalBorrows_964_);
lean_inc(v_resetTargets_963_);
lean_dec(v_ctx_961_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_976_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_972_, 0, v_fvarId_962_);
lean_ctor_set(v___x_972_, 1, v_unconditionalBorrows_964_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_resetTargets_963_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_derivedValMap_965_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_varMap_966_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_jpLiveVarMap_967_);
lean_ctor_set(v_reuseFailAlloc_975_, 5, v_idx_968_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(lean_object* v_t_977_, lean_object* v_k_978_){
_start:
{
if (lean_obj_tag(v_t_977_) == 0)
{
lean_object* v_k_979_; lean_object* v_v_980_; lean_object* v_l_981_; lean_object* v_r_982_; uint8_t v___x_983_; 
v_k_979_ = lean_ctor_get(v_t_977_, 1);
v_v_980_ = lean_ctor_get(v_t_977_, 2);
v_l_981_ = lean_ctor_get(v_t_977_, 3);
v_r_982_ = lean_ctor_get(v_t_977_, 4);
v___x_983_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_978_, v_k_979_);
switch(v___x_983_)
{
case 0:
{
v_t_977_ = v_l_981_;
goto _start;
}
case 1:
{
lean_object* v___x_985_; 
lean_inc(v_v_980_);
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v_v_980_);
return v___x_985_;
}
default: 
{
v_t_977_ = v_r_982_;
goto _start;
}
}
}
else
{
lean_object* v___x_987_; 
v___x_987_ = lean_box(0);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg___boxed(lean_object* v_t_988_, lean_object* v_k_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_t_988_, v_k_989_);
lean_dec(v_k_989_);
lean_dec(v_t_988_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(lean_object* v_ctx_991_, lean_object* v_as_992_, size_t v_i_993_, size_t v_stop_994_, lean_object* v_b_995_){
_start:
{
lean_object* v___y_997_; uint8_t v___x_1001_; 
v___x_1001_ = lean_usize_dec_eq(v_i_993_, v_stop_994_);
if (v___x_1001_ == 0)
{
lean_object* v_varMap_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_varMap_1002_ = lean_ctor_get(v_ctx_991_, 3);
v___x_1003_ = lean_array_uget_borrowed(v_as_992_, v_i_993_);
v___x_1004_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_varMap_1002_, v___x_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
v___y_997_ = v_b_995_;
goto v___jp_996_;
}
else
{
lean_object* v_val_1005_; uint8_t v_isPossibleRef_1006_; 
v_val_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v_isPossibleRef_1006_ = lean_ctor_get_uint8(v_val_1005_, sizeof(void*)*2);
lean_dec(v_val_1005_);
if (v_isPossibleRef_1006_ == 0)
{
v___y_997_ = v_b_995_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1007_; 
lean_inc(v___x_1003_);
v___x_1007_ = lean_array_push(v_b_995_, v___x_1003_);
v___y_997_ = v___x_1007_;
goto v___jp_996_;
}
}
}
else
{
return v_b_995_;
}
v___jp_996_:
{
size_t v___x_998_; size_t v___x_999_; 
v___x_998_ = ((size_t)1ULL);
v___x_999_ = lean_usize_add(v_i_993_, v___x_998_);
v_i_993_ = v___x_999_;
v_b_995_ = v___y_997_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1___boxed(lean_object* v_ctx_1008_, lean_object* v_as_1009_, lean_object* v_i_1010_, lean_object* v_stop_1011_, lean_object* v_b_1012_){
_start:
{
size_t v_i_boxed_1013_; size_t v_stop_boxed_1014_; lean_object* v_res_1015_; 
v_i_boxed_1013_ = lean_unbox_usize(v_i_1010_);
lean_dec(v_i_1010_);
v_stop_boxed_1014_ = lean_unbox_usize(v_stop_1011_);
lean_dec(v_stop_1011_);
v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(v_ctx_1008_, v_as_1009_, v_i_boxed_1013_, v_stop_boxed_1014_, v_b_1012_);
lean_dec_ref(v_as_1009_);
lean_dec_ref(v_ctx_1008_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(lean_object* v_ctx_1018_, lean_object* v_parents_1019_, lean_object* v_decl_1020_){
_start:
{
lean_object* v_fvarId_1021_; lean_object* v_type_1022_; uint8_t v___x_1023_; 
v_fvarId_1021_ = lean_ctor_get(v_decl_1020_, 0);
lean_inc(v_fvarId_1021_);
v_type_1022_ = lean_ctor_get(v_decl_1020_, 2);
lean_inc_ref(v_type_1022_);
lean_dec_ref(v_decl_1020_);
v___x_1023_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1022_);
lean_dec_ref(v_type_1022_);
if (v___x_1023_ == 0)
{
lean_dec(v_fvarId_1021_);
return v_ctx_1018_;
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_array_get_size(v_parents_1019_);
v___x_1026_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1027_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
v___x_1028_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1018_, v___x_1026_, v_fvarId_1021_);
return v___x_1028_;
}
else
{
uint8_t v___x_1029_; 
v___x_1029_ = lean_nat_dec_le(v___x_1025_, v___x_1025_);
if (v___x_1029_ == 0)
{
if (v___x_1027_ == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1018_, v___x_1026_, v_fvarId_1021_);
return v___x_1030_;
}
else
{
size_t v___x_1031_; size_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1031_ = ((size_t)0ULL);
v___x_1032_ = lean_usize_of_nat(v___x_1025_);
v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(v_ctx_1018_, v_parents_1019_, v___x_1031_, v___x_1032_, v___x_1026_);
v___x_1034_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1018_, v___x_1033_, v_fvarId_1021_);
return v___x_1034_;
}
}
else
{
size_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = lean_usize_of_nat(v___x_1025_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(v_ctx_1018_, v_parents_1019_, v___x_1035_, v___x_1036_, v___x_1026_);
v___x_1038_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1018_, v___x_1037_, v_fvarId_1021_);
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___boxed(lean_object* v_ctx_1039_, lean_object* v_parents_1040_, lean_object* v_decl_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1039_, v_parents_1040_, v_decl_1041_);
lean_dec_ref(v_parents_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0(lean_object* v_00_u03b4_1043_, lean_object* v_t_1044_, lean_object* v_k_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_t_1044_, v_k_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___boxed(lean_object* v_00_u03b4_1047_, lean_object* v_t_1048_, lean_object* v_k_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0(v_00_u03b4_1047_, v_t_1048_, v_k_1049_);
lean_dec(v_k_1049_);
lean_dec(v_t_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(lean_object* v_as_1051_, size_t v_i_1052_, size_t v_stop_1053_, lean_object* v_b_1054_){
_start:
{
lean_object* v___y_1056_; uint8_t v___x_1060_; 
v___x_1060_ = lean_usize_dec_eq(v_i_1052_, v_stop_1053_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_array_uget_borrowed(v_as_1051_, v_i_1052_);
if (lean_obj_tag(v___x_1061_) == 0)
{
v___y_1056_ = v_b_1054_;
goto v___jp_1055_;
}
else
{
lean_object* v_fvarId_1062_; lean_object* v___x_1063_; 
v_fvarId_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_fvarId_1062_);
v___x_1063_ = lean_array_push(v_b_1054_, v_fvarId_1062_);
v___y_1056_ = v___x_1063_;
goto v___jp_1055_;
}
}
else
{
return v_b_1054_;
}
v___jp_1055_:
{
size_t v___x_1057_; size_t v___x_1058_; 
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_1052_, v___x_1057_);
v_i_1052_ = v___x_1058_;
v_b_1054_ = v___y_1056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0___boxed(lean_object* v_as_1064_, lean_object* v_i_1065_, lean_object* v_stop_1066_, lean_object* v_b_1067_){
_start:
{
size_t v_i_boxed_1068_; size_t v_stop_boxed_1069_; lean_object* v_res_1070_; 
v_i_boxed_1068_ = lean_unbox_usize(v_i_1065_);
lean_dec(v_i_1065_);
v_stop_boxed_1069_ = lean_unbox_usize(v_stop_1066_);
lean_dec(v_stop_1066_);
v_res_1070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1064_, v_i_boxed_1068_, v_stop_boxed_1069_, v_b_1067_);
lean_dec_ref(v_as_1064_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(lean_object* v_as_1071_, lean_object* v_start_1072_, lean_object* v_stop_1073_){
_start:
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1075_ = lean_nat_dec_lt(v_start_1072_, v_stop_1073_);
if (v___x_1075_ == 0)
{
return v___x_1074_;
}
else
{
lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = lean_array_get_size(v_as_1071_);
v___x_1077_ = lean_nat_dec_le(v_stop_1073_, v___x_1076_);
if (v___x_1077_ == 0)
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_nat_dec_lt(v_start_1072_, v___x_1076_);
if (v___x_1078_ == 0)
{
return v___x_1074_;
}
else
{
size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_usize_of_nat(v_start_1072_);
v___x_1080_ = lean_usize_of_nat(v___x_1076_);
v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1071_, v___x_1079_, v___x_1080_, v___x_1074_);
return v___x_1081_;
}
}
else
{
size_t v___x_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_usize_of_nat(v_start_1072_);
v___x_1083_ = lean_usize_of_nat(v_stop_1073_);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1071_, v___x_1082_, v___x_1083_, v___x_1074_);
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0___boxed(lean_object* v_as_1085_, lean_object* v_start_1086_, lean_object* v_stop_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(v_as_1085_, v_start_1086_, v_stop_1087_);
lean_dec(v_stop_1087_);
lean_dec(v_start_1086_);
lean_dec_ref(v_as_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(lean_object* v_ctx_1093_, lean_object* v_decl_1094_){
_start:
{
lean_object* v_args_1096_; lean_object* v_fvarId_1107_; lean_object* v_value_1108_; 
v_fvarId_1107_ = lean_ctor_get(v_decl_1094_, 0);
v_value_1108_ = lean_ctor_get(v_decl_1094_, 3);
switch(lean_obj_tag(v_value_1108_))
{
case 6:
{
lean_object* v_var_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_var_1113_ = lean_ctor_get(v_value_1108_, 1);
v___x_1114_ = lean_unsigned_to_nat(1u);
v___x_1115_ = lean_mk_empty_array_with_capacity(v___x_1114_);
lean_inc(v_var_1113_);
v___x_1116_ = lean_array_push(v___x_1115_, v_var_1113_);
v___x_1117_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1093_, v___x_1116_, v_decl_1094_);
lean_dec_ref(v___x_1116_);
return v___x_1117_;
}
case 9:
{
lean_object* v_fn_1118_; 
v_fn_1118_ = lean_ctor_get(v_value_1108_, 0);
if (lean_obj_tag(v_fn_1118_) == 1)
{
lean_object* v_pre_1119_; 
v_pre_1119_ = lean_ctor_get(v_fn_1118_, 0);
if (lean_obj_tag(v_pre_1119_) == 1)
{
lean_object* v_pre_1120_; 
v_pre_1120_ = lean_ctor_get(v_pre_1119_, 0);
if (lean_obj_tag(v_pre_1120_) == 0)
{
lean_object* v_args_1121_; lean_object* v_str_1122_; lean_object* v_str_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v_args_1121_ = lean_ctor_get(v_value_1108_, 1);
v_str_1122_ = lean_ctor_get(v_fn_1118_, 1);
v_str_1123_ = lean_ctor_get(v_pre_1119_, 1);
v___x_1124_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0));
v___x_1125_ = lean_string_dec_eq(v_str_1123_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1126_ = lean_array_get_size(v_args_1121_);
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_nat_dec_eq(v___x_1126_, v___x_1127_);
if (v___x_1128_ == 0)
{
goto v___jp_1104_;
}
else
{
lean_inc(v_fvarId_1107_);
goto v___jp_1109_;
}
}
else
{
lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__1));
v___x_1130_ = lean_string_dec_eq(v_str_1122_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__2));
v___x_1132_ = lean_string_dec_eq(v_str_1122_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__3));
v___x_1134_ = lean_string_dec_eq(v_str_1122_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1135_ = lean_array_get_size(v_args_1121_);
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = lean_nat_dec_eq(v___x_1135_, v___x_1136_);
if (v___x_1137_ == 0)
{
goto v___jp_1104_;
}
else
{
lean_inc(v_fvarId_1107_);
goto v___jp_1109_;
}
}
else
{
lean_inc_ref(v_args_1121_);
v_args_1096_ = v_args_1121_;
goto v___jp_1095_;
}
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_parents_1148_; lean_object* v___x_1149_; 
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = lean_array_get_borrowed(v___x_1138_, v_args_1121_, v___x_1139_);
v___x_1141_ = lean_unsigned_to_nat(2u);
v___x_1142_ = lean_array_get_borrowed(v___x_1138_, v_args_1121_, v___x_1141_);
v___x_1143_ = lean_mk_empty_array_with_capacity(v___x_1141_);
lean_inc(v___x_1140_);
v___x_1144_ = lean_array_push(v___x_1143_, v___x_1140_);
lean_inc(v___x_1142_);
v___x_1145_ = lean_array_push(v___x_1144_, v___x_1142_);
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = lean_array_get_size(v___x_1145_);
v_parents_1148_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(v___x_1145_, v___x_1146_, v___x_1147_);
lean_dec_ref(v___x_1145_);
v___x_1149_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1093_, v_parents_1148_, v_decl_1094_);
lean_dec_ref(v_parents_1148_);
return v___x_1149_;
}
}
else
{
lean_inc_ref(v_args_1121_);
v_args_1096_ = v_args_1121_;
goto v___jp_1095_;
}
}
}
else
{
lean_object* v_args_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_args_1150_ = lean_ctor_get(v_value_1108_, 1);
v___x_1151_ = lean_array_get_size(v_args_1150_);
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = lean_nat_dec_eq(v___x_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
goto v___jp_1104_;
}
else
{
lean_inc(v_fvarId_1107_);
goto v___jp_1109_;
}
}
}
else
{
lean_object* v_args_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_args_1154_ = lean_ctor_get(v_value_1108_, 1);
v___x_1155_ = lean_array_get_size(v_args_1154_);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_nat_dec_eq(v___x_1155_, v___x_1156_);
if (v___x_1157_ == 0)
{
goto v___jp_1104_;
}
else
{
lean_inc(v_fvarId_1107_);
goto v___jp_1109_;
}
}
}
else
{
lean_object* v_args_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v_args_1158_ = lean_ctor_get(v_value_1108_, 1);
v___x_1159_ = lean_array_get_size(v_args_1158_);
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_nat_dec_eq(v___x_1159_, v___x_1160_);
if (v___x_1161_ == 0)
{
goto v___jp_1104_;
}
else
{
lean_inc(v_fvarId_1107_);
goto v___jp_1109_;
}
}
}
case 5:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1163_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1093_, v___x_1162_, v_decl_1094_);
return v___x_1163_;
}
case 12:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1165_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1093_, v___x_1164_, v_decl_1094_);
return v___x_1165_;
}
default: 
{
lean_dec_ref(v_decl_1094_);
return v_ctx_1093_;
}
}
v___jp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = lean_array_get(v___x_1097_, v_args_1096_, v___x_1098_);
lean_dec_ref(v_args_1096_);
if (lean_obj_tag(v___x_1099_) == 1)
{
lean_object* v_fvarId_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_fvarId_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_fvarId_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1101_ = lean_mk_empty_array_with_capacity(v___x_1098_);
v___x_1102_ = lean_array_push(v___x_1101_, v_fvarId_1100_);
v___x_1103_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1093_, v___x_1102_, v_decl_1094_);
lean_dec_ref(v___x_1102_);
return v___x_1103_;
}
else
{
lean_dec(v___x_1099_);
lean_dec_ref(v_decl_1094_);
return v_ctx_1093_;
}
}
v___jp_1104_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1106_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1093_, v___x_1105_, v_decl_1094_);
return v___x_1106_;
}
v___jp_1109_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1111_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1093_, v___x_1110_, v_decl_1094_);
v___x_1112_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(v___x_1111_, v_fvarId_1107_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___lam__0(lean_object* v_x1_1166_, lean_object* v_x2_1167_){
_start:
{
lean_object* v_resetTargets_1168_; lean_object* v_unconditionalBorrows_1169_; lean_object* v_derivedValMap_1170_; lean_object* v_varMap_1171_; lean_object* v_jpLiveVarMap_1172_; lean_object* v_idx_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1194_; 
v_resetTargets_1168_ = lean_ctor_get(v_x1_1166_, 0);
v_unconditionalBorrows_1169_ = lean_ctor_get(v_x1_1166_, 1);
v_derivedValMap_1170_ = lean_ctor_get(v_x1_1166_, 2);
v_varMap_1171_ = lean_ctor_get(v_x1_1166_, 3);
v_jpLiveVarMap_1172_ = lean_ctor_get(v_x1_1166_, 4);
v_idx_1173_ = lean_ctor_get(v_x1_1166_, 5);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_x1_1166_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1175_ = v_x1_1166_;
v_isShared_1176_ = v_isSharedCheck_1194_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_idx_1173_);
lean_inc(v_jpLiveVarMap_1172_);
lean_inc(v_varMap_1171_);
lean_inc(v_derivedValMap_1170_);
lean_inc(v_unconditionalBorrows_1169_);
lean_inc(v_resetTargets_1168_);
lean_dec(v_x1_1166_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1194_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_fvarId_1177_; lean_object* v_type_1178_; uint8_t v_borrow_1179_; uint8_t v___x_1180_; uint8_t v___x_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v_varMap_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v_ctx_1189_; 
v_fvarId_1177_ = lean_ctor_get(v_x2_1167_, 0);
lean_inc_n(v_fvarId_1177_, 2);
v_type_1178_ = lean_ctor_get(v_x2_1167_, 2);
lean_inc_ref(v_type_1178_);
v_borrow_1179_ = lean_ctor_get_uint8(v_x2_1167_, sizeof(void*)*3);
lean_dec_ref(v_x2_1167_);
v___x_1180_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1178_);
v___x_1181_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1178_);
lean_dec_ref(v_type_1178_);
v___x_1182_ = 0;
v___x_1183_ = lean_box(0);
lean_inc(v_idx_1173_);
v___x_1184_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1184_, 0, v_idx_1173_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*2, v___x_1180_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*2 + 1, v___x_1181_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*2 + 2, v___x_1182_);
v_varMap_1185_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1177_, v___x_1184_, v_varMap_1171_);
v___x_1186_ = lean_unsigned_to_nat(1u);
v___x_1187_ = lean_nat_add(v_idx_1173_, v___x_1186_);
lean_dec(v_idx_1173_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 5, v___x_1187_);
lean_ctor_set(v___x_1175_, 3, v_varMap_1185_);
v_ctx_1189_ = v___x_1175_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_resetTargets_1168_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_unconditionalBorrows_1169_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_derivedValMap_1170_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_varMap_1185_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_jpLiveVarMap_1172_);
lean_ctor_set(v_reuseFailAlloc_1193_, 5, v___x_1187_);
v_ctx_1189_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; lean_object* v_ctx_1191_; 
v___x_1190_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
lean_inc(v_fvarId_1177_);
v_ctx_1191_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1189_, v___x_1190_, v_fvarId_1177_);
if (v_borrow_1179_ == 0)
{
lean_dec(v_fvarId_1177_);
return v_ctx_1191_;
}
else
{
if (v___x_1180_ == 0)
{
lean_dec(v_fvarId_1177_);
return v_ctx_1191_;
}
else
{
lean_object* v___x_1192_; 
v___x_1192_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(v_ctx_1191_, v_fvarId_1177_);
return v___x_1192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(lean_object* v_ps_1196_, lean_object* v_x_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_array_get_size(v_ps_1196_);
v___x_1207_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v___x_1208_ = lean_nat_dec_lt(v___x_1205_, v___x_1206_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; 
lean_dec_ref(v_ps_1196_);
lean_inc(v_a_1203_);
lean_inc_ref(v_a_1202_);
lean_inc(v_a_1201_);
lean_inc_ref(v_a_1200_);
lean_inc(v_a_1199_);
lean_inc_ref(v_a_1198_);
v___x_1209_ = lean_apply_7(v_x_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, lean_box(0));
return v___x_1209_;
}
else
{
lean_object* v___f_1210_; uint8_t v___x_1211_; 
v___f_1210_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___x_1211_ = lean_nat_dec_le(v___x_1206_, v___x_1206_);
if (v___x_1211_ == 0)
{
if (v___x_1208_ == 0)
{
lean_object* v___x_1212_; 
lean_dec_ref(v_ps_1196_);
lean_inc(v_a_1203_);
lean_inc_ref(v_a_1202_);
lean_inc(v_a_1201_);
lean_inc_ref(v_a_1200_);
lean_inc(v_a_1199_);
lean_inc_ref(v_a_1198_);
v___x_1212_ = lean_apply_7(v_x_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, lean_box(0));
return v___x_1212_;
}
else
{
size_t v___x_1213_; size_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1213_ = ((size_t)0ULL);
v___x_1214_ = lean_usize_of_nat(v___x_1206_);
lean_inc_ref(v_a_1198_);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1207_, v___f_1210_, v_ps_1196_, v___x_1213_, v___x_1214_, v_a_1198_);
lean_inc(v_a_1203_);
lean_inc_ref(v_a_1202_);
lean_inc(v_a_1201_);
lean_inc_ref(v_a_1200_);
lean_inc(v_a_1199_);
v___x_1216_ = lean_apply_7(v_x_1197_, v___x_1215_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, lean_box(0));
return v___x_1216_;
}
}
else
{
size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1217_ = ((size_t)0ULL);
v___x_1218_ = lean_usize_of_nat(v___x_1206_);
lean_inc_ref(v_a_1198_);
v___x_1219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1207_, v___f_1210_, v_ps_1196_, v___x_1217_, v___x_1218_, v_a_1198_);
lean_inc(v_a_1203_);
lean_inc_ref(v_a_1202_);
lean_inc(v_a_1201_);
lean_inc_ref(v_a_1200_);
lean_inc(v_a_1199_);
v___x_1220_ = lean_apply_7(v_x_1197_, v___x_1219_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, lean_box(0));
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___boxed(lean_object* v_ps_1221_, lean_object* v_x_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(v_ps_1221_, v_x_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(lean_object* v_00_u03b1_1231_, lean_object* v_ps_1232_, lean_object* v_x_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = lean_array_get_size(v_ps_1232_);
v___x_1243_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v___x_1244_ = lean_nat_dec_lt(v___x_1241_, v___x_1242_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
lean_dec_ref(v_ps_1232_);
lean_inc(v_a_1239_);
lean_inc_ref(v_a_1238_);
lean_inc(v_a_1237_);
lean_inc_ref(v_a_1236_);
lean_inc(v_a_1235_);
lean_inc_ref(v_a_1234_);
v___x_1245_ = lean_apply_7(v_x_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, lean_box(0));
return v___x_1245_;
}
else
{
lean_object* v___f_1246_; uint8_t v___x_1247_; 
v___f_1246_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___x_1247_ = lean_nat_dec_le(v___x_1242_, v___x_1242_);
if (v___x_1247_ == 0)
{
if (v___x_1244_ == 0)
{
lean_object* v___x_1248_; 
lean_dec_ref(v_ps_1232_);
lean_inc(v_a_1239_);
lean_inc_ref(v_a_1238_);
lean_inc(v_a_1237_);
lean_inc_ref(v_a_1236_);
lean_inc(v_a_1235_);
lean_inc_ref(v_a_1234_);
v___x_1248_ = lean_apply_7(v_x_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, lean_box(0));
return v___x_1248_;
}
else
{
size_t v___x_1249_; size_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1249_ = ((size_t)0ULL);
v___x_1250_ = lean_usize_of_nat(v___x_1242_);
lean_inc_ref(v_a_1234_);
v___x_1251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1243_, v___f_1246_, v_ps_1232_, v___x_1249_, v___x_1250_, v_a_1234_);
lean_inc(v_a_1239_);
lean_inc_ref(v_a_1238_);
lean_inc(v_a_1237_);
lean_inc_ref(v_a_1236_);
lean_inc(v_a_1235_);
v___x_1252_ = lean_apply_7(v_x_1233_, v___x_1251_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, lean_box(0));
return v___x_1252_;
}
}
else
{
size_t v___x_1253_; size_t v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1253_ = ((size_t)0ULL);
v___x_1254_ = lean_usize_of_nat(v___x_1242_);
lean_inc_ref(v_a_1234_);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1243_, v___f_1246_, v_ps_1232_, v___x_1253_, v___x_1254_, v_a_1234_);
lean_inc(v_a_1239_);
lean_inc_ref(v_a_1238_);
lean_inc(v_a_1237_);
lean_inc_ref(v_a_1236_);
lean_inc(v_a_1235_);
v___x_1256_ = lean_apply_7(v_x_1233_, v___x_1255_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, lean_box(0));
return v___x_1256_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___boxed(lean_object* v_00_u03b1_1257_, lean_object* v_ps_1258_, lean_object* v_x_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(v_00_u03b1_1257_, v_ps_1258_, v_x_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(lean_object* v_decl_1268_, lean_object* v_x_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_fvarId_1277_; lean_object* v_type_1278_; lean_object* v_value_1279_; lean_object* v___y_1281_; 
v_fvarId_1277_ = lean_ctor_get(v_decl_1268_, 0);
v_type_1278_ = lean_ctor_get(v_decl_1268_, 2);
v_value_1279_ = lean_ctor_get(v_decl_1268_, 3);
if (lean_obj_tag(v_value_1279_) == 5)
{
lean_object* v_i_1298_; lean_object* v___x_1299_; 
v_i_1298_ = lean_ctor_get(v_value_1279_, 0);
lean_inc_ref(v_i_1298_);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_i_1298_);
v___y_1281_ = v___x_1299_;
goto v___jp_1280_;
}
else
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_box(0);
v___y_1281_ = v___x_1300_;
goto v___jp_1280_;
}
v___jp_1280_:
{
lean_object* v_resetTargets_1282_; lean_object* v_unconditionalBorrows_1283_; lean_object* v_derivedValMap_1284_; lean_object* v_varMap_1285_; lean_object* v_jpLiveVarMap_1286_; lean_object* v_idx_1287_; uint8_t v___x_1288_; uint8_t v___x_1289_; uint8_t v___x_1290_; lean_object* v_varInfo_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_ctx_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_resetTargets_1282_ = lean_ctor_get(v_a_1270_, 0);
v_unconditionalBorrows_1283_ = lean_ctor_get(v_a_1270_, 1);
v_derivedValMap_1284_ = lean_ctor_get(v_a_1270_, 2);
v_varMap_1285_ = lean_ctor_get(v_a_1270_, 3);
v_jpLiveVarMap_1286_ = lean_ctor_get(v_a_1270_, 4);
v_idx_1287_ = lean_ctor_get(v_a_1270_, 5);
v___x_1288_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1278_);
v___x_1289_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1278_);
v___x_1290_ = l_Lean_Compiler_LCNF_LetValue_isPersistent(v_value_1279_);
lean_inc(v_idx_1287_);
v_varInfo_1291_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_varInfo_1291_, 0, v_idx_1287_);
lean_ctor_set(v_varInfo_1291_, 1, v___y_1281_);
lean_ctor_set_uint8(v_varInfo_1291_, sizeof(void*)*2, v___x_1288_);
lean_ctor_set_uint8(v_varInfo_1291_, sizeof(void*)*2 + 1, v___x_1289_);
lean_ctor_set_uint8(v_varInfo_1291_, sizeof(void*)*2 + 2, v___x_1290_);
lean_inc(v_varMap_1285_);
lean_inc(v_fvarId_1277_);
v___x_1292_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1277_, v_varInfo_1291_, v_varMap_1285_);
v___x_1293_ = lean_unsigned_to_nat(1u);
v___x_1294_ = lean_nat_add(v_idx_1287_, v___x_1293_);
lean_inc(v_jpLiveVarMap_1286_);
lean_inc(v_derivedValMap_1284_);
lean_inc(v_unconditionalBorrows_1283_);
lean_inc_ref(v_resetTargets_1282_);
v_ctx_1295_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_ctx_1295_, 0, v_resetTargets_1282_);
lean_ctor_set(v_ctx_1295_, 1, v_unconditionalBorrows_1283_);
lean_ctor_set(v_ctx_1295_, 2, v_derivedValMap_1284_);
lean_ctor_set(v_ctx_1295_, 3, v___x_1292_);
lean_ctor_set(v_ctx_1295_, 4, v_jpLiveVarMap_1286_);
lean_ctor_set(v_ctx_1295_, 5, v___x_1294_);
v___x_1296_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(v_ctx_1295_, v_decl_1268_);
lean_inc(v_a_1275_);
lean_inc_ref(v_a_1274_);
lean_inc(v_a_1273_);
lean_inc_ref(v_a_1272_);
lean_inc(v_a_1271_);
v___x_1297_ = lean_apply_7(v_x_1269_, v___x_1296_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, lean_box(0));
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg___boxed(lean_object* v_decl_1301_, lean_object* v_x_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(v_decl_1301_, v_x_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(lean_object* v_00_u03b1_1311_, lean_object* v_decl_1312_, lean_object* v_x_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_fvarId_1321_; lean_object* v_type_1322_; lean_object* v_value_1323_; lean_object* v___y_1325_; 
v_fvarId_1321_ = lean_ctor_get(v_decl_1312_, 0);
v_type_1322_ = lean_ctor_get(v_decl_1312_, 2);
v_value_1323_ = lean_ctor_get(v_decl_1312_, 3);
if (lean_obj_tag(v_value_1323_) == 5)
{
lean_object* v_i_1342_; lean_object* v___x_1343_; 
v_i_1342_ = lean_ctor_get(v_value_1323_, 0);
lean_inc_ref(v_i_1342_);
v___x_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_i_1342_);
v___y_1325_ = v___x_1343_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_box(0);
v___y_1325_ = v___x_1344_;
goto v___jp_1324_;
}
v___jp_1324_:
{
lean_object* v_resetTargets_1326_; lean_object* v_unconditionalBorrows_1327_; lean_object* v_derivedValMap_1328_; lean_object* v_varMap_1329_; lean_object* v_jpLiveVarMap_1330_; lean_object* v_idx_1331_; uint8_t v___x_1332_; uint8_t v___x_1333_; uint8_t v___x_1334_; lean_object* v_varInfo_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v_ctx_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_resetTargets_1326_ = lean_ctor_get(v_a_1314_, 0);
v_unconditionalBorrows_1327_ = lean_ctor_get(v_a_1314_, 1);
v_derivedValMap_1328_ = lean_ctor_get(v_a_1314_, 2);
v_varMap_1329_ = lean_ctor_get(v_a_1314_, 3);
v_jpLiveVarMap_1330_ = lean_ctor_get(v_a_1314_, 4);
v_idx_1331_ = lean_ctor_get(v_a_1314_, 5);
v___x_1332_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1322_);
v___x_1333_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1322_);
v___x_1334_ = l_Lean_Compiler_LCNF_LetValue_isPersistent(v_value_1323_);
lean_inc(v_idx_1331_);
v_varInfo_1335_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_varInfo_1335_, 0, v_idx_1331_);
lean_ctor_set(v_varInfo_1335_, 1, v___y_1325_);
lean_ctor_set_uint8(v_varInfo_1335_, sizeof(void*)*2, v___x_1332_);
lean_ctor_set_uint8(v_varInfo_1335_, sizeof(void*)*2 + 1, v___x_1333_);
lean_ctor_set_uint8(v_varInfo_1335_, sizeof(void*)*2 + 2, v___x_1334_);
lean_inc(v_varMap_1329_);
lean_inc(v_fvarId_1321_);
v___x_1336_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1321_, v_varInfo_1335_, v_varMap_1329_);
v___x_1337_ = lean_unsigned_to_nat(1u);
v___x_1338_ = lean_nat_add(v_idx_1331_, v___x_1337_);
lean_inc(v_jpLiveVarMap_1330_);
lean_inc(v_derivedValMap_1328_);
lean_inc(v_unconditionalBorrows_1327_);
lean_inc_ref(v_resetTargets_1326_);
v_ctx_1339_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_ctx_1339_, 0, v_resetTargets_1326_);
lean_ctor_set(v_ctx_1339_, 1, v_unconditionalBorrows_1327_);
lean_ctor_set(v_ctx_1339_, 2, v_derivedValMap_1328_);
lean_ctor_set(v_ctx_1339_, 3, v___x_1336_);
lean_ctor_set(v_ctx_1339_, 4, v_jpLiveVarMap_1330_);
lean_ctor_set(v_ctx_1339_, 5, v___x_1338_);
v___x_1340_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(v_ctx_1339_, v_decl_1312_);
lean_inc(v_a_1319_);
lean_inc_ref(v_a_1318_);
lean_inc(v_a_1317_);
lean_inc_ref(v_a_1316_);
lean_inc(v_a_1315_);
v___x_1341_ = lean_apply_7(v_x_1313_, v___x_1340_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, lean_box(0));
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_decl_1346_, lean_object* v_x_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(v_00_u03b1_1345_, v_decl_1346_, v_x_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(lean_object* v_discr_1356_, lean_object* v_c_1357_, lean_object* v_x_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_resetTargets_1366_; lean_object* v_unconditionalBorrows_1367_; lean_object* v_derivedValMap_1368_; lean_object* v_varMap_1369_; lean_object* v_jpLiveVarMap_1370_; lean_object* v_idx_1371_; lean_object* v___y_1373_; lean_object* v___f_1378_; lean_object* v___x_1379_; 
v_resetTargets_1366_ = lean_ctor_get(v_a_1359_, 0);
v_unconditionalBorrows_1367_ = lean_ctor_get(v_a_1359_, 1);
v_derivedValMap_1368_ = lean_ctor_get(v_a_1359_, 2);
v_varMap_1369_ = lean_ctor_get(v_a_1359_, 3);
v_jpLiveVarMap_1370_ = lean_ctor_get(v_a_1359_, 4);
v_idx_1371_ = lean_ctor_get(v_a_1359_, 5);
v___f_1378_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_discr_1356_);
lean_inc(v_varMap_1369_);
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1378_, v_varMap_1369_, v_discr_1356_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_dec_ref(v_c_1357_);
lean_dec(v_discr_1356_);
lean_inc(v_varMap_1369_);
v___y_1373_ = v_varMap_1369_;
goto v___jp_1372_;
}
else
{
lean_object* v_val_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1401_; 
v_val_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1401_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_val_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1401_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
uint8_t v_persistent_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1398_; 
v_persistent_1384_ = lean_ctor_get_uint8(v_val_1380_, sizeof(void*)*2 + 2);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_val_1380_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1399_ = lean_ctor_get(v_val_1380_, 1);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_val_1380_, 0);
lean_dec(v_unused_1400_);
v___x_1386_ = v_val_1380_;
v_isShared_1387_ = v_isSharedCheck_1398_;
goto v_resetjp_1385_;
}
else
{
lean_dec(v_val_1380_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1398_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1388_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_c_1357_);
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = lean_nat_add(v_idx_1371_, v___x_1389_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v_c_1357_);
v___x_1392_ = v___x_1382_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_c_1357_);
v___x_1392_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1394_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v___x_1392_);
lean_ctor_set(v___x_1386_, 0, v___x_1390_);
v___x_1394_ = v___x_1386_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1396_, sizeof(void*)*2 + 2, v_persistent_1384_);
v___x_1394_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; 
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*2, v___x_1388_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*2 + 1, v___x_1388_);
lean_inc(v_varMap_1369_);
v___x_1395_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_1356_, v___x_1394_, v_varMap_1369_);
v___y_1373_ = v___x_1395_;
goto v___jp_1372_;
}
}
}
}
}
v___jp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = lean_nat_add(v_idx_1371_, v___x_1374_);
lean_inc(v_jpLiveVarMap_1370_);
lean_inc(v_derivedValMap_1368_);
lean_inc(v_unconditionalBorrows_1367_);
lean_inc_ref(v_resetTargets_1366_);
v___x_1376_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1376_, 0, v_resetTargets_1366_);
lean_ctor_set(v___x_1376_, 1, v_unconditionalBorrows_1367_);
lean_ctor_set(v___x_1376_, 2, v_derivedValMap_1368_);
lean_ctor_set(v___x_1376_, 3, v___y_1373_);
lean_ctor_set(v___x_1376_, 4, v_jpLiveVarMap_1370_);
lean_ctor_set(v___x_1376_, 5, v___x_1375_);
lean_inc(v_a_1364_);
lean_inc_ref(v_a_1363_);
lean_inc(v_a_1362_);
lean_inc_ref(v_a_1361_);
lean_inc(v_a_1360_);
v___x_1377_ = lean_apply_7(v_x_1358_, v___x_1376_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, lean_box(0));
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg___boxed(lean_object* v_discr_1402_, lean_object* v_c_1403_, lean_object* v_x_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(v_discr_1402_, v_c_1403_, v_x_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(lean_object* v_00_u03b1_1413_, lean_object* v_discr_1414_, lean_object* v_c_1415_, lean_object* v_x_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_resetTargets_1424_; lean_object* v_unconditionalBorrows_1425_; lean_object* v_derivedValMap_1426_; lean_object* v_varMap_1427_; lean_object* v_jpLiveVarMap_1428_; lean_object* v_idx_1429_; lean_object* v___y_1431_; lean_object* v___f_1436_; lean_object* v___x_1437_; 
v_resetTargets_1424_ = lean_ctor_get(v_a_1417_, 0);
v_unconditionalBorrows_1425_ = lean_ctor_get(v_a_1417_, 1);
v_derivedValMap_1426_ = lean_ctor_get(v_a_1417_, 2);
v_varMap_1427_ = lean_ctor_get(v_a_1417_, 3);
v_jpLiveVarMap_1428_ = lean_ctor_get(v_a_1417_, 4);
v_idx_1429_ = lean_ctor_get(v_a_1417_, 5);
v___f_1436_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_discr_1414_);
lean_inc(v_varMap_1427_);
v___x_1437_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1436_, v_varMap_1427_, v_discr_1414_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_dec_ref(v_c_1415_);
lean_dec(v_discr_1414_);
lean_inc(v_varMap_1427_);
v___y_1431_ = v_varMap_1427_;
goto v___jp_1430_;
}
else
{
lean_object* v_val_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1459_; 
v_val_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1459_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_val_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1459_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
uint8_t v_persistent_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1456_; 
v_persistent_1442_ = lean_ctor_get_uint8(v_val_1438_, sizeof(void*)*2 + 2);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_val_1438_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; lean_object* v_unused_1458_; 
v_unused_1457_ = lean_ctor_get(v_val_1438_, 1);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_val_1438_, 0);
lean_dec(v_unused_1458_);
v___x_1444_ = v_val_1438_;
v_isShared_1445_ = v_isSharedCheck_1456_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v_val_1438_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1456_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
uint8_t v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1446_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_c_1415_);
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_nat_add(v_idx_1429_, v___x_1447_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_c_1415_);
v___x_1450_ = v___x_1440_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_c_1415_);
v___x_1450_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v___x_1450_);
lean_ctor_set(v___x_1444_, 0, v___x_1448_);
v___x_1452_ = v___x_1444_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1450_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*2 + 2, v_persistent_1442_);
v___x_1452_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; 
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*2, v___x_1446_);
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*2 + 1, v___x_1446_);
lean_inc(v_varMap_1427_);
v___x_1453_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_1414_, v___x_1452_, v_varMap_1427_);
v___y_1431_ = v___x_1453_;
goto v___jp_1430_;
}
}
}
}
}
v___jp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1432_ = lean_unsigned_to_nat(1u);
v___x_1433_ = lean_nat_add(v_idx_1429_, v___x_1432_);
lean_inc(v_jpLiveVarMap_1428_);
lean_inc(v_derivedValMap_1426_);
lean_inc(v_unconditionalBorrows_1425_);
lean_inc_ref(v_resetTargets_1424_);
v___x_1434_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1434_, 0, v_resetTargets_1424_);
lean_ctor_set(v___x_1434_, 1, v_unconditionalBorrows_1425_);
lean_ctor_set(v___x_1434_, 2, v_derivedValMap_1426_);
lean_ctor_set(v___x_1434_, 3, v___y_1431_);
lean_ctor_set(v___x_1434_, 4, v_jpLiveVarMap_1428_);
lean_ctor_set(v___x_1434_, 5, v___x_1433_);
lean_inc(v_a_1422_);
lean_inc_ref(v_a_1421_);
lean_inc(v_a_1420_);
lean_inc_ref(v_a_1419_);
lean_inc(v_a_1418_);
v___x_1435_ = lean_apply_7(v_x_1416_, v___x_1434_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, lean_box(0));
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___boxed(lean_object* v_00_u03b1_1460_, lean_object* v_discr_1461_, lean_object* v_c_1462_, lean_object* v_x_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(v_00_u03b1_1460_, v_discr_1461_, v_c_1462_, v_x_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(lean_object* v_x_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1480_ = lean_st_ref_get(v_a_1474_);
v___x_1481_ = lean_st_ref_take(v_a_1474_);
lean_dec(v___x_1481_);
v___x_1482_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_1483_ = lean_st_ref_put(v_a_1474_, v___x_1482_);
lean_inc(v_a_1478_);
lean_inc_ref(v_a_1477_);
lean_inc(v_a_1476_);
lean_inc_ref(v_a_1475_);
lean_inc(v_a_1474_);
lean_inc_ref(v_a_1473_);
v___x_1484_ = lean_apply_7(v_x_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, lean_box(0));
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1496_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1496_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1496_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1489_ = lean_st_ref_get(v_a_1474_);
v___x_1490_ = lean_st_ref_take(v_a_1474_);
lean_dec(v___x_1490_);
v___x_1491_ = lean_st_ref_put(v_a_1474_, v___x_1480_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_a_1485_);
lean_ctor_set(v___x_1492_, 1, v___x_1489_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1492_);
v___x_1494_ = v___x_1487_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec(v___x_1480_);
v_a_1497_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1484_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1484_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg___boxed(lean_object* v_x_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(v_x_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(lean_object* v_00_u03b1_1514_, lean_object* v_x_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1523_ = lean_st_ref_get(v_a_1517_);
v___x_1524_ = lean_st_ref_take(v_a_1517_);
lean_dec(v___x_1524_);
v___x_1525_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_1526_ = lean_st_ref_put(v_a_1517_, v___x_1525_);
lean_inc(v_a_1521_);
lean_inc_ref(v_a_1520_);
lean_inc(v_a_1519_);
lean_inc_ref(v_a_1518_);
lean_inc(v_a_1517_);
lean_inc_ref(v_a_1516_);
v___x_1527_ = lean_apply_7(v_x_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, lean_box(0));
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1539_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1539_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1539_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1532_ = lean_st_ref_get(v_a_1517_);
v___x_1533_ = lean_st_ref_take(v_a_1517_);
lean_dec(v___x_1533_);
v___x_1534_ = lean_st_ref_put(v_a_1517_, v___x_1523_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v_a_1528_);
lean_ctor_set(v___x_1535_, 1, v___x_1532_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1535_);
v___x_1537_ = v___x_1530_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec(v___x_1523_);
v_a_1540_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1527_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1527_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___boxed(lean_object* v_00_u03b1_1548_, lean_object* v_x_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(v_00_u03b1_1548_, v_x_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
return v_res_1557_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0(lean_object* v_liveVars_1558_, uint8_t v___x_1559_, lean_object* v___x_1560_, lean_object* v___x_1561_, lean_object* v_v_1562_){
_start:
{
uint8_t v___y_1564_; lean_object* v_vars_1566_; lean_object* v_borrows_1567_; uint8_t v___x_1568_; 
v_vars_1566_ = lean_ctor_get(v_liveVars_1558_, 0);
v_borrows_1567_ = lean_ctor_get(v_liveVars_1558_, 1);
lean_inc(v_v_1562_);
lean_inc_ref(v___x_1561_);
lean_inc_ref(v___x_1560_);
v___x_1568_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1560_, v___x_1561_, v_vars_1566_, v_v_1562_);
if (v___x_1568_ == 0)
{
uint8_t v___x_1569_; 
v___x_1569_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1560_, v___x_1561_, v_borrows_1567_, v_v_1562_);
v___y_1564_ = v___x_1569_;
goto v___jp_1563_;
}
else
{
lean_dec(v_v_1562_);
lean_dec_ref(v___x_1561_);
lean_dec_ref(v___x_1560_);
v___y_1564_ = v___x_1568_;
goto v___jp_1563_;
}
v___jp_1563_:
{
if (v___y_1564_ == 0)
{
return v___x_1559_;
}
else
{
uint8_t v___x_1565_; 
v___x_1565_ = 0;
return v___x_1565_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0___boxed(lean_object* v_liveVars_1570_, lean_object* v___x_1571_, lean_object* v___x_1572_, lean_object* v___x_1573_, lean_object* v_v_1574_){
_start:
{
uint8_t v___x_362__boxed_1575_; uint8_t v_res_1576_; lean_object* v_r_1577_; 
v___x_362__boxed_1575_ = lean_unbox(v___x_1571_);
v_res_1576_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0(v_liveVars_1570_, v___x_362__boxed_1575_, v___x_1572_, v___x_1573_, v_v_1574_);
lean_dec_ref(v_liveVars_1570_);
v_r_1577_ = lean_box(v_res_1576_);
return v_r_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1(lean_object* v___f_1578_, lean_object* v___x_1579_, lean_object* v_derivedValMap_1580_, lean_object* v_shouldAdd_1581_, lean_object* v___x_1582_, lean_object* v___x_1583_, lean_object* v_liveVars_1584_, lean_object* v_child_1585_){
_start:
{
lean_object* v_cinfo_1602_; lean_object* v_parents_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
lean_inc(v_child_1585_);
lean_inc(v_derivedValMap_1580_);
v_cinfo_1602_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_1578_, v___x_1579_, v_derivedValMap_1580_, v_child_1585_);
v_parents_1603_ = lean_ctor_get(v_cinfo_1602_, 0);
lean_inc_ref(v_parents_1603_);
lean_dec(v_cinfo_1602_);
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = lean_array_get_size(v_parents_1603_);
v___x_1606_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v___x_1607_ = lean_nat_dec_lt(v___x_1604_, v___x_1605_);
if (v___x_1607_ == 0)
{
lean_dec_ref(v_parents_1603_);
goto v___jp_1586_;
}
else
{
if (v___x_1607_ == 0)
{
lean_dec_ref(v_parents_1603_);
goto v___jp_1586_;
}
else
{
lean_object* v___x_1608_; lean_object* v___f_1609_; size_t v___x_1610_; size_t v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1608_ = lean_box(v___x_1607_);
lean_inc_ref(v___x_1583_);
lean_inc_ref(v___x_1582_);
lean_inc_ref(v_liveVars_1584_);
v___f_1609_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1609_, 0, v_liveVars_1584_);
lean_closure_set(v___f_1609_, 1, v___x_1608_);
lean_closure_set(v___f_1609_, 2, v___x_1582_);
lean_closure_set(v___f_1609_, 3, v___x_1583_);
v___x_1610_ = ((size_t)0ULL);
v___x_1611_ = lean_usize_of_nat(v___x_1605_);
v___x_1612_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1606_, v___f_1609_, v_parents_1603_, v___x_1610_, v___x_1611_);
v___x_1613_ = lean_unbox(v___x_1612_);
lean_dec(v___x_1612_);
if (v___x_1613_ == 0)
{
goto v___jp_1586_;
}
else
{
lean_object* v___x_1614_; 
lean_dec_ref(v___x_1583_);
lean_dec_ref(v___x_1582_);
v___x_1614_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_child_1585_, v_derivedValMap_1580_, v_liveVars_1584_, v_shouldAdd_1581_);
return v___x_1614_;
}
}
}
v___jp_1586_:
{
lean_object* v___x_1587_; uint8_t v___x_1588_; 
lean_inc_ref(v_shouldAdd_1581_);
lean_inc(v_child_1585_);
v___x_1587_ = lean_apply_1(v_shouldAdd_1581_, v_child_1585_);
v___x_1588_ = lean_unbox(v___x_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; 
lean_dec_ref(v___x_1583_);
lean_dec_ref(v___x_1582_);
v___x_1589_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_child_1585_, v_derivedValMap_1580_, v_liveVars_1584_, v_shouldAdd_1581_);
return v___x_1589_;
}
else
{
lean_object* v_vars_1590_; lean_object* v_borrows_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1601_; 
v_vars_1590_ = lean_ctor_get(v_liveVars_1584_, 0);
v_borrows_1591_ = lean_ctor_get(v_liveVars_1584_, 1);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_liveVars_1584_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1593_ = v_liveVars_1584_;
v_isShared_1594_ = v_isSharedCheck_1601_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_borrows_1591_);
lean_inc(v_vars_1590_);
lean_dec(v_liveVars_1584_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1601_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1595_ = lean_box(0);
lean_inc(v_child_1585_);
v___x_1596_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1582_, v___x_1583_, v_borrows_1591_, v_child_1585_, v___x_1595_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v___x_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_vars_1590_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_child_1585_, v_derivedValMap_1580_, v___x_1598_, v_shouldAdd_1581_);
return v___x_1599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1___boxed(lean_object* v___f_1615_, lean_object* v___x_1616_, lean_object* v_derivedValMap_1617_, lean_object* v_shouldAdd_1618_, lean_object* v___x_1619_, lean_object* v___x_1620_, lean_object* v_liveVars_1621_, lean_object* v_child_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1(v___f_1615_, v___x_1616_, v_derivedValMap_1617_, v_shouldAdd_1618_, v___x_1619_, v___x_1620_, v_liveVars_1621_, v_child_1622_);
lean_dec_ref(v___x_1616_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(lean_object* v_fvarId_1624_, lean_object* v_derivedValMap_1625_, lean_object* v_liveVars_1626_, lean_object* v_shouldAdd_1627_){
_start:
{
lean_object* v___f_1628_; lean_object* v___x_1629_; 
v___f_1628_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_derivedValMap_1625_);
v___x_1629_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1628_, v_derivedValMap_1625_, v_fvarId_1624_);
if (lean_obj_tag(v___x_1629_) == 1)
{
lean_object* v_val_1630_; lean_object* v_children_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___f_1635_; lean_object* v___x_1636_; 
v_val_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_val_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v_children_1631_ = lean_ctor_get(v_val_1630_, 1);
lean_inc(v_children_1631_);
lean_dec(v_val_1630_);
v___x_1632_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default));
v___x_1633_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_1634_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___f_1635_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1___boxed), 8, 6);
lean_closure_set(v___f_1635_, 0, v___f_1628_);
lean_closure_set(v___f_1635_, 1, v___x_1632_);
lean_closure_set(v___f_1635_, 2, v_derivedValMap_1625_);
lean_closure_set(v___f_1635_, 3, v_shouldAdd_1627_);
lean_closure_set(v___f_1635_, 4, v___x_1633_);
lean_closure_set(v___f_1635_, 5, v___x_1634_);
v___x_1636_ = l_List_foldl___redArg(v___f_1635_, v_liveVars_1626_, v_children_1631_);
return v___x_1636_;
}
else
{
lean_dec(v___x_1629_);
lean_dec_ref(v_shouldAdd_1627_);
lean_dec(v_derivedValMap_1625_);
return v_liveVars_1626_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0(lean_object* v_val_1637_, lean_object* v___x_1638_, lean_object* v___x_1639_, lean_object* v_shouldBorrow_1640_, uint8_t v___x_1641_, lean_object* v_y_1642_){
_start:
{
lean_object* v_vars_1643_; uint8_t v___x_1644_; 
v_vars_1643_ = lean_ctor_get(v_val_1637_, 0);
lean_inc(v_y_1642_);
v___x_1644_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1638_, v___x_1639_, v_vars_1643_, v_y_1642_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = lean_apply_1(v_shouldBorrow_1640_, v_y_1642_);
v___x_1646_ = lean_unbox(v___x_1645_);
return v___x_1646_;
}
else
{
lean_dec(v_y_1642_);
lean_dec_ref(v_shouldBorrow_1640_);
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0___boxed(lean_object* v_val_1647_, lean_object* v___x_1648_, lean_object* v___x_1649_, lean_object* v_shouldBorrow_1650_, lean_object* v___x_1651_, lean_object* v_y_1652_){
_start:
{
uint8_t v___x_1972__boxed_1653_; uint8_t v_res_1654_; lean_object* v_r_1655_; 
v___x_1972__boxed_1653_ = lean_unbox(v___x_1651_);
v_res_1654_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0(v_val_1647_, v___x_1648_, v___x_1649_, v_shouldBorrow_1650_, v___x_1972__boxed_1653_, v_y_1652_);
lean_dec_ref(v_val_1647_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(lean_object* v_fvarId_1656_, lean_object* v_shouldBorrow_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v_vars_1664_; uint8_t v___x_1665_; 
v___x_1661_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_1662_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_1663_ = lean_st_ref_get(v_a_1659_);
v_vars_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc_ref(v_vars_1664_);
lean_dec(v___x_1663_);
lean_inc(v_fvarId_1656_);
v___x_1665_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1661_, v___x_1662_, v_vars_1664_, v_fvarId_1656_);
lean_dec_ref(v_vars_1664_);
if (v___x_1665_ == 0)
{
lean_object* v_derivedValMap_1666_; lean_object* v___x_1667_; lean_object* v_vars_1668_; lean_object* v_borrows_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1685_; 
v_derivedValMap_1666_ = lean_ctor_get(v_a_1658_, 2);
v___x_1667_ = lean_st_ref_take(v_a_1659_);
v_vars_1668_ = lean_ctor_get(v___x_1667_, 0);
v_borrows_1669_ = lean_ctor_get(v___x_1667_, 1);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1671_ = v___x_1667_;
v_isShared_1672_ = v_isSharedCheck_1685_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_borrows_1669_);
lean_inc(v_vars_1668_);
lean_dec(v___x_1667_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1685_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1673_ = lean_box(0);
lean_inc(v_fvarId_1656_);
v___x_1674_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1661_, v___x_1662_, v_vars_1668_, v_fvarId_1656_, v___x_1673_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1674_);
v___x_1676_ = v___x_1671_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_borrows_1669_);
v___x_1676_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___f_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1677_ = lean_st_ref_put(v_a_1659_, v___x_1676_);
v___x_1678_ = lean_st_ref_take(v_a_1659_);
v___x_1679_ = lean_box(v___x_1665_);
lean_inc(v___x_1678_);
v___f_1680_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1680_, 0, v___x_1678_);
lean_closure_set(v___f_1680_, 1, v___x_1661_);
lean_closure_set(v___f_1680_, 2, v___x_1662_);
lean_closure_set(v___f_1680_, 3, v_shouldBorrow_1657_);
lean_closure_set(v___f_1680_, 4, v___x_1679_);
lean_inc(v_derivedValMap_1666_);
v___x_1681_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_fvarId_1656_, v_derivedValMap_1666_, v___x_1678_, v___f_1680_);
v___x_1682_ = lean_st_ref_put(v_a_1659_, v___x_1681_);
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1673_);
return v___x_1683_;
}
}
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec_ref(v_shouldBorrow_1657_);
lean_dec(v_fvarId_1656_);
v___x_1686_ = lean_box(0);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___boxed(lean_object* v_fvarId_1688_, lean_object* v_shouldBorrow_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_1688_, v_shouldBorrow_1689_, v_a_1690_, v_a_1691_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(lean_object* v_fvarId_1694_, lean_object* v_shouldBorrow_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_1694_, v_shouldBorrow_1695_, v_a_1696_, v_a_1697_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___boxed(lean_object* v_fvarId_1704_, lean_object* v_shouldBorrow_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(v_fvarId_1704_, v_shouldBorrow_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
return v_res_1713_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(lean_object* v_liveVars_1714_, lean_object* v_as_1715_, size_t v_i_1716_, size_t v_stop_1717_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_usize_dec_eq(v_i_1716_, v_stop_1717_);
if (v___x_1718_ == 0)
{
lean_object* v_vars_1719_; lean_object* v_borrows_1720_; uint8_t v___x_1721_; uint8_t v___y_1723_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_vars_1719_ = lean_ctor_get(v_liveVars_1714_, 0);
v_borrows_1720_ = lean_ctor_get(v_liveVars_1714_, 1);
v___x_1721_ = 1;
v___x_1727_ = lean_array_uget_borrowed(v_as_1715_, v_i_1716_);
v___x_1728_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1719_, v___x_1727_);
if (v___x_1728_ == 0)
{
uint8_t v___x_1729_; 
v___x_1729_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_1720_, v___x_1727_);
v___y_1723_ = v___x_1729_;
goto v___jp_1722_;
}
else
{
v___y_1723_ = v___x_1728_;
goto v___jp_1722_;
}
v___jp_1722_:
{
if (v___y_1723_ == 0)
{
return v___x_1721_;
}
else
{
size_t v___x_1724_; size_t v___x_1725_; 
v___x_1724_ = ((size_t)1ULL);
v___x_1725_ = lean_usize_add(v_i_1716_, v___x_1724_);
v_i_1716_ = v___x_1725_;
goto _start;
}
}
}
else
{
uint8_t v___x_1730_; 
v___x_1730_ = 0;
return v___x_1730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3___boxed(lean_object* v_liveVars_1731_, lean_object* v_as_1732_, lean_object* v_i_1733_, lean_object* v_stop_1734_){
_start:
{
size_t v_i_boxed_1735_; size_t v_stop_boxed_1736_; uint8_t v_res_1737_; lean_object* v_r_1738_; 
v_i_boxed_1735_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_stop_boxed_1736_ = lean_unbox_usize(v_stop_1734_);
lean_dec(v_stop_1734_);
v_res_1737_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_liveVars_1731_, v_as_1732_, v_i_boxed_1735_, v_stop_boxed_1736_);
lean_dec_ref(v_as_1732_);
lean_dec_ref(v_liveVars_1731_);
v_r_1738_ = lean_box(v_res_1737_);
return v_r_1738_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(lean_object* v_y_1739_, lean_object* v_as_1740_, size_t v_i_1741_, size_t v_stop_1742_){
_start:
{
uint8_t v___x_1747_; 
v___x_1747_ = lean_usize_dec_eq(v_i_1741_, v_stop_1742_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_array_uget_borrowed(v_as_1740_, v_i_1741_);
if (lean_obj_tag(v___x_1748_) == 0)
{
goto v___jp_1743_;
}
else
{
lean_object* v_fvarId_1749_; uint8_t v___x_1750_; 
v_fvarId_1749_ = lean_ctor_get(v___x_1748_, 0);
v___x_1750_ = l_Lean_instBEqFVarId_beq(v_y_1739_, v_fvarId_1749_);
if (v___x_1750_ == 0)
{
goto v___jp_1743_;
}
else
{
return v___x_1750_;
}
}
}
else
{
uint8_t v___x_1751_; 
v___x_1751_ = 0;
return v___x_1751_;
}
v___jp_1743_:
{
size_t v___x_1744_; size_t v___x_1745_; 
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_add(v_i_1741_, v___x_1744_);
v_i_1741_ = v___x_1745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0___boxed(lean_object* v_y_1752_, lean_object* v_as_1753_, lean_object* v_i_1754_, lean_object* v_stop_1755_){
_start:
{
size_t v_i_boxed_1756_; size_t v_stop_boxed_1757_; uint8_t v_res_1758_; lean_object* v_r_1759_; 
v_i_boxed_1756_ = lean_unbox_usize(v_i_1754_);
lean_dec(v_i_1754_);
v_stop_boxed_1757_ = lean_unbox_usize(v_stop_1755_);
lean_dec(v_stop_1755_);
v_res_1758_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_y_1752_, v_as_1753_, v_i_boxed_1756_, v_stop_boxed_1757_);
lean_dec_ref(v_as_1753_);
lean_dec(v_y_1752_);
v_r_1759_ = lean_box(v_res_1758_);
return v_r_1759_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2_spec__4(lean_object* v_msg_1760_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default));
v___x_1762_ = lean_panic_fn_borrowed(v___x_1761_, v_msg_1760_);
return v___x_1762_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1766_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__2));
v___x_1767_ = lean_unsigned_to_nat(13u);
v___x_1768_ = lean_unsigned_to_nat(227u);
v___x_1769_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__1));
v___x_1770_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__0));
v___x_1771_ = l_mkPanicMessageWithDecl(v___x_1770_, v___x_1769_, v___x_1768_, v___x_1767_, v___x_1766_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(lean_object* v_t_1772_, lean_object* v_k_1773_){
_start:
{
if (lean_obj_tag(v_t_1772_) == 0)
{
lean_object* v_k_1774_; lean_object* v_v_1775_; lean_object* v_l_1776_; lean_object* v_r_1777_; uint8_t v___x_1778_; 
v_k_1774_ = lean_ctor_get(v_t_1772_, 1);
v_v_1775_ = lean_ctor_get(v_t_1772_, 2);
v_l_1776_ = lean_ctor_get(v_t_1772_, 3);
v_r_1777_ = lean_ctor_get(v_t_1772_, 4);
v___x_1778_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1773_, v_k_1774_);
switch(v___x_1778_)
{
case 0:
{
v_t_1772_ = v_l_1776_;
goto _start;
}
case 1:
{
lean_inc(v_v_1775_);
return v_v_1775_;
}
default: 
{
v_t_1772_ = v_r_1777_;
goto _start;
}
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3);
v___x_1782_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2_spec__4(v___x_1781_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___boxed(lean_object* v_t_1783_, lean_object* v_k_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_t_1783_, v_k_1784_);
lean_dec(v_k_1784_);
lean_dec(v_t_1783_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(lean_object* v___x_1786_, lean_object* v_args_1787_, uint8_t v___x_1788_, lean_object* v_derivedValMap_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
if (lean_obj_tag(v_x_1791_) == 0)
{
return v_x_1790_;
}
else
{
lean_object* v_head_1792_; lean_object* v_tail_1793_; uint8_t v___y_1809_; lean_object* v_cinfo_1821_; lean_object* v_parents_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v_head_1792_ = lean_ctor_get(v_x_1791_, 0);
lean_inc(v_head_1792_);
v_tail_1793_ = lean_ctor_get(v_x_1791_, 1);
lean_inc(v_tail_1793_);
lean_dec_ref_known(v_x_1791_, 2);
v_cinfo_1821_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_1789_, v_head_1792_);
v_parents_1822_ = lean_ctor_get(v_cinfo_1821_, 0);
lean_inc_ref(v_parents_1822_);
lean_dec_ref(v_cinfo_1821_);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = lean_array_get_size(v_parents_1822_);
v___x_1825_ = lean_nat_dec_lt(v___x_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_dec_ref(v_parents_1822_);
goto v___jp_1812_;
}
else
{
if (v___x_1825_ == 0)
{
lean_dec_ref(v_parents_1822_);
goto v___jp_1812_;
}
else
{
size_t v___x_1826_; size_t v___x_1827_; uint8_t v___x_1828_; 
v___x_1826_ = ((size_t)0ULL);
v___x_1827_ = lean_usize_of_nat(v___x_1824_);
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_1790_, v_parents_1822_, v___x_1826_, v___x_1827_);
lean_dec_ref(v_parents_1822_);
if (v___x_1828_ == 0)
{
goto v___jp_1812_;
}
else
{
lean_object* v___x_1829_; 
v___x_1829_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1786_, v_args_1787_, v___x_1788_, v_head_1792_, v_derivedValMap_1789_, v_x_1790_);
lean_dec(v_head_1792_);
v_x_1790_ = v___x_1829_;
v_x_1791_ = v_tail_1793_;
goto _start;
}
}
}
v___jp_1794_:
{
lean_object* v_vars_1795_; lean_object* v_borrows_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1807_; 
v_vars_1795_ = lean_ctor_get(v_x_1790_, 0);
v_borrows_1796_ = lean_ctor_get(v_x_1790_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_x_1790_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1798_ = v_x_1790_;
v_isShared_1799_ = v_isSharedCheck_1807_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_borrows_1796_);
lean_inc(v_vars_1795_);
lean_dec(v_x_1790_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1807_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1800_ = lean_box(0);
lean_inc(v_head_1792_);
v___x_1801_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_1796_, v_head_1792_, v___x_1800_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 1, v___x_1801_);
v___x_1803_ = v___x_1798_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_vars_1795_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; 
v___x_1804_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1786_, v_args_1787_, v___x_1788_, v_head_1792_, v_derivedValMap_1789_, v___x_1803_);
lean_dec(v_head_1792_);
v_x_1790_ = v___x_1804_;
v_x_1791_ = v_tail_1793_;
goto _start;
}
}
}
v___jp_1808_:
{
if (v___y_1809_ == 0)
{
lean_object* v___x_1810_; 
v___x_1810_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1786_, v_args_1787_, v___x_1788_, v_head_1792_, v_derivedValMap_1789_, v_x_1790_);
lean_dec(v_head_1792_);
v_x_1790_ = v___x_1810_;
v_x_1791_ = v_tail_1793_;
goto _start;
}
else
{
goto v___jp_1794_;
}
}
v___jp_1812_:
{
lean_object* v_vars_1813_; uint8_t v___x_1814_; 
v_vars_1813_ = lean_ctor_get(v___x_1786_, 0);
v___x_1814_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1813_, v_head_1792_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = lean_array_get_size(v_args_1787_);
v___x_1817_ = lean_nat_dec_lt(v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
goto v___jp_1794_;
}
else
{
if (v___x_1817_ == 0)
{
goto v___jp_1794_;
}
else
{
size_t v___x_1818_; size_t v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = ((size_t)0ULL);
v___x_1819_ = lean_usize_of_nat(v___x_1816_);
v___x_1820_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_head_1792_, v_args_1787_, v___x_1818_, v___x_1819_);
if (v___x_1820_ == 0)
{
goto v___jp_1794_;
}
else
{
v___y_1809_ = v___x_1814_;
goto v___jp_1808_;
}
}
}
}
else
{
v___y_1809_ = v___x_1788_;
goto v___jp_1808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(lean_object* v___x_1831_, lean_object* v_args_1832_, uint8_t v___x_1833_, lean_object* v_derivedValMap_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
if (lean_obj_tag(v_x_1836_) == 0)
{
return v_x_1835_;
}
else
{
lean_object* v_head_1837_; lean_object* v_tail_1838_; uint8_t v___y_1854_; lean_object* v_cinfo_1866_; lean_object* v_parents_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v_head_1837_ = lean_ctor_get(v_x_1836_, 0);
lean_inc(v_head_1837_);
v_tail_1838_ = lean_ctor_get(v_x_1836_, 1);
lean_inc(v_tail_1838_);
lean_dec_ref_known(v_x_1836_, 2);
v_cinfo_1866_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_1834_, v_head_1837_);
v_parents_1867_ = lean_ctor_get(v_cinfo_1866_, 0);
lean_inc_ref(v_parents_1867_);
lean_dec_ref(v_cinfo_1866_);
v___x_1868_ = lean_unsigned_to_nat(0u);
v___x_1869_ = lean_array_get_size(v_parents_1867_);
v___x_1870_ = lean_nat_dec_lt(v___x_1868_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_dec_ref(v_parents_1867_);
goto v___jp_1857_;
}
else
{
if (v___x_1870_ == 0)
{
lean_dec_ref(v_parents_1867_);
goto v___jp_1857_;
}
else
{
size_t v___x_1871_; size_t v___x_1872_; uint8_t v___x_1873_; 
v___x_1871_ = ((size_t)0ULL);
v___x_1872_ = lean_usize_of_nat(v___x_1869_);
v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_1835_, v_parents_1867_, v___x_1871_, v___x_1872_);
lean_dec_ref(v_parents_1867_);
if (v___x_1873_ == 0)
{
goto v___jp_1857_;
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1831_, v_args_1832_, v___x_1833_, v_head_1837_, v_derivedValMap_1834_, v_x_1835_);
lean_dec(v_head_1837_);
v___x_1875_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1831_, v_args_1832_, v___x_1833_, v_derivedValMap_1834_, v___x_1874_, v_tail_1838_);
return v___x_1875_;
}
}
}
v___jp_1839_:
{
lean_object* v_vars_1840_; lean_object* v_borrows_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1852_; 
v_vars_1840_ = lean_ctor_get(v_x_1835_, 0);
v_borrows_1841_ = lean_ctor_get(v_x_1835_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_x_1835_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1843_ = v_x_1835_;
v_isShared_1844_ = v_isSharedCheck_1852_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_borrows_1841_);
lean_inc(v_vars_1840_);
lean_dec(v_x_1835_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1852_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1845_ = lean_box(0);
lean_inc(v_head_1837_);
v___x_1846_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_1841_, v_head_1837_, v___x_1845_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v___x_1846_);
v___x_1848_ = v___x_1843_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_vars_1840_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1831_, v_args_1832_, v___x_1833_, v_head_1837_, v_derivedValMap_1834_, v___x_1848_);
lean_dec(v_head_1837_);
v___x_1850_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1831_, v_args_1832_, v___x_1833_, v_derivedValMap_1834_, v___x_1849_, v_tail_1838_);
return v___x_1850_;
}
}
}
v___jp_1853_:
{
if (v___y_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1831_, v_args_1832_, v___x_1833_, v_head_1837_, v_derivedValMap_1834_, v_x_1835_);
lean_dec(v_head_1837_);
v___x_1856_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1831_, v_args_1832_, v___x_1833_, v_derivedValMap_1834_, v___x_1855_, v_tail_1838_);
return v___x_1856_;
}
else
{
goto v___jp_1839_;
}
}
v___jp_1857_:
{
lean_object* v_vars_1858_; uint8_t v___x_1859_; 
v_vars_1858_ = lean_ctor_get(v___x_1831_, 0);
v___x_1859_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1858_, v_head_1837_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = lean_array_get_size(v_args_1832_);
v___x_1862_ = lean_nat_dec_lt(v___x_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
goto v___jp_1839_;
}
else
{
if (v___x_1862_ == 0)
{
goto v___jp_1839_;
}
else
{
size_t v___x_1863_; size_t v___x_1864_; uint8_t v___x_1865_; 
v___x_1863_ = ((size_t)0ULL);
v___x_1864_ = lean_usize_of_nat(v___x_1861_);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_head_1837_, v_args_1832_, v___x_1863_, v___x_1864_);
if (v___x_1865_ == 0)
{
goto v___jp_1839_;
}
else
{
v___y_1854_ = v___x_1859_;
goto v___jp_1853_;
}
}
}
}
else
{
v___y_1854_ = v___x_1833_;
goto v___jp_1853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(lean_object* v___x_1876_, lean_object* v_args_1877_, uint8_t v___x_1878_, lean_object* v_fvarId_1879_, lean_object* v_derivedValMap_1880_, lean_object* v_liveVars_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_derivedValMap_1880_, v_fvarId_1879_);
if (lean_obj_tag(v___x_1882_) == 1)
{
lean_object* v_val_1883_; lean_object* v_children_1884_; lean_object* v___x_1885_; 
v_val_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_val_1883_);
lean_dec_ref_known(v___x_1882_, 1);
v_children_1884_ = lean_ctor_get(v_val_1883_, 1);
lean_inc(v_children_1884_);
lean_dec(v_val_1883_);
v___x_1885_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(v___x_1876_, v_args_1877_, v___x_1878_, v_derivedValMap_1880_, v_liveVars_1881_, v_children_1884_);
return v___x_1885_;
}
else
{
lean_dec(v___x_1882_);
return v_liveVars_1881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1___boxed(lean_object* v___x_1886_, lean_object* v_args_1887_, lean_object* v___x_1888_, lean_object* v_fvarId_1889_, lean_object* v_derivedValMap_1890_, lean_object* v_liveVars_1891_){
_start:
{
uint8_t v___x_2270__boxed_1892_; lean_object* v_res_1893_; 
v___x_2270__boxed_1892_ = lean_unbox(v___x_1888_);
v_res_1893_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1886_, v_args_1887_, v___x_2270__boxed_1892_, v_fvarId_1889_, v_derivedValMap_1890_, v_liveVars_1891_);
lean_dec(v_derivedValMap_1890_);
lean_dec(v_fvarId_1889_);
lean_dec_ref(v_args_1887_);
lean_dec_ref(v___x_1886_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v___x_1894_, lean_object* v_args_1895_, lean_object* v___x_1896_, lean_object* v_derivedValMap_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
uint8_t v___x_2275__boxed_1900_; lean_object* v_res_1901_; 
v___x_2275__boxed_1900_ = lean_unbox(v___x_1896_);
v_res_1901_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1894_, v_args_1895_, v___x_2275__boxed_1900_, v_derivedValMap_1897_, v_x_1898_, v_x_1899_);
lean_dec(v_derivedValMap_1897_);
lean_dec_ref(v_args_1895_);
lean_dec_ref(v___x_1894_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4___boxed(lean_object* v___x_1902_, lean_object* v_args_1903_, lean_object* v___x_1904_, lean_object* v_derivedValMap_1905_, lean_object* v_x_1906_, lean_object* v_x_1907_){
_start:
{
uint8_t v___x_2307__boxed_1908_; lean_object* v_res_1909_; 
v___x_2307__boxed_1908_ = lean_unbox(v___x_1904_);
v_res_1909_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(v___x_1902_, v_args_1903_, v___x_2307__boxed_1908_, v_derivedValMap_1905_, v_x_1906_, v_x_1907_);
lean_dec(v_derivedValMap_1905_);
lean_dec_ref(v_args_1903_);
lean_dec_ref(v___x_1902_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(lean_object* v_args_1910_, lean_object* v_fvarId_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v___x_1915_; lean_object* v_vars_1916_; uint8_t v___x_1917_; 
v___x_1915_ = lean_st_ref_get(v_a_1913_);
v_vars_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc_ref(v_vars_1916_);
lean_dec(v___x_1915_);
v___x_1917_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1916_, v_fvarId_1911_);
lean_dec_ref(v_vars_1916_);
if (v___x_1917_ == 0)
{
lean_object* v_derivedValMap_1918_; lean_object* v___x_1919_; lean_object* v_vars_1920_; lean_object* v_borrows_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1935_; 
v_derivedValMap_1918_ = lean_ctor_get(v_a_1912_, 2);
v___x_1919_ = lean_st_ref_take(v_a_1913_);
v_vars_1920_ = lean_ctor_get(v___x_1919_, 0);
v_borrows_1921_ = lean_ctor_get(v___x_1919_, 1);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1923_ = v___x_1919_;
v_isShared_1924_ = v_isSharedCheck_1935_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_borrows_1921_);
lean_inc(v_vars_1920_);
lean_dec(v___x_1919_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1935_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1925_ = lean_box(0);
lean_inc(v_fvarId_1911_);
v___x_1926_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_vars_1920_, v_fvarId_1911_, v___x_1925_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1926_);
v___x_1928_ = v___x_1923_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_borrows_1921_);
v___x_1928_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1929_ = lean_st_ref_put(v_a_1913_, v___x_1928_);
v___x_1930_ = lean_st_ref_take(v_a_1913_);
lean_inc(v___x_1930_);
v___x_1931_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1930_, v_args_1910_, v___x_1917_, v_fvarId_1911_, v_derivedValMap_1918_, v___x_1930_);
lean_dec(v_fvarId_1911_);
lean_dec(v___x_1930_);
v___x_1932_ = lean_st_ref_put(v_a_1913_, v___x_1931_);
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1925_);
return v___x_1933_;
}
}
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v_fvarId_1911_);
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg___boxed(lean_object* v_args_1938_, lean_object* v_fvarId_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_1938_, v_fvarId_1939_, v_a_1940_, v_a_1941_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec_ref(v_args_1938_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(lean_object* v_args_1944_, lean_object* v_as_1945_, size_t v_i_1946_, size_t v_stop_1947_, lean_object* v_b_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_a_1957_; uint8_t v___x_1961_; 
v___x_1961_ = lean_usize_dec_eq(v_i_1946_, v_stop_1947_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
v___x_1962_ = lean_array_uget_borrowed(v_as_1945_, v_i_1946_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v___x_1963_; 
v___x_1963_ = lean_box(0);
v_a_1957_ = v___x_1963_;
goto v___jp_1956_;
}
else
{
lean_object* v_fvarId_1964_; lean_object* v___x_1965_; 
v_fvarId_1964_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_fvarId_1964_);
v___x_1965_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_1944_, v_fvarId_1964_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1965_, 1);
v_a_1957_ = v_a_1966_;
goto v___jp_1956_;
}
else
{
return v___x_1965_;
}
}
}
else
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_b_1948_);
return v___x_1967_;
}
v___jp_1956_:
{
size_t v___x_1958_; size_t v___x_1959_; 
v___x_1958_ = ((size_t)1ULL);
v___x_1959_ = lean_usize_add(v_i_1946_, v___x_1958_);
v_i_1946_ = v___x_1959_;
v_b_1948_ = v_a_1957_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2___boxed(lean_object* v_args_1968_, lean_object* v_as_1969_, lean_object* v_i_1970_, lean_object* v_stop_1971_, lean_object* v_b_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
size_t v_i_boxed_1980_; size_t v_stop_boxed_1981_; lean_object* v_res_1982_; 
v_i_boxed_1980_ = lean_unbox_usize(v_i_1970_);
lean_dec(v_i_1970_);
v_stop_boxed_1981_ = lean_unbox_usize(v_stop_1971_);
lean_dec(v_stop_1971_);
v_res_1982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(v_args_1968_, v_as_1969_, v_i_boxed_1980_, v_stop_boxed_1981_, v_b_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec_ref(v_as_1969_);
lean_dec_ref(v_args_1968_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(lean_object* v_args_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1991_ = lean_unsigned_to_nat(0u);
v___x_1992_ = lean_array_get_size(v_args_1983_);
v___x_1993_ = lean_box(0);
v___x_1994_ = lean_nat_dec_lt(v___x_1991_, v___x_1992_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
return v___x_1995_;
}
else
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_nat_dec_le(v___x_1992_, v___x_1992_);
if (v___x_1996_ == 0)
{
if (v___x_1994_ == 0)
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1993_);
return v___x_1997_;
}
else
{
size_t v___x_1998_; size_t v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = ((size_t)0ULL);
v___x_1999_ = lean_usize_of_nat(v___x_1992_);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(v_args_1983_, v_args_1983_, v___x_1998_, v___x_1999_, v___x_1993_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
return v___x_2000_;
}
}
else
{
size_t v___x_2001_; size_t v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = ((size_t)0ULL);
v___x_2002_ = lean_usize_of_nat(v___x_1992_);
v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(v_args_1983_, v_args_1983_, v___x_2001_, v___x_2002_, v___x_1993_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs___boxed(lean_object* v_args_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_args_2004_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(lean_object* v_args_2013_, lean_object* v_fvarId_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_2013_, v_fvarId_2014_, v_a_2015_, v_a_2016_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___boxed(lean_object* v_args_2023_, lean_object* v_fvarId_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(v_args_2023_, v_fvarId_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec_ref(v_args_2023_);
return v_res_2032_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_instMonadEIO___redArg();
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(lean_object* v_msg_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v_toApplicative_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2111_; 
v___x_2046_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0);
v___x_2047_ = l_StateRefT_x27_instMonad___redArg(v___x_2046_);
v_toApplicative_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v___x_2047_, 1);
lean_dec(v_unused_2112_);
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2111_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_toApplicative_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2111_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v_toFunctor_2052_; lean_object* v_toSeq_2053_; lean_object* v_toSeqLeft_2054_; lean_object* v_toSeqRight_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2109_; 
v_toFunctor_2052_ = lean_ctor_get(v_toApplicative_2048_, 0);
v_toSeq_2053_ = lean_ctor_get(v_toApplicative_2048_, 2);
v_toSeqLeft_2054_ = lean_ctor_get(v_toApplicative_2048_, 3);
v_toSeqRight_2055_ = lean_ctor_get(v_toApplicative_2048_, 4);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_toApplicative_2048_);
if (v_isSharedCheck_2109_ == 0)
{
lean_object* v_unused_2110_; 
v_unused_2110_ = lean_ctor_get(v_toApplicative_2048_, 1);
lean_dec(v_unused_2110_);
v___x_2057_ = v_toApplicative_2048_;
v_isShared_2058_ = v_isSharedCheck_2109_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_toSeqRight_2055_);
lean_inc(v_toSeqLeft_2054_);
lean_inc(v_toSeq_2053_);
lean_inc(v_toFunctor_2052_);
lean_dec(v_toApplicative_2048_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2109_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___f_2059_; lean_object* v___f_2060_; lean_object* v___f_2061_; lean_object* v___f_2062_; lean_object* v___x_2063_; lean_object* v___f_2064_; lean_object* v___f_2065_; lean_object* v___f_2066_; lean_object* v___x_2068_; 
v___f_2059_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__1));
v___f_2060_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2052_);
v___f_2061_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2061_, 0, v_toFunctor_2052_);
v___f_2062_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2062_, 0, v_toFunctor_2052_);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___f_2061_);
lean_ctor_set(v___x_2063_, 1, v___f_2062_);
v___f_2064_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2064_, 0, v_toSeqRight_2055_);
v___f_2065_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2065_, 0, v_toSeqLeft_2054_);
v___f_2066_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2066_, 0, v_toSeq_2053_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 4, v___f_2064_);
lean_ctor_set(v___x_2057_, 3, v___f_2065_);
lean_ctor_set(v___x_2057_, 2, v___f_2066_);
lean_ctor_set(v___x_2057_, 1, v___f_2059_);
lean_ctor_set(v___x_2057_, 0, v___x_2063_);
v___x_2068_ = v___x_2057_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___f_2059_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v___f_2066_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v___f_2065_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v___f_2064_);
v___x_2068_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2070_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 1, v___f_2060_);
lean_ctor_set(v___x_2050_, 0, v___x_2068_);
v___x_2070_ = v___x_2050_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v___f_2060_);
v___x_2070_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2071_; lean_object* v_toApplicative_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2105_; 
v___x_2071_ = l_StateRefT_x27_instMonad___redArg(v___x_2070_);
v_toApplicative_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; 
v_unused_2106_ = lean_ctor_get(v___x_2071_, 1);
lean_dec(v_unused_2106_);
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2105_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_toApplicative_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2105_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_toFunctor_2076_; lean_object* v_toSeq_2077_; lean_object* v_toSeqLeft_2078_; lean_object* v_toSeqRight_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2103_; 
v_toFunctor_2076_ = lean_ctor_get(v_toApplicative_2072_, 0);
v_toSeq_2077_ = lean_ctor_get(v_toApplicative_2072_, 2);
v_toSeqLeft_2078_ = lean_ctor_get(v_toApplicative_2072_, 3);
v_toSeqRight_2079_ = lean_ctor_get(v_toApplicative_2072_, 4);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_toApplicative_2072_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v_toApplicative_2072_, 1);
lean_dec(v_unused_2104_);
v___x_2081_ = v_toApplicative_2072_;
v_isShared_2082_ = v_isSharedCheck_2103_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_toSeqRight_2079_);
lean_inc(v_toSeqLeft_2078_);
lean_inc(v_toSeq_2077_);
lean_inc(v_toFunctor_2076_);
lean_dec(v_toApplicative_2072_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2103_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___f_2083_; lean_object* v___f_2084_; lean_object* v___f_2085_; lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v___f_2088_; lean_object* v___f_2089_; lean_object* v___f_2090_; lean_object* v___x_2092_; 
v___f_2083_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__3));
v___f_2084_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2076_);
v___f_2085_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2085_, 0, v_toFunctor_2076_);
v___f_2086_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2086_, 0, v_toFunctor_2076_);
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___f_2085_);
lean_ctor_set(v___x_2087_, 1, v___f_2086_);
v___f_2088_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2088_, 0, v_toSeqRight_2079_);
v___f_2089_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2089_, 0, v_toSeqLeft_2078_);
v___f_2090_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2090_, 0, v_toSeq_2077_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 4, v___f_2088_);
lean_ctor_set(v___x_2081_, 3, v___f_2089_);
lean_ctor_set(v___x_2081_, 2, v___f_2090_);
lean_ctor_set(v___x_2081_, 1, v___f_2083_);
lean_ctor_set(v___x_2081_, 0, v___x_2087_);
v___x_2092_ = v___x_2081_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v___f_2083_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v___f_2090_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v___f_2089_);
lean_ctor_set(v_reuseFailAlloc_2102_, 4, v___f_2088_);
v___x_2092_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2094_; 
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 1, v___f_2084_);
lean_ctor_set(v___x_2074_, 0, v___x_2092_);
v___x_2094_ = v___x_2074_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v___f_2084_);
v___x_2094_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___f_2098_; lean_object* v___x_1646__overap_2099_; lean_object* v___x_2100_; 
v___x_2095_ = l_StateRefT_x27_instMonad___redArg(v___x_2094_);
v___x_2096_ = lean_box(0);
v___x_2097_ = l_instInhabitedOfMonad___redArg(v___x_2095_, v___x_2096_);
v___f_2098_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2098_, 0, v___x_2097_);
v___x_1646__overap_2099_ = lean_panic_fn_borrowed(v___f_2098_, v_msg_2038_);
lean_dec_ref(v___f_2098_);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
v___x_2100_ = lean_apply_7(v___x_1646__overap_2099_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, lean_box(0));
return v___x_2100_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___boxed(lean_object* v_msg_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(v_msg_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_2122_, uint8_t v___x_2123_, lean_object* v_derivedValMap_2124_, lean_object* v_x_2125_, lean_object* v_x_2126_){
_start:
{
if (lean_obj_tag(v_x_2126_) == 0)
{
return v_x_2125_;
}
else
{
lean_object* v_head_2127_; lean_object* v_tail_2128_; lean_object* v_cinfo_2148_; lean_object* v_parents_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v_head_2127_ = lean_ctor_get(v_x_2126_, 0);
lean_inc(v_head_2127_);
v_tail_2128_ = lean_ctor_get(v_x_2126_, 1);
lean_inc(v_tail_2128_);
lean_dec_ref_known(v_x_2126_, 2);
v_cinfo_2148_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2124_, v_head_2127_);
v_parents_2149_ = lean_ctor_get(v_cinfo_2148_, 0);
lean_inc_ref(v_parents_2149_);
lean_dec_ref(v_cinfo_2148_);
v___x_2150_ = lean_unsigned_to_nat(0u);
v___x_2151_ = lean_array_get_size(v_parents_2149_);
v___x_2152_ = lean_nat_dec_lt(v___x_2150_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_dec_ref(v_parents_2149_);
goto v___jp_2143_;
}
else
{
if (v___x_2152_ == 0)
{
lean_dec_ref(v_parents_2149_);
goto v___jp_2143_;
}
else
{
size_t v___x_2153_; size_t v___x_2154_; uint8_t v___x_2155_; 
v___x_2153_ = ((size_t)0ULL);
v___x_2154_ = lean_usize_of_nat(v___x_2151_);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2125_, v_parents_2149_, v___x_2153_, v___x_2154_);
lean_dec_ref(v_parents_2149_);
if (v___x_2155_ == 0)
{
goto v___jp_2143_;
}
else
{
lean_object* v___x_2156_; 
v___x_2156_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2122_, v___x_2123_, v_head_2127_, v_derivedValMap_2124_, v_x_2125_);
lean_dec(v_head_2127_);
v_x_2125_ = v___x_2156_;
v_x_2126_ = v_tail_2128_;
goto _start;
}
}
}
v___jp_2129_:
{
lean_object* v_vars_2130_; lean_object* v_borrows_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2142_; 
v_vars_2130_ = lean_ctor_get(v_x_2125_, 0);
v_borrows_2131_ = lean_ctor_get(v_x_2125_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_x_2125_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2133_ = v_x_2125_;
v_isShared_2134_ = v_isSharedCheck_2142_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_borrows_2131_);
lean_inc(v_vars_2130_);
lean_dec(v_x_2125_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2142_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2135_ = lean_box(0);
lean_inc(v_head_2127_);
v___x_2136_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2131_, v_head_2127_, v___x_2135_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v___x_2136_);
v___x_2138_ = v___x_2133_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_vars_2130_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2139_; 
v___x_2139_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2122_, v___x_2123_, v_head_2127_, v_derivedValMap_2124_, v___x_2138_);
lean_dec(v_head_2127_);
v_x_2125_ = v___x_2139_;
v_x_2126_ = v_tail_2128_;
goto _start;
}
}
}
v___jp_2143_:
{
lean_object* v_vars_2144_; uint8_t v___x_2145_; 
v_vars_2144_ = lean_ctor_get(v___x_2122_, 0);
v___x_2145_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2144_, v_head_2127_);
if (v___x_2145_ == 0)
{
goto v___jp_2129_;
}
else
{
if (v___x_2123_ == 0)
{
lean_object* v___x_2146_; 
v___x_2146_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2122_, v___x_2123_, v_head_2127_, v_derivedValMap_2124_, v_x_2125_);
lean_dec(v_head_2127_);
v_x_2125_ = v___x_2146_;
v_x_2126_ = v_tail_2128_;
goto _start;
}
else
{
goto v___jp_2129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(lean_object* v___x_2158_, uint8_t v___x_2159_, lean_object* v_derivedValMap_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_){
_start:
{
if (lean_obj_tag(v_x_2162_) == 0)
{
return v_x_2161_;
}
else
{
lean_object* v_head_2163_; lean_object* v_tail_2164_; lean_object* v_cinfo_2184_; lean_object* v_parents_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v_head_2163_ = lean_ctor_get(v_x_2162_, 0);
lean_inc(v_head_2163_);
v_tail_2164_ = lean_ctor_get(v_x_2162_, 1);
lean_inc(v_tail_2164_);
lean_dec_ref_known(v_x_2162_, 2);
v_cinfo_2184_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2160_, v_head_2163_);
v_parents_2185_ = lean_ctor_get(v_cinfo_2184_, 0);
lean_inc_ref(v_parents_2185_);
lean_dec_ref(v_cinfo_2184_);
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = lean_array_get_size(v_parents_2185_);
v___x_2188_ = lean_nat_dec_lt(v___x_2186_, v___x_2187_);
if (v___x_2188_ == 0)
{
lean_dec_ref(v_parents_2185_);
goto v___jp_2179_;
}
else
{
if (v___x_2188_ == 0)
{
lean_dec_ref(v_parents_2185_);
goto v___jp_2179_;
}
else
{
size_t v___x_2189_; size_t v___x_2190_; uint8_t v___x_2191_; 
v___x_2189_ = ((size_t)0ULL);
v___x_2190_ = lean_usize_of_nat(v___x_2187_);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2161_, v_parents_2185_, v___x_2189_, v___x_2190_);
lean_dec_ref(v_parents_2185_);
if (v___x_2191_ == 0)
{
goto v___jp_2179_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2158_, v___x_2159_, v_head_2163_, v_derivedValMap_2160_, v_x_2161_);
lean_dec(v_head_2163_);
v___x_2193_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2158_, v___x_2159_, v_derivedValMap_2160_, v___x_2192_, v_tail_2164_);
return v___x_2193_;
}
}
}
v___jp_2165_:
{
lean_object* v_vars_2166_; lean_object* v_borrows_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2178_; 
v_vars_2166_ = lean_ctor_get(v_x_2161_, 0);
v_borrows_2167_ = lean_ctor_get(v_x_2161_, 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_x_2161_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2169_ = v_x_2161_;
v_isShared_2170_ = v_isSharedCheck_2178_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_borrows_2167_);
lean_inc(v_vars_2166_);
lean_dec(v_x_2161_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2178_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2171_ = lean_box(0);
lean_inc(v_head_2163_);
v___x_2172_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2167_, v_head_2163_, v___x_2171_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 1, v___x_2172_);
v___x_2174_ = v___x_2169_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_vars_2166_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2158_, v___x_2159_, v_head_2163_, v_derivedValMap_2160_, v___x_2174_);
lean_dec(v_head_2163_);
v___x_2176_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2158_, v___x_2159_, v_derivedValMap_2160_, v___x_2175_, v_tail_2164_);
return v___x_2176_;
}
}
}
v___jp_2179_:
{
lean_object* v_vars_2180_; uint8_t v___x_2181_; 
v_vars_2180_ = lean_ctor_get(v___x_2158_, 0);
v___x_2181_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2180_, v_head_2163_);
if (v___x_2181_ == 0)
{
goto v___jp_2165_;
}
else
{
if (v___x_2159_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2158_, v___x_2159_, v_head_2163_, v_derivedValMap_2160_, v_x_2161_);
lean_dec(v_head_2163_);
v___x_2183_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2158_, v___x_2159_, v_derivedValMap_2160_, v___x_2182_, v_tail_2164_);
return v___x_2183_;
}
else
{
goto v___jp_2165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(lean_object* v___x_2194_, uint8_t v___x_2195_, lean_object* v_fvarId_2196_, lean_object* v_derivedValMap_2197_, lean_object* v_liveVars_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_derivedValMap_2197_, v_fvarId_2196_);
if (lean_obj_tag(v___x_2199_) == 1)
{
lean_object* v_val_2200_; lean_object* v_children_2201_; lean_object* v___x_2202_; 
v_val_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v___x_2199_, 1);
v_children_2201_ = lean_ctor_get(v_val_2200_, 1);
lean_inc(v_children_2201_);
lean_dec(v_val_2200_);
v___x_2202_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(v___x_2194_, v___x_2195_, v_derivedValMap_2197_, v_liveVars_2198_, v_children_2201_);
return v___x_2202_;
}
else
{
lean_dec(v___x_2199_);
return v_liveVars_2198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0___boxed(lean_object* v___x_2203_, lean_object* v___x_2204_, lean_object* v_fvarId_2205_, lean_object* v_derivedValMap_2206_, lean_object* v_liveVars_2207_){
_start:
{
uint8_t v___x_2263__boxed_2208_; lean_object* v_res_2209_; 
v___x_2263__boxed_2208_ = lean_unbox(v___x_2204_);
v_res_2209_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2203_, v___x_2263__boxed_2208_, v_fvarId_2205_, v_derivedValMap_2206_, v_liveVars_2207_);
lean_dec(v_derivedValMap_2206_);
lean_dec(v_fvarId_2205_);
lean_dec_ref(v___x_2203_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v___x_2210_, lean_object* v___x_2211_, lean_object* v_derivedValMap_2212_, lean_object* v_x_2213_, lean_object* v_x_2214_){
_start:
{
uint8_t v___x_2268__boxed_2215_; lean_object* v_res_2216_; 
v___x_2268__boxed_2215_ = lean_unbox(v___x_2211_);
v_res_2216_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2210_, v___x_2268__boxed_2215_, v_derivedValMap_2212_, v_x_2213_, v_x_2214_);
lean_dec(v_derivedValMap_2212_);
lean_dec_ref(v___x_2210_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2___boxed(lean_object* v___x_2217_, lean_object* v___x_2218_, lean_object* v_derivedValMap_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_){
_start:
{
uint8_t v___x_2292__boxed_2222_; lean_object* v_res_2223_; 
v___x_2292__boxed_2222_ = lean_unbox(v___x_2218_);
v_res_2223_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(v___x_2217_, v___x_2292__boxed_2222_, v_derivedValMap_2219_, v_x_2220_, v_x_2221_);
lean_dec(v_derivedValMap_2219_);
lean_dec_ref(v___x_2217_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(lean_object* v_fvarId_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v___x_2228_; lean_object* v_vars_2229_; uint8_t v___x_2230_; 
v___x_2228_ = lean_st_ref_get(v_a_2226_);
v_vars_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc_ref(v_vars_2229_);
lean_dec(v___x_2228_);
v___x_2230_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2229_, v_fvarId_2224_);
lean_dec_ref(v_vars_2229_);
if (v___x_2230_ == 0)
{
lean_object* v_derivedValMap_2231_; lean_object* v___x_2232_; lean_object* v_vars_2233_; lean_object* v_borrows_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2248_; 
v_derivedValMap_2231_ = lean_ctor_get(v_a_2225_, 2);
v___x_2232_ = lean_st_ref_take(v_a_2226_);
v_vars_2233_ = lean_ctor_get(v___x_2232_, 0);
v_borrows_2234_ = lean_ctor_get(v___x_2232_, 1);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2236_ = v___x_2232_;
v_isShared_2237_ = v_isSharedCheck_2248_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_borrows_2234_);
lean_inc(v_vars_2233_);
lean_dec(v___x_2232_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2248_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2238_ = lean_box(0);
lean_inc(v_fvarId_2224_);
v___x_2239_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_vars_2233_, v_fvarId_2224_, v___x_2238_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v___x_2239_);
v___x_2241_ = v___x_2236_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_borrows_2234_);
v___x_2241_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2242_ = lean_st_ref_put(v_a_2226_, v___x_2241_);
v___x_2243_ = lean_st_ref_take(v_a_2226_);
lean_inc(v___x_2243_);
v___x_2244_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2243_, v___x_2230_, v_fvarId_2224_, v_derivedValMap_2231_, v___x_2243_);
lean_dec(v_fvarId_2224_);
lean_dec(v___x_2243_);
v___x_2245_ = lean_st_ref_put(v_a_2226_, v___x_2244_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2238_);
return v___x_2246_;
}
}
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_dec(v_fvarId_2224_);
v___x_2249_ = lean_box(0);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg___boxed(lean_object* v_fvarId_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2251_, v_a_2252_, v_a_2253_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
return v_res_2255_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2257_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_2258_ = lean_unsigned_to_nat(20u);
v___x_2259_ = lean_unsigned_to_nat(343u);
v___x_2260_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__0));
v___x_2261_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_2262_ = l_mkPanicMessageWithDecl(v___x_2261_, v___x_2260_, v___x_2259_, v___x_2258_, v___x_2257_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(lean_object* v_value_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
switch(lean_obj_tag(v_value_2263_))
{
case 0:
{
lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2278_; 
v_isSharedCheck_2278_ = !lean_is_exclusive(v_value_2263_);
if (v_isSharedCheck_2278_ == 0)
{
lean_object* v_unused_2279_; 
v_unused_2279_ = lean_ctor_get(v_value_2263_, 0);
lean_dec(v_unused_2279_);
v___x_2272_ = v_value_2263_;
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
else
{
lean_dec(v_value_2263_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = lean_box(0);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2274_);
v___x_2276_ = v___x_2272_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
case 1:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_box(0);
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
return v___x_2281_;
}
case 4:
{
lean_object* v_fvarId_2282_; lean_object* v_args_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_fvarId_2282_ = lean_ctor_get(v_value_2263_, 0);
lean_inc(v_fvarId_2282_);
v_args_2283_ = lean_ctor_get(v_value_2263_, 1);
lean_inc_ref(v_args_2283_);
lean_dec_ref_known(v_value_2263_, 2);
v___x_2284_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2282_, v_a_2264_, v_a_2265_);
lean_dec_ref(v___x_2284_);
v___x_2285_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2283_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec_ref(v_args_2283_);
return v___x_2285_;
}
case 5:
{
lean_object* v_args_2286_; lean_object* v___x_2287_; 
v_args_2286_ = lean_ctor_get(v_value_2263_, 1);
lean_inc_ref(v_args_2286_);
lean_dec_ref_known(v_value_2263_, 2);
v___x_2287_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2286_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec_ref(v_args_2286_);
return v___x_2287_;
}
case 8:
{
lean_object* v_var_2288_; lean_object* v___x_2289_; 
v_var_2288_ = lean_ctor_get(v_value_2263_, 2);
lean_inc(v_var_2288_);
lean_dec_ref_known(v_value_2263_, 3);
v___x_2289_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2288_, v_a_2264_, v_a_2265_);
return v___x_2289_;
}
case 9:
{
lean_object* v_args_2290_; lean_object* v___x_2291_; 
v_args_2290_ = lean_ctor_get(v_value_2263_, 1);
lean_inc_ref(v_args_2290_);
lean_dec_ref_known(v_value_2263_, 2);
v___x_2291_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2290_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec_ref(v_args_2290_);
return v___x_2291_;
}
case 10:
{
lean_object* v_args_2292_; lean_object* v___x_2293_; 
v_args_2292_ = lean_ctor_get(v_value_2263_, 1);
lean_inc_ref(v_args_2292_);
lean_dec_ref_known(v_value_2263_, 2);
v___x_2293_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2292_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec_ref(v_args_2292_);
return v___x_2293_;
}
case 12:
{
lean_object* v_var_2294_; lean_object* v_args_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v_var_2294_ = lean_ctor_get(v_value_2263_, 0);
lean_inc(v_var_2294_);
v_args_2295_ = lean_ctor_get(v_value_2263_, 2);
lean_inc_ref(v_args_2295_);
lean_dec_ref_known(v_value_2263_, 3);
v___x_2296_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2294_, v_a_2264_, v_a_2265_);
lean_dec_ref(v___x_2296_);
v___x_2297_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2295_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec_ref(v_args_2295_);
return v___x_2297_;
}
case 14:
{
lean_object* v_fvarId_2298_; lean_object* v___x_2299_; 
v_fvarId_2298_ = lean_ctor_get(v_value_2263_, 0);
lean_inc(v_fvarId_2298_);
lean_dec_ref_known(v_value_2263_, 1);
v___x_2299_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2298_, v_a_2264_, v_a_2265_);
return v___x_2299_;
}
case 15:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec_ref_known(v_value_2263_, 1);
v___x_2300_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1);
v___x_2301_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(v___x_2300_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
return v___x_2301_;
}
default: 
{
lean_object* v_var_2302_; lean_object* v___x_2303_; 
v_var_2302_ = lean_ctor_get(v_value_2263_, 1);
lean_inc(v_var_2302_);
lean_dec(v_value_2263_);
v___x_2303_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2302_, v_a_2264_, v_a_2265_);
return v___x_2303_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___boxed(lean_object* v_value_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(v_value_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(lean_object* v_fvarId_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2313_, v_a_2314_, v_a_2315_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___boxed(lean_object* v_fvarId_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(v_fvarId_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(lean_object* v_fvarId_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v___x_2334_; lean_object* v_vars_2335_; lean_object* v_borrows_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2350_; 
v___x_2334_ = lean_st_ref_take(v_a_2332_);
v_vars_2335_ = lean_ctor_get(v___x_2334_, 0);
v_borrows_2336_ = lean_ctor_get(v___x_2334_, 1);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2338_ = v___x_2334_;
v_isShared_2339_ = v_isSharedCheck_2350_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_borrows_2336_);
lean_inc(v_vars_2335_);
lean_dec(v___x_2334_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2350_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v_vars_2343_; lean_object* v_borrows_2344_; lean_object* v___x_2346_; 
v___x_2340_ = lean_box(0);
v___x_2341_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_2342_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
lean_inc(v_fvarId_2331_);
v_vars_2343_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2341_, v___x_2342_, v_vars_2335_, v_fvarId_2331_);
v_borrows_2344_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2341_, v___x_2342_, v_borrows_2336_, v_fvarId_2331_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 1, v_borrows_2344_);
lean_ctor_set(v___x_2338_, 0, v_vars_2343_);
v___x_2346_ = v___x_2338_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_vars_2343_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_borrows_2344_);
v___x_2346_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = lean_st_ref_put(v_a_2332_, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2340_);
return v___x_2348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg___boxed(lean_object* v_fvarId_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(v_fvarId_2351_, v_a_2352_);
lean_dec(v_a_2352_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(lean_object* v_fvarId_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v___x_2363_; lean_object* v_vars_2364_; lean_object* v_borrows_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2379_; 
v___x_2363_ = lean_st_ref_take(v_a_2357_);
v_vars_2364_ = lean_ctor_get(v___x_2363_, 0);
v_borrows_2365_ = lean_ctor_get(v___x_2363_, 1);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2367_ = v___x_2363_;
v_isShared_2368_ = v_isSharedCheck_2379_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_borrows_2365_);
lean_inc(v_vars_2364_);
lean_dec(v___x_2363_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2379_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v_vars_2372_; lean_object* v_borrows_2373_; lean_object* v___x_2375_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_2371_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
lean_inc(v_fvarId_2355_);
v_vars_2372_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2370_, v___x_2371_, v_vars_2364_, v_fvarId_2355_);
v_borrows_2373_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2370_, v___x_2371_, v_borrows_2365_, v_fvarId_2355_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 1, v_borrows_2373_);
lean_ctor_set(v___x_2367_, 0, v_vars_2372_);
v___x_2375_ = v___x_2367_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_vars_2372_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v_borrows_2373_);
v___x_2375_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = lean_st_ref_put(v_a_2357_, v___x_2375_);
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2369_);
return v___x_2377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___boxed(lean_object* v_fvarId_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(v_fvarId_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(lean_object* v_liveVars_2389_, lean_object* v_derivedValMap_2390_, lean_object* v_x_2391_, lean_object* v_x_2392_){
_start:
{
if (lean_obj_tag(v_x_2392_) == 0)
{
return v_x_2391_;
}
else
{
lean_object* v_head_2393_; lean_object* v_tail_2394_; lean_object* v_cinfo_2413_; lean_object* v_parents_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v_head_2393_ = lean_ctor_get(v_x_2392_, 0);
lean_inc(v_head_2393_);
v_tail_2394_ = lean_ctor_get(v_x_2392_, 1);
lean_inc(v_tail_2394_);
lean_dec_ref_known(v_x_2392_, 2);
v_cinfo_2413_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2390_, v_head_2393_);
v_parents_2414_ = lean_ctor_get(v_cinfo_2413_, 0);
lean_inc_ref(v_parents_2414_);
lean_dec_ref(v_cinfo_2413_);
v___x_2415_ = lean_unsigned_to_nat(0u);
v___x_2416_ = lean_array_get_size(v_parents_2414_);
v___x_2417_ = lean_nat_dec_lt(v___x_2415_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_dec_ref(v_parents_2414_);
goto v___jp_2395_;
}
else
{
if (v___x_2417_ == 0)
{
lean_dec_ref(v_parents_2414_);
goto v___jp_2395_;
}
else
{
size_t v___x_2418_; size_t v___x_2419_; uint8_t v___x_2420_; 
v___x_2418_ = ((size_t)0ULL);
v___x_2419_ = lean_usize_of_nat(v___x_2416_);
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2391_, v_parents_2414_, v___x_2418_, v___x_2419_);
lean_dec_ref(v_parents_2414_);
if (v___x_2420_ == 0)
{
goto v___jp_2395_;
}
else
{
lean_object* v___x_2421_; 
v___x_2421_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2389_, v_head_2393_, v_derivedValMap_2390_, v_x_2391_);
lean_dec(v_head_2393_);
v_x_2391_ = v___x_2421_;
v_x_2392_ = v_tail_2394_;
goto _start;
}
}
}
v___jp_2395_:
{
lean_object* v_vars_2396_; uint8_t v___x_2397_; 
v_vars_2396_ = lean_ctor_get(v_liveVars_2389_, 0);
v___x_2397_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2396_, v_head_2393_);
if (v___x_2397_ == 0)
{
lean_object* v_vars_2398_; lean_object* v_borrows_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2410_; 
v_vars_2398_ = lean_ctor_get(v_x_2391_, 0);
v_borrows_2399_ = lean_ctor_get(v_x_2391_, 1);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_x_2391_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2401_ = v_x_2391_;
v_isShared_2402_ = v_isSharedCheck_2410_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_borrows_2399_);
lean_inc(v_vars_2398_);
lean_dec(v_x_2391_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2410_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2403_ = lean_box(0);
lean_inc(v_head_2393_);
v___x_2404_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2399_, v_head_2393_, v___x_2403_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 1, v___x_2404_);
v___x_2406_ = v___x_2401_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_vars_2398_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2407_; 
v___x_2407_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2389_, v_head_2393_, v_derivedValMap_2390_, v___x_2406_);
lean_dec(v_head_2393_);
v_x_2391_ = v___x_2407_;
v_x_2392_ = v_tail_2394_;
goto _start;
}
}
}
else
{
lean_object* v___x_2411_; 
v___x_2411_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2389_, v_head_2393_, v_derivedValMap_2390_, v_x_2391_);
lean_dec(v_head_2393_);
v_x_2391_ = v___x_2411_;
v_x_2392_ = v_tail_2394_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(lean_object* v_liveVars_2423_, lean_object* v_derivedValMap_2424_, lean_object* v_x_2425_, lean_object* v_x_2426_){
_start:
{
if (lean_obj_tag(v_x_2426_) == 0)
{
return v_x_2425_;
}
else
{
lean_object* v_head_2427_; lean_object* v_tail_2428_; lean_object* v_cinfo_2447_; lean_object* v_parents_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; 
v_head_2427_ = lean_ctor_get(v_x_2426_, 0);
lean_inc(v_head_2427_);
v_tail_2428_ = lean_ctor_get(v_x_2426_, 1);
lean_inc(v_tail_2428_);
lean_dec_ref_known(v_x_2426_, 2);
v_cinfo_2447_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2424_, v_head_2427_);
v_parents_2448_ = lean_ctor_get(v_cinfo_2447_, 0);
lean_inc_ref(v_parents_2448_);
lean_dec_ref(v_cinfo_2447_);
v___x_2449_ = lean_unsigned_to_nat(0u);
v___x_2450_ = lean_array_get_size(v_parents_2448_);
v___x_2451_ = lean_nat_dec_lt(v___x_2449_, v___x_2450_);
if (v___x_2451_ == 0)
{
lean_dec_ref(v_parents_2448_);
goto v___jp_2429_;
}
else
{
if (v___x_2451_ == 0)
{
lean_dec_ref(v_parents_2448_);
goto v___jp_2429_;
}
else
{
size_t v___x_2452_; size_t v___x_2453_; uint8_t v___x_2454_; 
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = lean_usize_of_nat(v___x_2450_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2425_, v_parents_2448_, v___x_2452_, v___x_2453_);
lean_dec_ref(v_parents_2448_);
if (v___x_2454_ == 0)
{
goto v___jp_2429_;
}
else
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2423_, v_head_2427_, v_derivedValMap_2424_, v_x_2425_);
lean_dec(v_head_2427_);
v___x_2456_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2423_, v_derivedValMap_2424_, v___x_2455_, v_tail_2428_);
return v___x_2456_;
}
}
}
v___jp_2429_:
{
lean_object* v_vars_2430_; uint8_t v___x_2431_; 
v_vars_2430_ = lean_ctor_get(v_liveVars_2423_, 0);
v___x_2431_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2430_, v_head_2427_);
if (v___x_2431_ == 0)
{
lean_object* v_vars_2432_; lean_object* v_borrows_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2444_; 
v_vars_2432_ = lean_ctor_get(v_x_2425_, 0);
v_borrows_2433_ = lean_ctor_get(v_x_2425_, 1);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_x_2425_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2435_ = v_x_2425_;
v_isShared_2436_ = v_isSharedCheck_2444_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_borrows_2433_);
lean_inc(v_vars_2432_);
lean_dec(v_x_2425_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2444_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2437_ = lean_box(0);
lean_inc(v_head_2427_);
v___x_2438_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2433_, v_head_2427_, v___x_2437_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 1, v___x_2438_);
v___x_2440_ = v___x_2435_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_vars_2432_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2423_, v_head_2427_, v_derivedValMap_2424_, v___x_2440_);
lean_dec(v_head_2427_);
v___x_2442_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2423_, v_derivedValMap_2424_, v___x_2441_, v_tail_2428_);
return v___x_2442_;
}
}
}
else
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2423_, v_head_2427_, v_derivedValMap_2424_, v_x_2425_);
lean_dec(v_head_2427_);
v___x_2446_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2423_, v_derivedValMap_2424_, v___x_2445_, v_tail_2428_);
return v___x_2446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(lean_object* v_liveVars_2457_, lean_object* v_fvarId_2458_, lean_object* v_derivedValMap_2459_, lean_object* v_liveVars_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_derivedValMap_2459_, v_fvarId_2458_);
if (lean_obj_tag(v___x_2461_) == 1)
{
lean_object* v_val_2462_; lean_object* v_children_2463_; lean_object* v___x_2464_; 
v_val_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_val_2462_);
lean_dec_ref_known(v___x_2461_, 1);
v_children_2463_ = lean_ctor_get(v_val_2462_, 1);
lean_inc(v_children_2463_);
lean_dec(v_val_2462_);
v___x_2464_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(v_liveVars_2457_, v_derivedValMap_2459_, v_liveVars_2460_, v_children_2463_);
return v___x_2464_;
}
else
{
lean_dec(v___x_2461_);
return v_liveVars_2460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0___boxed(lean_object* v_liveVars_2465_, lean_object* v_fvarId_2466_, lean_object* v_derivedValMap_2467_, lean_object* v_liveVars_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2465_, v_fvarId_2466_, v_derivedValMap_2467_, v_liveVars_2468_);
lean_dec(v_derivedValMap_2467_);
lean_dec(v_fvarId_2466_);
lean_dec_ref(v_liveVars_2465_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1___boxed(lean_object* v_liveVars_2470_, lean_object* v_derivedValMap_2471_, lean_object* v_x_2472_, lean_object* v_x_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2470_, v_derivedValMap_2471_, v_x_2472_, v_x_2473_);
lean_dec(v_derivedValMap_2471_);
lean_dec_ref(v_liveVars_2470_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0___boxed(lean_object* v_liveVars_2475_, lean_object* v_derivedValMap_2476_, lean_object* v_x_2477_, lean_object* v_x_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(v_liveVars_2475_, v_derivedValMap_2476_, v_x_2477_, v_x_2478_);
lean_dec(v_derivedValMap_2476_);
lean_dec_ref(v_liveVars_2475_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(lean_object* v_a_2480_, lean_object* v_liveVars_2481_, lean_object* v_x_2482_, lean_object* v_x_2483_){
_start:
{
if (lean_obj_tag(v_x_2483_) == 0)
{
return v_x_2482_;
}
else
{
lean_object* v_key_2484_; lean_object* v_tail_2485_; lean_object* v_derivedValMap_2486_; lean_object* v___x_2487_; 
v_key_2484_ = lean_ctor_get(v_x_2483_, 0);
v_tail_2485_ = lean_ctor_get(v_x_2483_, 2);
v_derivedValMap_2486_ = lean_ctor_get(v_a_2480_, 2);
v___x_2487_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2481_, v_key_2484_, v_derivedValMap_2486_, v_x_2482_);
v_x_2482_ = v___x_2487_;
v_x_2483_ = v_tail_2485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2___boxed(lean_object* v_a_2489_, lean_object* v_liveVars_2490_, lean_object* v_x_2491_, lean_object* v_x_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(v_a_2489_, v_liveVars_2490_, v_x_2491_, v_x_2492_);
lean_dec(v_x_2492_);
lean_dec_ref(v_liveVars_2490_);
lean_dec_ref(v_a_2489_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(lean_object* v_a_2494_, lean_object* v_liveVars_2495_, lean_object* v_x_2496_, lean_object* v_x_2497_){
_start:
{
if (lean_obj_tag(v_x_2497_) == 0)
{
return v_x_2496_;
}
else
{
lean_object* v_key_2498_; lean_object* v_tail_2499_; lean_object* v_derivedValMap_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v_key_2498_ = lean_ctor_get(v_x_2497_, 0);
v_tail_2499_ = lean_ctor_get(v_x_2497_, 2);
v_derivedValMap_2500_ = lean_ctor_get(v_a_2494_, 2);
v___x_2501_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2495_, v_key_2498_, v_derivedValMap_2500_, v_x_2496_);
v___x_2502_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(v_a_2494_, v_liveVars_2495_, v___x_2501_, v_tail_2499_);
return v___x_2502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1___boxed(lean_object* v_a_2503_, lean_object* v_liveVars_2504_, lean_object* v_x_2505_, lean_object* v_x_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(v_a_2503_, v_liveVars_2504_, v_x_2505_, v_x_2506_);
lean_dec(v_x_2506_);
lean_dec_ref(v_liveVars_2504_);
lean_dec_ref(v_a_2503_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(lean_object* v_a_2508_, lean_object* v_liveVars_2509_, lean_object* v_as_2510_, size_t v_i_2511_, size_t v_stop_2512_, lean_object* v_b_2513_){
_start:
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_usize_dec_eq(v_i_2511_, v_stop_2512_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; lean_object* v___x_2516_; size_t v___x_2517_; size_t v___x_2518_; 
v___x_2515_ = lean_array_uget_borrowed(v_as_2510_, v_i_2511_);
v___x_2516_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(v_a_2508_, v_liveVars_2509_, v_b_2513_, v___x_2515_);
v___x_2517_ = ((size_t)1ULL);
v___x_2518_ = lean_usize_add(v_i_2511_, v___x_2517_);
v_i_2511_ = v___x_2518_;
v_b_2513_ = v___x_2516_;
goto _start;
}
else
{
return v_b_2513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2___boxed(lean_object* v_a_2520_, lean_object* v_liveVars_2521_, lean_object* v_as_2522_, lean_object* v_i_2523_, lean_object* v_stop_2524_, lean_object* v_b_2525_){
_start:
{
size_t v_i_boxed_2526_; size_t v_stop_boxed_2527_; lean_object* v_res_2528_; 
v_i_boxed_2526_ = lean_unbox_usize(v_i_2523_);
lean_dec(v_i_2523_);
v_stop_boxed_2527_ = lean_unbox_usize(v_stop_2524_);
lean_dec(v_stop_2524_);
v_res_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2520_, v_liveVars_2521_, v_as_2522_, v_i_boxed_2526_, v_stop_boxed_2527_, v_b_2525_);
lean_dec_ref(v_as_2522_);
lean_dec_ref(v_liveVars_2521_);
lean_dec_ref(v_a_2520_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(lean_object* v_a_2529_, lean_object* v_liveVars_2530_, lean_object* v_x_2531_, lean_object* v_x_2532_){
_start:
{
if (lean_obj_tag(v_x_2532_) == 0)
{
return v_x_2531_;
}
else
{
lean_object* v_head_2533_; lean_object* v_tail_2534_; lean_object* v_derivedValMap_2535_; lean_object* v_vars_2536_; lean_object* v_borrows_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2548_; 
v_head_2533_ = lean_ctor_get(v_x_2532_, 0);
lean_inc(v_head_2533_);
v_tail_2534_ = lean_ctor_get(v_x_2532_, 1);
lean_inc(v_tail_2534_);
lean_dec_ref_known(v_x_2532_, 2);
v_derivedValMap_2535_ = lean_ctor_get(v_a_2529_, 2);
v_vars_2536_ = lean_ctor_get(v_x_2531_, 0);
v_borrows_2537_ = lean_ctor_get(v_x_2531_, 1);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_x_2531_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2539_ = v_x_2531_;
v_isShared_2540_ = v_isSharedCheck_2548_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_borrows_2537_);
lean_inc(v_vars_2536_);
lean_dec(v_x_2531_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2548_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2541_ = lean_box(0);
lean_inc(v_head_2533_);
v___x_2542_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2537_, v_head_2533_, v___x_2541_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 1, v___x_2542_);
v___x_2544_ = v___x_2539_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_vars_2536_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; 
v___x_2545_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2530_, v_head_2533_, v_derivedValMap_2535_, v___x_2544_);
lean_dec(v_head_2533_);
v_x_2531_ = v___x_2545_;
v_x_2532_ = v_tail_2534_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3___boxed(lean_object* v_a_2549_, lean_object* v_liveVars_2550_, lean_object* v_x_2551_, lean_object* v_x_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(v_a_2549_, v_liveVars_2550_, v_x_2551_, v_x_2552_);
lean_dec_ref(v_liveVars_2550_);
lean_dec_ref(v_a_2549_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(lean_object* v_liveVars_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v___y_2558_; lean_object* v_unconditionalBorrows_2569_; lean_object* v___x_2570_; lean_object* v_vars_2571_; lean_object* v_buckets_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v_unconditionalBorrows_2569_ = lean_ctor_get(v_a_2555_, 1);
lean_inc(v_unconditionalBorrows_2569_);
lean_inc_ref(v_liveVars_2554_);
v___x_2570_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(v_a_2555_, v_liveVars_2554_, v_liveVars_2554_, v_unconditionalBorrows_2569_);
v_vars_2571_ = lean_ctor_get(v_liveVars_2554_, 0);
v_buckets_2572_ = lean_ctor_get(v_vars_2571_, 1);
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = lean_array_get_size(v_buckets_2572_);
v___x_2575_ = lean_nat_dec_lt(v___x_2573_, v___x_2574_);
if (v___x_2575_ == 0)
{
v___y_2558_ = v___x_2570_;
goto v___jp_2557_;
}
else
{
size_t v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = ((size_t)0ULL);
v___x_2577_ = lean_usize_of_nat(v___x_2574_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2555_, v_liveVars_2554_, v_buckets_2572_, v___x_2576_, v___x_2577_, v___x_2570_);
v___y_2558_ = v___x_2578_;
goto v___jp_2557_;
}
v___jp_2557_:
{
lean_object* v_borrows_2559_; lean_object* v_buckets_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
v_borrows_2559_ = lean_ctor_get(v___y_2558_, 1);
v_buckets_2560_ = lean_ctor_get(v_borrows_2559_, 1);
v___x_2561_ = lean_unsigned_to_nat(0u);
v___x_2562_ = lean_array_get_size(v_buckets_2560_);
v___x_2563_ = lean_nat_dec_lt(v___x_2561_, v___x_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; 
lean_dec_ref(v_liveVars_2554_);
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___y_2558_);
return v___x_2564_;
}
else
{
size_t v___x_2565_; size_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_inc_ref(v_buckets_2560_);
v___x_2565_ = ((size_t)0ULL);
v___x_2566_ = lean_usize_of_nat(v___x_2562_);
v___x_2567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2555_, v_liveVars_2554_, v_buckets_2560_, v___x_2565_, v___x_2566_, v___y_2558_);
lean_dec_ref(v_buckets_2560_);
lean_dec_ref(v_liveVars_2554_);
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
return v___x_2568_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg___boxed(lean_object* v_liveVars_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v_liveVars_2579_, v_a_2580_);
lean_dec_ref(v_a_2580_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows(lean_object* v_liveVars_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v_liveVars_2583_, v_a_2584_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___boxed(lean_object* v_liveVars_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows(v_liveVars_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2616_; 
v___x_2604_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_2605_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_2604_, v_a_2601_);
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2616_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2616_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2610_ = lean_st_ref_take(v_a_2602_);
lean_dec(v___x_2610_);
v___x_2611_ = lean_box(0);
v___x_2612_ = lean_st_ref_put(v_a_2602_, v_a_2606_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2611_);
v___x_2614_ = v___x_2608_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2611_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg___boxed(lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(v_a_2617_, v_a_2618_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2640_; 
v___x_2628_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_2629_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_2628_, v_a_2621_);
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2632_ = v___x_2629_;
v_isShared_2633_ = v_isSharedCheck_2640_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2629_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2640_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
v___x_2634_ = lean_st_ref_take(v_a_2622_);
lean_dec(v___x_2634_);
v___x_2635_ = lean_box(0);
v___x_2636_ = lean_st_ref_put(v_a_2622_, v_a_2630_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 0, v___x_2635_);
v___x_2638_ = v___x_2632_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2635_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___boxed(lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(lean_object* v_fvarId_2649_, lean_object* v_k_2650_, lean_object* v_n_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_nat_dec_eq(v_n_2651_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v_varMap_2656_; lean_object* v___f_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; uint8_t v___y_2661_; uint8_t v_isDefiniteRef_2665_; 
v_varMap_2656_ = lean_ctor_get(v_a_2652_, 3);
v___f_2657_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_2658_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_fvarId_2649_);
lean_inc(v_varMap_2656_);
v___x_2659_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_2657_, v___x_2658_, v_varMap_2656_, v_fvarId_2649_);
v_isDefiniteRef_2665_ = lean_ctor_get_uint8(v___x_2659_, sizeof(void*)*2 + 1);
if (v_isDefiniteRef_2665_ == 0)
{
uint8_t v___x_2666_; 
v___x_2666_ = 1;
v___y_2661_ = v___x_2666_;
goto v___jp_2660_;
}
else
{
v___y_2661_ = v___x_2655_;
goto v___jp_2660_;
}
v___jp_2660_:
{
uint8_t v_persistent_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v_persistent_2662_ = lean_ctor_get_uint8(v___x_2659_, sizeof(void*)*2 + 2);
lean_dec(v___x_2659_);
v___x_2663_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_2663_, 0, v_fvarId_2649_);
lean_ctor_set(v___x_2663_, 1, v_n_2651_);
lean_ctor_set(v___x_2663_, 2, v_k_2650_);
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*3, v___y_2661_);
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*3 + 1, v_persistent_2662_);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
return v___x_2664_;
}
}
else
{
lean_object* v___x_2667_; 
lean_dec(v_n_2651_);
lean_dec(v_fvarId_2649_);
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v_k_2650_);
return v___x_2667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg___boxed(lean_object* v_fvarId_2668_, lean_object* v_k_2669_, lean_object* v_n_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(v_fvarId_2668_, v_k_2669_, v_n_2670_, v_a_2671_);
lean_dec_ref(v_a_2671_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(lean_object* v_fvarId_2674_, lean_object* v_k_2675_, lean_object* v_n_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = lean_unsigned_to_nat(0u);
v___x_2685_ = lean_nat_dec_eq(v_n_2676_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_object* v_varMap_2686_; lean_object* v___f_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___y_2691_; uint8_t v_isDefiniteRef_2695_; 
v_varMap_2686_ = lean_ctor_get(v_a_2677_, 3);
v___f_2687_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_2688_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_fvarId_2674_);
lean_inc(v_varMap_2686_);
v___x_2689_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_2687_, v___x_2688_, v_varMap_2686_, v_fvarId_2674_);
v_isDefiniteRef_2695_ = lean_ctor_get_uint8(v___x_2689_, sizeof(void*)*2 + 1);
if (v_isDefiniteRef_2695_ == 0)
{
uint8_t v___x_2696_; 
v___x_2696_ = 1;
v___y_2691_ = v___x_2696_;
goto v___jp_2690_;
}
else
{
v___y_2691_ = v___x_2685_;
goto v___jp_2690_;
}
v___jp_2690_:
{
uint8_t v_persistent_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v_persistent_2692_ = lean_ctor_get_uint8(v___x_2689_, sizeof(void*)*2 + 2);
lean_dec(v___x_2689_);
v___x_2693_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_2693_, 0, v_fvarId_2674_);
lean_ctor_set(v___x_2693_, 1, v_n_2676_);
lean_ctor_set(v___x_2693_, 2, v_k_2675_);
lean_ctor_set_uint8(v___x_2693_, sizeof(void*)*3, v___y_2691_);
lean_ctor_set_uint8(v___x_2693_, sizeof(void*)*3 + 1, v_persistent_2692_);
v___x_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
return v___x_2694_;
}
}
else
{
lean_object* v___x_2697_; 
lean_dec(v_n_2676_);
lean_dec(v_fvarId_2674_);
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v_k_2675_);
return v___x_2697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___boxed(lean_object* v_fvarId_2698_, lean_object* v_k_2699_, lean_object* v_n_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(v_fvarId_2698_, v_k_2699_, v_n_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0_spec__0(lean_object* v_msg_2709_){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_2711_ = lean_panic_fn_borrowed(v___x_2710_, v_msg_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(lean_object* v_t_2712_, lean_object* v_k_2713_){
_start:
{
if (lean_obj_tag(v_t_2712_) == 0)
{
lean_object* v_k_2714_; lean_object* v_v_2715_; lean_object* v_l_2716_; lean_object* v_r_2717_; uint8_t v___x_2718_; 
v_k_2714_ = lean_ctor_get(v_t_2712_, 1);
v_v_2715_ = lean_ctor_get(v_t_2712_, 2);
v_l_2716_ = lean_ctor_get(v_t_2712_, 3);
v_r_2717_ = lean_ctor_get(v_t_2712_, 4);
v___x_2718_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2713_, v_k_2714_);
switch(v___x_2718_)
{
case 0:
{
v_t_2712_ = v_l_2716_;
goto _start;
}
case 1:
{
lean_inc(v_v_2715_);
return v_v_2715_;
}
default: 
{
v_t_2712_ = v_r_2717_;
goto _start;
}
}
}
else
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3);
v___x_2722_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0_spec__0(v___x_2721_);
return v___x_2722_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0___boxed(lean_object* v_t_2723_, lean_object* v_k_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_t_2723_, v_k_2724_);
lean_dec(v_k_2724_);
lean_dec(v_t_2723_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(lean_object* v_fvarId_2726_, lean_object* v_k_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v_varMap_2730_; lean_object* v___x_2731_; lean_object* v_ctorInfo_2732_; 
v_varMap_2730_ = lean_ctor_get(v_a_2728_, 3);
v___x_2731_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_2730_, v_fvarId_2726_);
v_ctorInfo_2732_ = lean_ctor_get(v___x_2731_, 1);
lean_inc(v_ctorInfo_2732_);
if (lean_obj_tag(v_ctorInfo_2732_) == 0)
{
uint8_t v_isDefiniteRef_2733_; uint8_t v_persistent_2734_; lean_object* v___x_2735_; uint8_t v___y_2737_; 
v_isDefiniteRef_2733_ = lean_ctor_get_uint8(v___x_2731_, sizeof(void*)*2 + 1);
v_persistent_2734_ = lean_ctor_get_uint8(v___x_2731_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_2731_);
v___x_2735_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_2733_ == 0)
{
uint8_t v___x_2741_; 
v___x_2741_ = 1;
v___y_2737_ = v___x_2741_;
goto v___jp_2736_;
}
else
{
uint8_t v___x_2742_; 
v___x_2742_ = 0;
v___y_2737_ = v___x_2742_;
goto v___jp_2736_;
}
v___jp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2738_ = lean_box(0);
v___x_2739_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_2739_, 0, v_fvarId_2726_);
lean_ctor_set(v___x_2739_, 1, v___x_2735_);
lean_ctor_set(v___x_2739_, 2, v___x_2738_);
lean_ctor_set(v___x_2739_, 3, v_k_2727_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*4, v___y_2737_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*4 + 1, v_persistent_2734_);
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
return v___x_2740_;
}
}
else
{
uint8_t v_persistent_2743_; lean_object* v_val_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2758_; 
v_persistent_2743_ = lean_ctor_get_uint8(v___x_2731_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_2731_);
v_val_2744_ = lean_ctor_get(v_ctorInfo_2732_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_ctorInfo_2732_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2746_ = v_ctorInfo_2732_;
v_isShared_2747_ = v_isSharedCheck_2758_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_val_2744_);
lean_dec(v_ctorInfo_2732_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2758_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
uint8_t v___x_2748_; 
v___x_2748_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_val_2744_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; 
lean_del_object(v___x_2746_);
lean_dec(v_val_2744_);
lean_dec(v_fvarId_2726_);
v___x_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_k_2727_);
return v___x_2749_;
}
else
{
lean_object* v_size_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; lean_object* v___x_2754_; 
v_size_2750_ = lean_ctor_get(v_val_2744_, 2);
lean_inc(v_size_2750_);
lean_dec(v_val_2744_);
v___x_2751_ = lean_unsigned_to_nat(1u);
v___x_2752_ = 0;
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v_size_2750_);
v___x_2754_ = v___x_2746_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_size_2750_);
v___x_2754_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_2755_, 0, v_fvarId_2726_);
lean_ctor_set(v___x_2755_, 1, v___x_2751_);
lean_ctor_set(v___x_2755_, 2, v___x_2754_);
lean_ctor_set(v___x_2755_, 3, v_k_2727_);
lean_ctor_set_uint8(v___x_2755_, sizeof(void*)*4, v___x_2752_);
lean_ctor_set_uint8(v___x_2755_, sizeof(void*)*4 + 1, v_persistent_2743_);
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
return v___x_2756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg___boxed(lean_object* v_fvarId_2759_, lean_object* v_k_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_2759_, v_k_2760_, v_a_2761_);
lean_dec_ref(v_a_2761_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(lean_object* v_fvarId_2764_, lean_object* v_k_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_2764_, v_k_2765_, v_a_2766_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___boxed(lean_object* v_fvarId_2774_, lean_object* v_k_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(v_fvarId_2774_, v_k_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
lean_dec(v_a_2779_);
lean_dec_ref(v_a_2778_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
return v_res_2783_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(lean_object* v_x_2784_, lean_object* v_x_2785_){
_start:
{
lean_object* v_snd_2786_; lean_object* v_snd_2787_; uint8_t v___x_2788_; 
v_snd_2786_ = lean_ctor_get(v_x_2784_, 1);
v_snd_2787_ = lean_ctor_get(v_x_2785_, 1);
v___x_2788_ = lean_nat_dec_lt(v_snd_2786_, v_snd_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0___boxed(lean_object* v_x_2789_, lean_object* v_x_2790_){
_start:
{
uint8_t v_res_2791_; lean_object* v_r_2792_; 
v_res_2791_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v_x_2789_, v_x_2790_);
lean_dec_ref(v_x_2790_);
lean_dec_ref(v_x_2789_);
v_r_2792_ = lean_box(v_res_2791_);
return v_r_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(lean_object* v_hi_2793_, lean_object* v_pivot_2794_, lean_object* v_as_2795_, lean_object* v_i_2796_, lean_object* v_k_2797_){
_start:
{
uint8_t v___x_2798_; 
v___x_2798_ = lean_nat_dec_lt(v_k_2797_, v_hi_2793_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_dec(v_k_2797_);
v___x_2799_ = lean_array_fswap(v_as_2795_, v_i_2796_, v_hi_2793_);
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v_i_2796_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
return v___x_2800_;
}
else
{
lean_object* v___x_2801_; lean_object* v_snd_2802_; lean_object* v_snd_2803_; uint8_t v___x_2804_; 
v___x_2801_ = lean_array_fget_borrowed(v_as_2795_, v_k_2797_);
v_snd_2802_ = lean_ctor_get(v___x_2801_, 1);
v_snd_2803_ = lean_ctor_get(v_pivot_2794_, 1);
v___x_2804_ = lean_nat_dec_lt(v_snd_2802_, v_snd_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = lean_unsigned_to_nat(1u);
v___x_2806_ = lean_nat_add(v_k_2797_, v___x_2805_);
lean_dec(v_k_2797_);
v_k_2797_ = v___x_2806_;
goto _start;
}
else
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2808_ = lean_array_fswap(v_as_2795_, v_i_2796_, v_k_2797_);
v___x_2809_ = lean_unsigned_to_nat(1u);
v___x_2810_ = lean_nat_add(v_i_2796_, v___x_2809_);
lean_dec(v_i_2796_);
v___x_2811_ = lean_nat_add(v_k_2797_, v___x_2809_);
lean_dec(v_k_2797_);
v_as_2795_ = v___x_2808_;
v_i_2796_ = v___x_2810_;
v_k_2797_ = v___x_2811_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg___boxed(lean_object* v_hi_2813_, lean_object* v_pivot_2814_, lean_object* v_as_2815_, lean_object* v_i_2816_, lean_object* v_k_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(v_hi_2813_, v_pivot_2814_, v_as_2815_, v_i_2816_, v_k_2817_);
lean_dec_ref(v_pivot_2814_);
lean_dec(v_hi_2813_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(lean_object* v_n_2819_, lean_object* v_as_2820_, lean_object* v_lo_2821_, lean_object* v_hi_2822_){
_start:
{
lean_object* v___y_2824_; uint8_t v___x_2834_; 
v___x_2834_ = lean_nat_dec_lt(v_lo_2821_, v_hi_2822_);
if (v___x_2834_ == 0)
{
lean_dec(v_lo_2821_);
return v_as_2820_;
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v_mid_2837_; lean_object* v___y_2839_; lean_object* v___y_2845_; lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2835_ = lean_nat_add(v_lo_2821_, v_hi_2822_);
v___x_2836_ = lean_unsigned_to_nat(1u);
v_mid_2837_ = lean_nat_shiftr(v___x_2835_, v___x_2836_);
lean_dec(v___x_2835_);
v___x_2850_ = lean_array_fget_borrowed(v_as_2820_, v_mid_2837_);
v___x_2851_ = lean_array_fget_borrowed(v_as_2820_, v_lo_2821_);
v___x_2852_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v___x_2850_, v___x_2851_);
if (v___x_2852_ == 0)
{
v___y_2845_ = v_as_2820_;
goto v___jp_2844_;
}
else
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_array_fswap(v_as_2820_, v_lo_2821_, v_mid_2837_);
v___y_2845_ = v___x_2853_;
goto v___jp_2844_;
}
v___jp_2838_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2840_ = lean_array_fget_borrowed(v___y_2839_, v_mid_2837_);
v___x_2841_ = lean_array_fget_borrowed(v___y_2839_, v_hi_2822_);
v___x_2842_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v___x_2840_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_dec(v_mid_2837_);
v___y_2824_ = v___y_2839_;
goto v___jp_2823_;
}
else
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_array_fswap(v___y_2839_, v_mid_2837_, v_hi_2822_);
lean_dec(v_mid_2837_);
v___y_2824_ = v___x_2843_;
goto v___jp_2823_;
}
}
v___jp_2844_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2846_ = lean_array_fget_borrowed(v___y_2845_, v_hi_2822_);
v___x_2847_ = lean_array_fget_borrowed(v___y_2845_, v_lo_2821_);
v___x_2848_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v___x_2846_, v___x_2847_);
if (v___x_2848_ == 0)
{
v___y_2839_ = v___y_2845_;
goto v___jp_2838_;
}
else
{
lean_object* v___x_2849_; 
v___x_2849_ = lean_array_fswap(v___y_2845_, v_lo_2821_, v_hi_2822_);
v___y_2839_ = v___x_2849_;
goto v___jp_2838_;
}
}
}
v___jp_2823_:
{
lean_object* v_pivot_2825_; lean_object* v___x_2826_; lean_object* v_fst_2827_; lean_object* v_snd_2828_; uint8_t v___x_2829_; 
v_pivot_2825_ = lean_array_fget(v___y_2824_, v_hi_2822_);
lean_inc_n(v_lo_2821_, 2);
v___x_2826_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(v_hi_2822_, v_pivot_2825_, v___y_2824_, v_lo_2821_, v_lo_2821_);
lean_dec(v_pivot_2825_);
v_fst_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_fst_2827_);
v_snd_2828_ = lean_ctor_get(v___x_2826_, 1);
lean_inc(v_snd_2828_);
lean_dec_ref(v___x_2826_);
v___x_2829_ = lean_nat_dec_le(v_hi_2822_, v_fst_2827_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2830_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_n_2819_, v_snd_2828_, v_lo_2821_, v_fst_2827_);
v___x_2831_ = lean_unsigned_to_nat(1u);
v___x_2832_ = lean_nat_add(v_fst_2827_, v___x_2831_);
lean_dec(v_fst_2827_);
v_as_2820_ = v___x_2830_;
v_lo_2821_ = v___x_2832_;
goto _start;
}
else
{
lean_dec(v_fst_2827_);
lean_dec(v_lo_2821_);
return v_snd_2828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___boxed(lean_object* v_n_2854_, lean_object* v_as_2855_, lean_object* v_lo_2856_, lean_object* v_hi_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_n_2854_, v_as_2855_, v_lo_2856_, v_hi_2857_);
lean_dec(v_hi_2857_);
lean_dec(v_n_2854_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(lean_object* v_altLiveVars_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
if (lean_obj_tag(v_a_2860_) == 0)
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2865_, 0, v_a_2861_);
v___x_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
return v___x_2866_;
}
else
{
lean_object* v_key_2867_; lean_object* v_tail_2868_; lean_object* v_fst_2869_; lean_object* v_snd_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2921_; 
v_key_2867_ = lean_ctor_get(v_a_2860_, 0);
v_tail_2868_ = lean_ctor_get(v_a_2860_, 2);
v_fst_2869_ = lean_ctor_get(v_a_2861_, 0);
v_snd_2870_ = lean_ctor_get(v_a_2861_, 1);
v_isSharedCheck_2921_ = !lean_is_exclusive(v_a_2861_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2872_ = v_a_2861_;
v_isShared_2873_ = v_isSharedCheck_2921_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_snd_2870_);
lean_inc(v_fst_2869_);
lean_dec(v_a_2861_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2921_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v_varMap_2874_; lean_object* v_vars_2875_; lean_object* v_borrows_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; 
v_varMap_2874_ = lean_ctor_get(v___y_2862_, 3);
v_vars_2875_ = lean_ctor_get(v_altLiveVars_2859_, 0);
v_borrows_2876_ = lean_ctor_get(v_altLiveVars_2859_, 1);
v___x_2877_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_2874_, v_key_2867_);
v___x_2878_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2875_, v_key_2867_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; uint8_t v_isPossibleRef_2885_; 
v___x_2879_ = lean_st_ref_get(v___y_2863_);
v_isPossibleRef_2885_ = lean_ctor_get_uint8(v___x_2877_, sizeof(void*)*2);
if (v_isPossibleRef_2885_ == 0)
{
lean_dec(v___x_2879_);
lean_dec_ref(v___x_2877_);
goto v___jp_2880_;
}
else
{
lean_object* v_idx_2886_; lean_object* v_borrows_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2898_; 
v_idx_2886_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_idx_2886_);
lean_dec_ref(v___x_2877_);
v_borrows_2887_ = lean_ctor_get(v___x_2879_, 1);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v___x_2879_, 0);
lean_dec(v_unused_2899_);
v___x_2889_ = v___x_2879_;
v_isShared_2890_ = v_isSharedCheck_2898_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_borrows_2887_);
lean_dec(v___x_2879_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2898_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
uint8_t v___x_2891_; 
v___x_2891_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_2887_, v_key_2867_);
lean_dec_ref(v_borrows_2887_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2893_; 
lean_del_object(v___x_2872_);
lean_inc(v_key_2867_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 1, v_idx_2886_);
lean_ctor_set(v___x_2889_, 0, v_key_2867_);
v___x_2893_ = v___x_2889_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_key_2867_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_idx_2886_);
v___x_2893_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = lean_array_push(v_snd_2870_, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v_fst_2869_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v_a_2860_ = v_tail_2868_;
v_a_2861_ = v___x_2895_;
goto _start;
}
}
else
{
lean_del_object(v___x_2889_);
lean_dec(v_idx_2886_);
goto v___jp_2880_;
}
}
}
v___jp_2880_:
{
lean_object* v___x_2882_; 
if (v_isShared_2873_ == 0)
{
v___x_2882_ = v___x_2872_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_fst_2869_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_snd_2870_);
v___x_2882_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
v_a_2860_ = v_tail_2868_;
v_a_2861_ = v___x_2882_;
goto _start;
}
}
}
else
{
lean_object* v___x_2900_; lean_object* v_borrows_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2919_; 
v___x_2900_ = lean_st_ref_get(v___y_2863_);
v_borrows_2906_ = lean_ctor_get(v___x_2900_, 1);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v___x_2900_, 0);
lean_dec(v_unused_2920_);
v___x_2908_ = v___x_2900_;
v_isShared_2909_ = v_isSharedCheck_2919_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_borrows_2906_);
lean_dec(v___x_2900_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2919_;
goto v_resetjp_2907_;
}
v___jp_2901_:
{
lean_object* v___x_2903_; 
if (v_isShared_2873_ == 0)
{
v___x_2903_ = v___x_2872_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_fst_2869_);
lean_ctor_set(v_reuseFailAlloc_2905_, 1, v_snd_2870_);
v___x_2903_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
v_a_2860_ = v_tail_2868_;
v_a_2861_ = v___x_2903_;
goto _start;
}
}
v_resetjp_2907_:
{
uint8_t v___x_2910_; 
v___x_2910_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_2906_, v_key_2867_);
lean_dec_ref(v_borrows_2906_);
if (v___x_2910_ == 0)
{
lean_del_object(v___x_2908_);
lean_dec_ref(v___x_2877_);
goto v___jp_2901_;
}
else
{
uint8_t v___x_2911_; 
v___x_2911_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_2876_, v_key_2867_);
if (v___x_2911_ == 0)
{
if (v___x_2910_ == 0)
{
lean_del_object(v___x_2908_);
lean_dec_ref(v___x_2877_);
goto v___jp_2901_;
}
else
{
lean_object* v_idx_2912_; lean_object* v___x_2914_; 
lean_del_object(v___x_2872_);
v_idx_2912_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_idx_2912_);
lean_dec_ref(v___x_2877_);
lean_inc(v_key_2867_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 1, v_idx_2912_);
lean_ctor_set(v___x_2908_, 0, v_key_2867_);
v___x_2914_ = v___x_2908_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_key_2867_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_idx_2912_);
v___x_2914_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = lean_array_push(v_fst_2869_, v___x_2914_);
v___x_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
lean_ctor_set(v___x_2916_, 1, v_snd_2870_);
v_a_2860_ = v_tail_2868_;
v_a_2861_ = v___x_2916_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_2908_);
lean_dec_ref(v___x_2877_);
goto v___jp_2901_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___boxed(lean_object* v_altLiveVars_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_2922_, v_a_2923_, v_a_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v_a_2923_);
lean_dec_ref(v_altLiveVars_2922_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(lean_object* v_altLiveVars_2929_, lean_object* v_as_2930_, size_t v_sz_2931_, size_t v_i_2932_, lean_object* v_b_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
uint8_t v___x_2941_; 
v___x_2941_ = lean_usize_dec_lt(v_i_2932_, v_sz_2931_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_b_2933_);
return v___x_2942_;
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2944_; 
v_a_2943_ = lean_array_uget_borrowed(v_as_2930_, v_i_2932_);
v___x_2944_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_2929_, v_a_2943_, v_b_2933_, v___y_2934_, v___y_2935_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2957_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_2957_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2957_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
if (lean_obj_tag(v_a_2945_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; 
v_a_2949_ = lean_ctor_get(v_a_2945_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v_a_2945_, 1);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v_a_2949_);
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2949_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
else
{
lean_object* v_a_2953_; size_t v___x_2954_; size_t v___x_2955_; 
lean_del_object(v___x_2947_);
v_a_2953_ = lean_ctor_get(v_a_2945_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v_a_2945_, 1);
v___x_2954_ = ((size_t)1ULL);
v___x_2955_ = lean_usize_add(v_i_2932_, v___x_2954_);
v_i_2932_ = v___x_2955_;
v_b_2933_ = v_a_2953_;
goto _start;
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
v_a_2958_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2944_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2944_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___boxed(lean_object* v_altLiveVars_2966_, lean_object* v_as_2967_, lean_object* v_sz_2968_, lean_object* v_i_2969_, lean_object* v_b_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
size_t v_sz_boxed_2978_; size_t v_i_boxed_2979_; lean_object* v_res_2980_; 
v_sz_boxed_2978_ = lean_unbox_usize(v_sz_2968_);
lean_dec(v_sz_2968_);
v_i_boxed_2979_ = lean_unbox_usize(v_i_2969_);
lean_dec(v_i_2969_);
v_res_2980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(v_altLiveVars_2966_, v_as_2967_, v_sz_boxed_2978_, v_i_boxed_2979_, v_b_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec_ref(v_as_2967_);
lean_dec_ref(v_altLiveVars_2966_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(lean_object* v_as_2981_, size_t v_i_2982_, size_t v_stop_2983_, lean_object* v_b_2984_, lean_object* v___y_2985_){
_start:
{
uint8_t v___x_2987_; 
v___x_2987_ = lean_usize_dec_eq(v_i_2982_, v_stop_2983_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; lean_object* v_fst_2989_; lean_object* v___x_2990_; 
v___x_2988_ = lean_array_uget_borrowed(v_as_2981_, v_i_2982_);
v_fst_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_fst_2989_);
v___x_2990_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fst_2989_, v_b_2984_, v___y_2985_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; size_t v___x_2992_; size_t v___x_2993_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
v___x_2992_ = ((size_t)1ULL);
v___x_2993_ = lean_usize_add(v_i_2982_, v___x_2992_);
v_i_2982_ = v___x_2993_;
v_b_2984_ = v_a_2991_;
goto _start;
}
else
{
return v___x_2990_;
}
}
else
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2995_, 0, v_b_2984_);
return v___x_2995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___boxed(lean_object* v_as_2996_, lean_object* v_i_2997_, lean_object* v_stop_2998_, lean_object* v_b_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
size_t v_i_boxed_3002_; size_t v_stop_boxed_3003_; lean_object* v_res_3004_; 
v_i_boxed_3002_ = lean_unbox_usize(v_i_2997_);
lean_dec(v_i_2997_);
v_stop_boxed_3003_ = lean_unbox_usize(v_stop_2998_);
lean_dec(v_stop_2998_);
v_res_3004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_as_2996_, v_i_boxed_3002_, v_stop_boxed_3003_, v_b_2999_, v___y_3000_);
lean_dec_ref(v___y_3000_);
lean_dec_ref(v_as_2996_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(lean_object* v_as_3005_, size_t v_i_3006_, size_t v_stop_3007_, lean_object* v_b_3008_, lean_object* v___y_3009_){
_start:
{
uint8_t v___x_3011_; 
v___x_3011_ = lean_usize_dec_eq(v_i_3006_, v_stop_3007_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; lean_object* v_fst_3013_; lean_object* v_varMap_3014_; lean_object* v___x_3015_; uint8_t v_isDefiniteRef_3016_; lean_object* v___x_3017_; uint8_t v___y_3019_; 
v___x_3012_ = lean_array_uget_borrowed(v_as_3005_, v_i_3006_);
v_fst_3013_ = lean_ctor_get(v___x_3012_, 0);
v_varMap_3014_ = lean_ctor_get(v___y_3009_, 3);
v___x_3015_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3014_, v_fst_3013_);
v_isDefiniteRef_3016_ = lean_ctor_get_uint8(v___x_3015_, sizeof(void*)*2 + 1);
v___x_3017_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_3016_ == 0)
{
uint8_t v___x_3025_; 
v___x_3025_ = 1;
v___y_3019_ = v___x_3025_;
goto v___jp_3018_;
}
else
{
v___y_3019_ = v___x_3011_;
goto v___jp_3018_;
}
v___jp_3018_:
{
uint8_t v_persistent_3020_; lean_object* v___x_3021_; size_t v___x_3022_; size_t v___x_3023_; 
v_persistent_3020_ = lean_ctor_get_uint8(v___x_3015_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_3015_);
lean_inc(v_fst_3013_);
v___x_3021_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_3021_, 0, v_fst_3013_);
lean_ctor_set(v___x_3021_, 1, v___x_3017_);
lean_ctor_set(v___x_3021_, 2, v_b_3008_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*3, v___y_3019_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*3 + 1, v_persistent_3020_);
v___x_3022_ = ((size_t)1ULL);
v___x_3023_ = lean_usize_add(v_i_3006_, v___x_3022_);
v_i_3006_ = v___x_3023_;
v_b_3008_ = v___x_3021_;
goto _start;
}
}
else
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3026_, 0, v_b_3008_);
return v___x_3026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg___boxed(lean_object* v_as_3027_, lean_object* v_i_3028_, lean_object* v_stop_3029_, lean_object* v_b_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
size_t v_i_boxed_3033_; size_t v_stop_boxed_3034_; lean_object* v_res_3035_; 
v_i_boxed_3033_ = lean_unbox_usize(v_i_3028_);
lean_dec(v_i_3028_);
v_stop_boxed_3034_ = lean_unbox_usize(v_stop_3029_);
lean_dec(v_stop_3029_);
v_res_3035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v_as_3027_, v_i_boxed_3033_, v_stop_boxed_3034_, v_b_3030_, v___y_3031_);
lean_dec_ref(v___y_3031_);
lean_dec_ref(v_as_3027_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(lean_object* v_altLiveVars_3040_, lean_object* v_k_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v_vars_3051_; lean_object* v___x_3052_; lean_object* v_buckets_3053_; size_t v_sz_3054_; size_t v___x_3055_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___x_3067_; 
v___x_3049_ = lean_unsigned_to_nat(0u);
v___x_3050_ = lean_st_ref_get(v_a_3043_);
v_vars_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc_ref(v_vars_3051_);
lean_dec(v___x_3050_);
v___x_3052_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1));
v_buckets_3053_ = lean_ctor_get(v_vars_3051_, 1);
lean_inc_ref(v_buckets_3053_);
lean_dec_ref(v_vars_3051_);
v_sz_3054_ = lean_array_size(v_buckets_3053_);
v___x_3055_ = ((size_t)0ULL);
v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(v_altLiveVars_3040_, v_buckets_3053_, v_sz_3054_, v___x_3055_, v___x_3052_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
lean_dec_ref(v_buckets_3053_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3125_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3070_ = v___x_3067_;
v_isShared_3071_ = v_isSharedCheck_3125_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3125_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v_fst_3072_; lean_object* v_snd_3073_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___x_3088_; lean_object* v___y_3090_; lean_object* v_a_3091_; lean_object* v___y_3097_; lean_object* v___y_3100_; lean_object* v___x_3114_; lean_object* v___y_3116_; lean_object* v___y_3117_; uint8_t v___x_3119_; 
v_fst_3072_ = lean_ctor_get(v_a_3068_, 0);
lean_inc(v_fst_3072_);
v_snd_3073_ = lean_ctor_get(v_a_3068_, 1);
lean_inc(v_snd_3073_);
lean_dec(v_a_3068_);
v___x_3088_ = lean_unsigned_to_nat(1u);
v___x_3114_ = lean_array_get_size(v_snd_3073_);
v___x_3119_ = lean_nat_dec_eq(v___x_3114_, v___x_3049_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; lean_object* v___y_3122_; uint8_t v___x_3124_; 
v___x_3120_ = lean_nat_sub(v___x_3114_, v___x_3088_);
v___x_3124_ = lean_nat_dec_le(v___x_3049_, v___x_3120_);
if (v___x_3124_ == 0)
{
lean_inc(v___x_3120_);
v___y_3122_ = v___x_3120_;
goto v___jp_3121_;
}
else
{
v___y_3122_ = v___x_3049_;
goto v___jp_3121_;
}
v___jp_3121_:
{
uint8_t v___x_3123_; 
v___x_3123_ = lean_nat_dec_le(v___y_3122_, v___x_3120_);
if (v___x_3123_ == 0)
{
lean_dec(v___x_3120_);
lean_inc(v___y_3122_);
v___y_3116_ = v___y_3122_;
v___y_3117_ = v___y_3122_;
goto v___jp_3115_;
}
else
{
v___y_3116_ = v___y_3122_;
v___y_3117_ = v___x_3120_;
goto v___jp_3115_;
}
}
}
else
{
v___y_3100_ = v_snd_3073_;
goto v___jp_3099_;
}
v___jp_3074_:
{
lean_object* v___x_3080_; 
v___x_3080_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v___y_3077_, v_fst_3072_, v___y_3076_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec(v___y_3077_);
v___y_3057_ = v___y_3075_;
v___y_3058_ = v___y_3078_;
v___y_3059_ = v___x_3080_;
goto v___jp_3056_;
}
v___jp_3081_:
{
uint8_t v___x_3087_; 
v___x_3087_ = lean_nat_dec_le(v___y_3086_, v___y_3085_);
if (v___x_3087_ == 0)
{
lean_dec(v___y_3085_);
lean_inc(v___y_3086_);
v___y_3075_ = v___y_3082_;
v___y_3076_ = v___y_3086_;
v___y_3077_ = v___y_3083_;
v___y_3078_ = v___y_3084_;
v___y_3079_ = v___y_3086_;
goto v___jp_3074_;
}
else
{
v___y_3075_ = v___y_3082_;
v___y_3076_ = v___y_3086_;
v___y_3077_ = v___y_3083_;
v___y_3078_ = v___y_3084_;
v___y_3079_ = v___y_3085_;
goto v___jp_3074_;
}
}
v___jp_3089_:
{
lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3092_ = lean_array_get_size(v_fst_3072_);
v___x_3093_ = lean_nat_dec_eq(v___x_3092_, v___x_3049_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3094_ = lean_nat_sub(v___x_3092_, v___x_3088_);
v___x_3095_ = lean_nat_dec_le(v___x_3049_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_inc(v___x_3094_);
v___y_3082_ = v_a_3091_;
v___y_3083_ = v___x_3092_;
v___y_3084_ = v___y_3090_;
v___y_3085_ = v___x_3094_;
v___y_3086_ = v___x_3094_;
goto v___jp_3081_;
}
else
{
v___y_3082_ = v_a_3091_;
v___y_3083_ = v___x_3092_;
v___y_3084_ = v___y_3090_;
v___y_3085_ = v___x_3094_;
v___y_3086_ = v___x_3049_;
goto v___jp_3081_;
}
}
else
{
v___y_3057_ = v_a_3091_;
v___y_3058_ = v___y_3090_;
v___y_3059_ = v_fst_3072_;
goto v___jp_3056_;
}
}
v___jp_3096_:
{
if (lean_obj_tag(v___y_3097_) == 0)
{
lean_object* v_a_3098_; 
v_a_3098_ = lean_ctor_get(v___y_3097_, 0);
lean_inc(v_a_3098_);
v___y_3090_ = v___y_3097_;
v_a_3091_ = v_a_3098_;
goto v___jp_3089_;
}
else
{
lean_dec(v_fst_3072_);
return v___y_3097_;
}
}
v___jp_3099_:
{
lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = lean_array_get_size(v___y_3100_);
v___x_3102_ = lean_nat_dec_lt(v___x_3049_, v___x_3101_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3104_; 
lean_dec_ref(v___y_3100_);
lean_inc_ref(v_k_3041_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v_k_3041_);
v___x_3104_ = v___x_3070_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_k_3041_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
v___y_3090_ = v___x_3104_;
v_a_3091_ = v_k_3041_;
goto v___jp_3089_;
}
}
else
{
uint8_t v___x_3106_; 
v___x_3106_ = lean_nat_dec_le(v___x_3101_, v___x_3101_);
if (v___x_3106_ == 0)
{
if (v___x_3102_ == 0)
{
lean_object* v___x_3108_; 
lean_dec_ref(v___y_3100_);
lean_inc_ref(v_k_3041_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v_k_3041_);
v___x_3108_ = v___x_3070_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_k_3041_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
v___y_3090_ = v___x_3108_;
v_a_3091_ = v_k_3041_;
goto v___jp_3089_;
}
}
else
{
size_t v___x_3110_; lean_object* v___x_3111_; 
lean_del_object(v___x_3070_);
v___x_3110_ = lean_usize_of_nat(v___x_3101_);
v___x_3111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v___y_3100_, v___x_3055_, v___x_3110_, v_k_3041_, v_a_3042_);
lean_dec_ref(v___y_3100_);
v___y_3097_ = v___x_3111_;
goto v___jp_3096_;
}
}
else
{
size_t v___x_3112_; lean_object* v___x_3113_; 
lean_del_object(v___x_3070_);
v___x_3112_ = lean_usize_of_nat(v___x_3101_);
v___x_3113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v___y_3100_, v___x_3055_, v___x_3112_, v_k_3041_, v_a_3042_);
lean_dec_ref(v___y_3100_);
v___y_3097_ = v___x_3113_;
goto v___jp_3096_;
}
}
}
v___jp_3115_:
{
lean_object* v___x_3118_; 
v___x_3118_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v___x_3114_, v_snd_3073_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
v___y_3100_ = v___x_3118_;
goto v___jp_3099_;
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v_k_3041_);
v_a_3126_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3067_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3067_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
v___jp_3056_:
{
lean_object* v___x_3060_; uint8_t v___x_3061_; 
v___x_3060_ = lean_array_get_size(v___y_3059_);
v___x_3061_ = lean_nat_dec_lt(v___x_3049_, v___x_3060_);
if (v___x_3061_ == 0)
{
lean_dec_ref(v___y_3059_);
lean_dec_ref(v___y_3057_);
return v___y_3058_;
}
else
{
uint8_t v___x_3062_; 
v___x_3062_ = lean_nat_dec_le(v___x_3060_, v___x_3060_);
if (v___x_3062_ == 0)
{
if (v___x_3061_ == 0)
{
lean_dec_ref(v___y_3059_);
lean_dec_ref(v___y_3057_);
return v___y_3058_;
}
else
{
size_t v___x_3063_; lean_object* v___x_3064_; 
lean_dec_ref(v___y_3058_);
v___x_3063_ = lean_usize_of_nat(v___x_3060_);
v___x_3064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v___y_3059_, v___x_3055_, v___x_3063_, v___y_3057_, v_a_3042_);
lean_dec_ref(v___y_3059_);
return v___x_3064_;
}
}
else
{
size_t v___x_3065_; lean_object* v___x_3066_; 
lean_dec_ref(v___y_3058_);
v___x_3065_ = lean_usize_of_nat(v___x_3060_);
v___x_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v___y_3059_, v___x_3055_, v___x_3065_, v___y_3057_, v_a_3042_);
lean_dec_ref(v___y_3059_);
return v___x_3066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___boxed(lean_object* v_altLiveVars_3134_, lean_object* v_k_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_altLiveVars_3134_, v_k_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
lean_dec(v_a_3139_);
lean_dec_ref(v_a_3138_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec_ref(v_altLiveVars_3134_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(lean_object* v_altLiveVars_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v___x_3154_; 
v___x_3154_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_3144_, v_a_3145_, v_a_3146_, v___y_3147_, v___y_3148_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___boxed(lean_object* v_altLiveVars_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(v_altLiveVars_3155_, v_a_3156_, v_a_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v_a_3156_);
lean_dec_ref(v_altLiveVars_3155_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(lean_object* v_as_3166_, size_t v_i_3167_, size_t v_stop_3168_, lean_object* v_b_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v_as_3166_, v_i_3167_, v_stop_3168_, v_b_3169_, v___y_3170_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___boxed(lean_object* v_as_3178_, lean_object* v_i_3179_, lean_object* v_stop_3180_, lean_object* v_b_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
size_t v_i_boxed_3189_; size_t v_stop_boxed_3190_; lean_object* v_res_3191_; 
v_i_boxed_3189_ = lean_unbox_usize(v_i_3179_);
lean_dec(v_i_3179_);
v_stop_boxed_3190_ = lean_unbox_usize(v_stop_3180_);
lean_dec(v_stop_3180_);
v_res_3191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(v_as_3178_, v_i_boxed_3189_, v_stop_boxed_3190_, v_b_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec_ref(v_as_3178_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3(lean_object* v_n_3192_, lean_object* v_as_3193_, lean_object* v_lo_3194_, lean_object* v_hi_3195_, lean_object* v_w_3196_, lean_object* v_hlo_3197_, lean_object* v_hhi_3198_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_n_3192_, v_as_3193_, v_lo_3194_, v_hi_3195_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___boxed(lean_object* v_n_3200_, lean_object* v_as_3201_, lean_object* v_lo_3202_, lean_object* v_hi_3203_, lean_object* v_w_3204_, lean_object* v_hlo_3205_, lean_object* v_hhi_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3(v_n_3200_, v_as_3201_, v_lo_3202_, v_hi_3203_, v_w_3204_, v_hlo_3205_, v_hhi_3206_);
lean_dec(v_hi_3203_);
lean_dec(v_n_3200_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(lean_object* v_as_3208_, size_t v_i_3209_, size_t v_stop_3210_, lean_object* v_b_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_as_3208_, v_i_3209_, v_stop_3210_, v_b_3211_, v___y_3212_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___boxed(lean_object* v_as_3220_, lean_object* v_i_3221_, lean_object* v_stop_3222_, lean_object* v_b_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
size_t v_i_boxed_3231_; size_t v_stop_boxed_3232_; lean_object* v_res_3233_; 
v_i_boxed_3231_ = lean_unbox_usize(v_i_3221_);
lean_dec(v_i_3221_);
v_stop_boxed_3232_ = lean_unbox_usize(v_stop_3222_);
lean_dec(v_stop_3222_);
v_res_3233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(v_as_3220_, v_i_boxed_3231_, v_stop_boxed_3232_, v_b_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec_ref(v_as_3220_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3(lean_object* v_n_3234_, lean_object* v_lo_3235_, lean_object* v_hi_3236_, lean_object* v_hhi_3237_, lean_object* v_pivot_3238_, lean_object* v_as_3239_, lean_object* v_i_3240_, lean_object* v_k_3241_, lean_object* v_ilo_3242_, lean_object* v_ik_3243_, lean_object* v_w_3244_){
_start:
{
lean_object* v___x_3245_; 
v___x_3245_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(v_hi_3236_, v_pivot_3238_, v_as_3239_, v_i_3240_, v_k_3241_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___boxed(lean_object* v_n_3246_, lean_object* v_lo_3247_, lean_object* v_hi_3248_, lean_object* v_hhi_3249_, lean_object* v_pivot_3250_, lean_object* v_as_3251_, lean_object* v_i_3252_, lean_object* v_k_3253_, lean_object* v_ilo_3254_, lean_object* v_ik_3255_, lean_object* v_w_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3(v_n_3246_, v_lo_3247_, v_hi_3248_, v_hhi_3249_, v_pivot_3250_, v_as_3251_, v_i_3252_, v_k_3253_, v_ilo_3254_, v_ik_3255_, v_w_3256_);
lean_dec_ref(v_pivot_3250_);
lean_dec(v_hi_3248_);
lean_dec(v_lo_3247_);
lean_dec(v_n_3246_);
return v_res_3257_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(lean_object* v_args_3258_, lean_object* v_x_3259_, lean_object* v_n_3260_, lean_object* v_i_3261_){
_start:
{
lean_object* v_zero_3262_; uint8_t v_isZero_3263_; 
v_zero_3262_ = lean_unsigned_to_nat(0u);
v_isZero_3263_ = lean_nat_dec_eq(v_i_3261_, v_zero_3262_);
if (v_isZero_3263_ == 1)
{
lean_dec(v_i_3261_);
return v_isZero_3263_;
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3264_ = lean_box(0);
v___x_3265_ = lean_nat_sub(v_n_3260_, v_i_3261_);
v___x_3266_ = lean_array_get_borrowed(v___x_3264_, v_args_3258_, v___x_3265_);
lean_dec(v___x_3265_);
v___x_3267_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_3266_, v_x_3259_);
if (v___x_3267_ == 0)
{
lean_object* v_one_3268_; lean_object* v_n_3269_; 
v_one_3268_ = lean_unsigned_to_nat(1u);
v_n_3269_ = lean_nat_sub(v_i_3261_, v_one_3268_);
lean_dec(v_i_3261_);
v_i_3261_ = v_n_3269_;
goto _start;
}
else
{
lean_dec(v_i_3261_);
return v_isZero_3263_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg___boxed(lean_object* v_args_3271_, lean_object* v_x_3272_, lean_object* v_n_3273_, lean_object* v_i_3274_){
_start:
{
uint8_t v_res_3275_; lean_object* v_r_3276_; 
v_res_3275_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3271_, v_x_3272_, v_n_3273_, v_i_3274_);
lean_dec(v_n_3273_);
lean_dec(v_x_3272_);
lean_dec_ref(v_args_3271_);
v_r_3276_ = lean_box(v_res_3275_);
return v_r_3276_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(lean_object* v_args_3277_, lean_object* v_i_3278_){
_start:
{
lean_object* v___x_3279_; lean_object* v_x_3280_; uint8_t v___x_3281_; 
v___x_3279_ = lean_box(0);
v_x_3280_ = lean_array_get_borrowed(v___x_3279_, v_args_3277_, v_i_3278_);
lean_inc(v_i_3278_);
v___x_3281_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3277_, v_x_3280_, v_i_3278_, v_i_3278_);
lean_dec(v_i_3278_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc___boxed(lean_object* v_args_3282_, lean_object* v_i_3283_){
_start:
{
uint8_t v_res_3284_; lean_object* v_r_3285_; 
v_res_3284_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3282_, v_i_3283_);
lean_dec_ref(v_args_3282_);
v_r_3285_ = lean_box(v_res_3284_);
return v_r_3285_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(lean_object* v_args_3286_, lean_object* v_x_3287_, lean_object* v_n_3288_, lean_object* v_i_3289_, lean_object* v_a_3290_){
_start:
{
uint8_t v___x_3291_; 
v___x_3291_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3286_, v_x_3287_, v_n_3288_, v_i_3289_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___boxed(lean_object* v_args_3292_, lean_object* v_x_3293_, lean_object* v_n_3294_, lean_object* v_i_3295_, lean_object* v_a_3296_){
_start:
{
uint8_t v_res_3297_; lean_object* v_r_3298_; 
v_res_3297_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(v_args_3292_, v_x_3293_, v_n_3294_, v_i_3295_, v_a_3296_);
lean_dec(v_n_3294_);
lean_dec(v_x_3293_);
lean_dec_ref(v_args_3292_);
v_r_3298_ = lean_box(v_res_3297_);
return v_r_3298_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(lean_object* v_args_3299_, lean_object* v_arg_3300_, lean_object* v_consumeParamPred_3301_, lean_object* v_n_3302_, lean_object* v_i_3303_){
_start:
{
lean_object* v_zero_3304_; uint8_t v_isZero_3305_; 
v_zero_3304_ = lean_unsigned_to_nat(0u);
v_isZero_3305_ = lean_nat_dec_eq(v_i_3303_, v_zero_3304_);
if (v_isZero_3305_ == 1)
{
uint8_t v___x_3306_; 
lean_dec(v_i_3303_);
lean_dec_ref(v_consumeParamPred_3301_);
v___x_3306_ = 0;
return v___x_3306_;
}
else
{
lean_object* v_one_3307_; lean_object* v_n_3308_; uint8_t v___y_3310_; lean_object* v___x_3312_; lean_object* v_arg_x27_3313_; 
v_one_3307_ = lean_unsigned_to_nat(1u);
v_n_3308_ = lean_nat_sub(v_i_3303_, v_one_3307_);
v___x_3312_ = lean_nat_sub(v_n_3302_, v_i_3303_);
lean_dec(v_i_3303_);
v_arg_x27_3313_ = lean_array_fget_borrowed(v_args_3299_, v___x_3312_);
if (lean_obj_tag(v_arg_x27_3313_) == 0)
{
lean_dec(v___x_3312_);
v_i_3303_ = v_n_3308_;
goto _start;
}
else
{
lean_object* v_fvarId_3315_; uint8_t v___x_3316_; 
v_fvarId_3315_ = lean_ctor_get(v_arg_x27_3313_, 0);
v___x_3316_ = l_Lean_instBEqFVarId_beq(v_arg_3300_, v_fvarId_3315_);
if (v___x_3316_ == 0)
{
lean_dec(v___x_3312_);
v___y_3310_ = v___x_3316_;
goto v___jp_3309_;
}
else
{
lean_object* v___x_3317_; uint8_t v___x_3318_; 
lean_inc_ref(v_consumeParamPred_3301_);
v___x_3317_ = lean_apply_1(v_consumeParamPred_3301_, v___x_3312_);
v___x_3318_ = lean_unbox(v___x_3317_);
if (v___x_3318_ == 0)
{
v___y_3310_ = v___x_3316_;
goto v___jp_3309_;
}
else
{
v_i_3303_ = v_n_3308_;
goto _start;
}
}
}
v___jp_3309_:
{
if (v___y_3310_ == 0)
{
v_i_3303_ = v_n_3308_;
goto _start;
}
else
{
lean_dec(v_n_3308_);
lean_dec_ref(v_consumeParamPred_3301_);
return v___y_3310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg___boxed(lean_object* v_args_3320_, lean_object* v_arg_3321_, lean_object* v_consumeParamPred_3322_, lean_object* v_n_3323_, lean_object* v_i_3324_){
_start:
{
uint8_t v_res_3325_; lean_object* v_r_3326_; 
v_res_3325_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3320_, v_arg_3321_, v_consumeParamPred_3322_, v_n_3323_, v_i_3324_);
lean_dec(v_n_3323_);
lean_dec(v_arg_3321_);
lean_dec_ref(v_args_3320_);
v_r_3326_ = lean_box(v_res_3325_);
return v_r_3326_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(lean_object* v_arg_3327_, lean_object* v_args_3328_, lean_object* v_consumeParamPred_3329_){
_start:
{
lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3330_ = lean_array_get_size(v_args_3328_);
v___x_3331_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3328_, v_arg_3327_, v_consumeParamPred_3329_, v___x_3330_, v___x_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux___boxed(lean_object* v_arg_3332_, lean_object* v_args_3333_, lean_object* v_consumeParamPred_3334_){
_start:
{
uint8_t v_res_3335_; lean_object* v_r_3336_; 
v_res_3335_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_arg_3332_, v_args_3333_, v_consumeParamPred_3334_);
lean_dec_ref(v_args_3333_);
lean_dec(v_arg_3332_);
v_r_3336_ = lean_box(v_res_3335_);
return v_r_3336_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(lean_object* v_args_3337_, lean_object* v_arg_3338_, lean_object* v_consumeParamPred_3339_, lean_object* v_n_3340_, lean_object* v_i_3341_, lean_object* v_a_3342_){
_start:
{
uint8_t v___x_3343_; 
v___x_3343_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3337_, v_arg_3338_, v_consumeParamPred_3339_, v_n_3340_, v_i_3341_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___boxed(lean_object* v_args_3344_, lean_object* v_arg_3345_, lean_object* v_consumeParamPred_3346_, lean_object* v_n_3347_, lean_object* v_i_3348_, lean_object* v_a_3349_){
_start:
{
uint8_t v_res_3350_; lean_object* v_r_3351_; 
v_res_3350_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(v_args_3344_, v_arg_3345_, v_consumeParamPred_3346_, v_n_3347_, v_i_3348_, v_a_3349_);
lean_dec(v_n_3347_);
lean_dec(v_arg_3345_);
lean_dec_ref(v_args_3344_);
v_r_3351_ = lean_box(v_res_3350_);
return v_r_3351_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3352_; 
v___x_3352_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_3352_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(lean_object* v_ps_3353_, lean_object* v_i_3354_){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; uint8_t v_borrow_3357_; 
v___x_3355_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0);
v___x_3356_ = lean_array_get_borrowed(v___x_3355_, v_ps_3353_, v_i_3354_);
v_borrow_3357_ = lean_ctor_get_uint8(v___x_3356_, sizeof(void*)*3);
if (v_borrow_3357_ == 0)
{
uint8_t v___x_3358_; 
v___x_3358_ = 1;
return v___x_3358_;
}
else
{
uint8_t v___x_3359_; 
v___x_3359_ = 0;
return v___x_3359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed(lean_object* v_ps_3360_, lean_object* v_i_3361_){
_start:
{
uint8_t v_res_3362_; lean_object* v_r_3363_; 
v_res_3362_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(v_ps_3360_, v_i_3361_);
lean_dec(v_i_3361_);
lean_dec_ref(v_ps_3360_);
v_r_3363_ = lean_box(v_res_3362_);
return v_r_3363_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(lean_object* v_arg_3364_, lean_object* v_args_3365_, lean_object* v_ps_3366_){
_start:
{
lean_object* v___f_3367_; uint8_t v___x_3368_; 
v___f_3367_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3367_, 0, v_ps_3366_);
v___x_3368_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_arg_3364_, v_args_3365_, v___f_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___boxed(lean_object* v_arg_3369_, lean_object* v_args_3370_, lean_object* v_ps_3371_){
_start:
{
uint8_t v_res_3372_; lean_object* v_r_3373_; 
v_res_3372_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(v_arg_3369_, v_args_3370_, v_ps_3371_);
lean_dec_ref(v_args_3370_);
lean_dec(v_arg_3369_);
v_r_3373_ = lean_box(v_res_3372_);
return v_r_3373_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(lean_object* v_upperBound_3374_, lean_object* v_args_3375_, lean_object* v_arg_3376_, lean_object* v_consumeParamPred_3377_, lean_object* v_a_3378_, lean_object* v_b_3379_){
_start:
{
lean_object* v_a_3381_; uint8_t v___y_3386_; uint8_t v___x_3389_; 
v___x_3389_ = lean_nat_dec_lt(v_a_3378_, v_upperBound_3374_);
if (v___x_3389_ == 0)
{
lean_dec(v_a_3378_);
lean_dec_ref(v_consumeParamPred_3377_);
return v_b_3379_;
}
else
{
lean_object* v___x_3390_; 
v___x_3390_ = lean_array_fget_borrowed(v_args_3375_, v_a_3378_);
if (lean_obj_tag(v___x_3390_) == 1)
{
lean_object* v_fvarId_3391_; uint8_t v___x_3392_; 
v_fvarId_3391_ = lean_ctor_get(v___x_3390_, 0);
v___x_3392_ = l_Lean_instBEqFVarId_beq(v_arg_3376_, v_fvarId_3391_);
if (v___x_3392_ == 0)
{
v___y_3386_ = v___x_3392_;
goto v___jp_3385_;
}
else
{
lean_object* v___x_3393_; uint8_t v___x_3394_; 
lean_inc_ref(v_consumeParamPred_3377_);
lean_inc(v_a_3378_);
v___x_3393_ = lean_apply_1(v_consumeParamPred_3377_, v_a_3378_);
v___x_3394_ = lean_unbox(v___x_3393_);
v___y_3386_ = v___x_3394_;
goto v___jp_3385_;
}
}
else
{
v_a_3381_ = v_b_3379_;
goto v___jp_3380_;
}
}
v___jp_3380_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = lean_unsigned_to_nat(1u);
v___x_3383_ = lean_nat_add(v_a_3378_, v___x_3382_);
lean_dec(v_a_3378_);
v_a_3378_ = v___x_3383_;
v_b_3379_ = v_a_3381_;
goto _start;
}
v___jp_3385_:
{
if (v___y_3386_ == 0)
{
v_a_3381_ = v_b_3379_;
goto v___jp_3380_;
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = lean_unsigned_to_nat(1u);
v___x_3388_ = lean_nat_add(v_b_3379_, v___x_3387_);
lean_dec(v_b_3379_);
v_a_3381_ = v___x_3388_;
goto v___jp_3380_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg___boxed(lean_object* v_upperBound_3395_, lean_object* v_args_3396_, lean_object* v_arg_3397_, lean_object* v_consumeParamPred_3398_, lean_object* v_a_3399_, lean_object* v_b_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v_upperBound_3395_, v_args_3396_, v_arg_3397_, v_consumeParamPred_3398_, v_a_3399_, v_b_3400_);
lean_dec(v_arg_3397_);
lean_dec_ref(v_args_3396_);
lean_dec(v_upperBound_3395_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(lean_object* v_arg_3402_, lean_object* v_args_3403_, lean_object* v_consumeParamPred_3404_){
_start:
{
lean_object* v_num_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v_num_3405_ = lean_unsigned_to_nat(0u);
v___x_3406_ = lean_array_get_size(v_args_3403_);
v___x_3407_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v___x_3406_, v_args_3403_, v_arg_3402_, v_consumeParamPred_3404_, v_num_3405_, v_num_3405_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions___boxed(lean_object* v_arg_3408_, lean_object* v_args_3409_, lean_object* v_consumeParamPred_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(v_arg_3408_, v_args_3409_, v_consumeParamPred_3410_);
lean_dec_ref(v_args_3409_);
lean_dec(v_arg_3408_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0(lean_object* v_upperBound_3412_, lean_object* v_args_3413_, lean_object* v_arg_3414_, lean_object* v_consumeParamPred_3415_, lean_object* v_inst_3416_, lean_object* v_R_3417_, lean_object* v_a_3418_, lean_object* v_b_3419_, lean_object* v_c_3420_){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v_upperBound_3412_, v_args_3413_, v_arg_3414_, v_consumeParamPred_3415_, v_a_3418_, v_b_3419_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___boxed(lean_object* v_upperBound_3422_, lean_object* v_args_3423_, lean_object* v_arg_3424_, lean_object* v_consumeParamPred_3425_, lean_object* v_inst_3426_, lean_object* v_R_3427_, lean_object* v_a_3428_, lean_object* v_b_3429_, lean_object* v_c_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0(v_upperBound_3422_, v_args_3423_, v_arg_3424_, v_consumeParamPred_3425_, v_inst_3426_, v_R_3427_, v_a_3428_, v_b_3429_, v_c_3430_);
lean_dec(v_arg_3424_);
lean_dec_ref(v_args_3423_);
lean_dec(v_upperBound_3422_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(lean_object* v_fvarId_3432_, lean_object* v_b_3433_, uint8_t v___x_3434_, lean_object* v_numIncs_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_a_3444_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
v___x_3447_ = lean_unsigned_to_nat(0u);
v___x_3448_ = lean_nat_dec_eq(v_numIncs_3435_, v___x_3447_);
if (v___x_3448_ == 0)
{
lean_object* v_varMap_3449_; lean_object* v___x_3450_; uint8_t v___y_3452_; uint8_t v_isDefiniteRef_3455_; 
v_varMap_3449_ = lean_ctor_get(v___y_3436_, 3);
v___x_3450_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3449_, v_fvarId_3432_);
v_isDefiniteRef_3455_ = lean_ctor_get_uint8(v___x_3450_, sizeof(void*)*2 + 1);
if (v_isDefiniteRef_3455_ == 0)
{
v___y_3452_ = v___x_3434_;
goto v___jp_3451_;
}
else
{
v___y_3452_ = v___x_3448_;
goto v___jp_3451_;
}
v___jp_3451_:
{
uint8_t v_persistent_3453_; lean_object* v___x_3454_; 
v_persistent_3453_ = lean_ctor_get_uint8(v___x_3450_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_3450_);
v___x_3454_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_3454_, 0, v_fvarId_3432_);
lean_ctor_set(v___x_3454_, 1, v_numIncs_3435_);
lean_ctor_set(v___x_3454_, 2, v_b_3433_);
lean_ctor_set_uint8(v___x_3454_, sizeof(void*)*3, v___y_3452_);
lean_ctor_set_uint8(v___x_3454_, sizeof(void*)*3 + 1, v_persistent_3453_);
v_a_3444_ = v___x_3454_;
goto v___jp_3443_;
}
}
else
{
lean_dec(v_numIncs_3435_);
lean_dec(v_fvarId_3432_);
v_a_3444_ = v_b_3433_;
goto v___jp_3443_;
}
v___jp_3443_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3445_, 0, v_a_3444_);
v___x_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
return v___x_3446_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_3456_, lean_object* v_b_3457_, lean_object* v___x_3458_, lean_object* v_numIncs_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
uint8_t v___x_7163__boxed_3467_; lean_object* v_res_3468_; 
v___x_7163__boxed_3467_ = lean_unbox(v___x_3458_);
v_res_3468_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3456_, v_b_3457_, v___x_7163__boxed_3467_, v_numIncs_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(lean_object* v_upperBound_3469_, lean_object* v_args_3470_, lean_object* v_consumeParamPred_3471_, lean_object* v_a_3472_, lean_object* v_b_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v_a_3482_; lean_object* v___y_3487_; uint8_t v___x_3506_; 
v___x_3506_ = lean_nat_dec_lt(v_a_3472_, v_upperBound_3469_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; 
lean_dec(v_a_3472_);
lean_dec_ref(v_consumeParamPred_3471_);
v___x_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3507_, 0, v_b_3473_);
return v___x_3507_;
}
else
{
lean_object* v___x_3508_; 
v___x_3508_ = lean_array_fget_borrowed(v_args_3470_, v_a_3472_);
if (lean_obj_tag(v___x_3508_) == 1)
{
lean_object* v_fvarId_3509_; lean_object* v_varMap_3510_; lean_object* v___x_3511_; uint8_t v_isPossibleRef_3512_; 
v_fvarId_3509_ = lean_ctor_get(v___x_3508_, 0);
v_varMap_3510_ = lean_ctor_get(v___y_3474_, 3);
v___x_3511_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3510_, v_fvarId_3509_);
v_isPossibleRef_3512_ = lean_ctor_get_uint8(v___x_3511_, sizeof(void*)*2);
lean_dec_ref(v___x_3511_);
if (v_isPossibleRef_3512_ == 0)
{
v_a_3482_ = v_b_3473_;
goto v___jp_3481_;
}
else
{
uint8_t v___x_3513_; 
lean_inc(v_a_3472_);
v___x_3513_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3470_, v_a_3472_);
if (v___x_3513_ == 0)
{
v_a_3482_ = v_b_3473_;
goto v___jp_3481_;
}
else
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v_vars_3516_; uint8_t v___x_3517_; lean_object* v___x_3518_; uint8_t v___y_3522_; 
lean_inc_ref(v_consumeParamPred_3471_);
v___x_3514_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(v_fvarId_3509_, v_args_3470_, v_consumeParamPred_3471_);
v___x_3515_ = lean_st_ref_get(v___y_3475_);
v_vars_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc_ref(v_vars_3516_);
lean_dec(v___x_3515_);
v___x_3517_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_3516_, v_fvarId_3509_);
lean_dec_ref(v_vars_3516_);
v___x_3518_ = lean_st_ref_get(v___y_3475_);
if (v___x_3517_ == 0)
{
lean_object* v_borrows_3527_; uint8_t v___x_3528_; 
v_borrows_3527_ = lean_ctor_get(v___x_3518_, 1);
lean_inc_ref(v_borrows_3527_);
lean_dec(v___x_3518_);
v___x_3528_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_3527_, v_fvarId_3509_);
lean_dec_ref(v_borrows_3527_);
v___y_3522_ = v___x_3528_;
goto v___jp_3521_;
}
else
{
lean_dec(v___x_3518_);
v___y_3522_ = v___x_3517_;
goto v___jp_3521_;
}
v___jp_3519_:
{
lean_object* v___x_3520_; 
lean_inc(v_fvarId_3509_);
v___x_3520_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3509_, v_b_3473_, v___x_3506_, v___x_3514_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v___y_3487_ = v___x_3520_;
goto v___jp_3486_;
}
v___jp_3521_:
{
if (v___y_3522_ == 0)
{
uint8_t v___x_3523_; 
lean_inc_ref(v_consumeParamPred_3471_);
v___x_3523_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_fvarId_3509_, v_args_3470_, v_consumeParamPred_3471_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = lean_unsigned_to_nat(1u);
v___x_3525_ = lean_nat_sub(v___x_3514_, v___x_3524_);
lean_dec(v___x_3514_);
lean_inc(v_fvarId_3509_);
v___x_3526_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3509_, v_b_3473_, v___x_3506_, v___x_3525_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
v___y_3487_ = v___x_3526_;
goto v___jp_3486_;
}
else
{
goto v___jp_3519_;
}
}
else
{
goto v___jp_3519_;
}
}
}
}
}
else
{
v_a_3482_ = v_b_3473_;
goto v___jp_3481_;
}
}
v___jp_3481_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = lean_unsigned_to_nat(1u);
v___x_3484_ = lean_nat_add(v_a_3472_, v___x_3483_);
lean_dec(v_a_3472_);
v_a_3472_ = v___x_3484_;
v_b_3473_ = v_a_3482_;
goto _start;
}
v___jp_3486_:
{
if (lean_obj_tag(v___y_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3497_; 
v_a_3488_ = lean_ctor_get(v___y_3487_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___y_3487_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3490_ = v___y_3487_;
v_isShared_3491_ = v_isSharedCheck_3497_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___y_3487_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3497_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
if (lean_obj_tag(v_a_3488_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3494_; 
lean_dec(v_a_3472_);
lean_dec_ref(v_consumeParamPred_3471_);
v_a_3492_ = lean_ctor_get(v_a_3488_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v_a_3488_, 1);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v_a_3492_);
v___x_3494_ = v___x_3490_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
else
{
lean_object* v_a_3496_; 
lean_del_object(v___x_3490_);
v_a_3496_ = lean_ctor_get(v_a_3488_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v_a_3488_, 1);
v_a_3482_ = v_a_3496_;
goto v___jp_3481_;
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec(v_a_3472_);
lean_dec_ref(v_consumeParamPred_3471_);
v_a_3498_ = lean_ctor_get(v___y_3487_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___y_3487_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___y_3487_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___y_3487_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___boxed(lean_object* v_upperBound_3529_, lean_object* v_args_3530_, lean_object* v_consumeParamPred_3531_, lean_object* v_a_3532_, lean_object* v_b_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v_upperBound_3529_, v_args_3530_, v_consumeParamPred_3531_, v_a_3532_, v_b_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v_args_3530_);
lean_dec(v_upperBound_3529_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(lean_object* v_args_3542_, lean_object* v_consumeParamPred_3543_, lean_object* v_k_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_unsigned_to_nat(0u);
v___x_3553_ = lean_array_get_size(v_args_3542_);
v___x_3554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v___x_3553_, v_args_3542_, v_consumeParamPred_3543_, v___x_3552_, v_k_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux___boxed(lean_object* v_args_3555_, lean_object* v_consumeParamPred_3556_, lean_object* v_k_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3555_, v_consumeParamPred_3556_, v_k_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec_ref(v_args_3555_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(lean_object* v_upperBound_3566_, lean_object* v_args_3567_, lean_object* v_consumeParamPred_3568_, lean_object* v_inst_3569_, lean_object* v_R_3570_, lean_object* v_a_3571_, lean_object* v_b_3572_, lean_object* v_c_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v_upperBound_3566_, v_args_3567_, v_consumeParamPred_3568_, v_a_3571_, v_b_3572_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___boxed(lean_object* v_upperBound_3582_, lean_object* v_args_3583_, lean_object* v_consumeParamPred_3584_, lean_object* v_inst_3585_, lean_object* v_R_3586_, lean_object* v_a_3587_, lean_object* v_b_3588_, lean_object* v_c_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(v_upperBound_3582_, v_args_3583_, v_consumeParamPred_3584_, v_inst_3585_, v_R_3586_, v_a_3587_, v_b_3588_, v_c_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v_args_3583_);
lean_dec(v_upperBound_3582_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(lean_object* v_args_3598_, lean_object* v_ps_3599_, lean_object* v_k_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_){
_start:
{
lean_object* v___f_3608_; lean_object* v___x_3609_; 
v___f_3608_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3608_, 0, v_ps_3599_);
v___x_3609_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3598_, v___f_3608_, v_k_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore___boxed(lean_object* v_args_3610_, lean_object* v_ps_3611_, lean_object* v_k_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_3610_, v_ps_3611_, v_k_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
lean_dec(v_a_3618_);
lean_dec_ref(v_a_3617_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec_ref(v_args_3610_);
return v_res_3620_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(lean_object* v_x_3621_){
_start:
{
uint8_t v___x_3622_; 
v___x_3622_ = 1;
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0___boxed(lean_object* v_x_3623_){
_start:
{
uint8_t v_res_3624_; lean_object* v_r_3625_; 
v_res_3624_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(v_x_3623_);
lean_dec(v_x_3623_);
v_r_3625_ = lean_box(v_res_3624_);
return v_r_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(lean_object* v_args_3627_, lean_object* v_k_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v___f_3636_; lean_object* v___x_3637_; 
v___f_3636_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___closed__0));
v___x_3637_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3627_, v___f_3636_, v_k_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___boxed(lean_object* v_args_3638_, lean_object* v_k_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_3638_, v_k_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
lean_dec(v_a_3645_);
lean_dec_ref(v_a_3644_);
lean_dec(v_a_3643_);
lean_dec_ref(v_a_3642_);
lean_dec(v_a_3641_);
lean_dec_ref(v_a_3640_);
lean_dec_ref(v_args_3638_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(lean_object* v_upperBound_3648_, lean_object* v_args_3649_, lean_object* v_ps_3650_, lean_object* v_a_3651_, lean_object* v_b_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v_a_3657_; uint8_t v___x_3661_; 
v___x_3661_ = lean_nat_dec_lt(v_a_3651_, v_upperBound_3648_);
if (v___x_3661_ == 0)
{
lean_object* v___x_3662_; 
lean_dec(v_a_3651_);
lean_dec_ref(v_ps_3650_);
v___x_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3662_, 0, v_b_3652_);
return v___x_3662_;
}
else
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_array_fget_borrowed(v_args_3649_, v_a_3651_);
if (lean_obj_tag(v___x_3663_) == 0)
{
v_a_3657_ = v_b_3652_;
goto v___jp_3656_;
}
else
{
lean_object* v_fvarId_3664_; lean_object* v_varMap_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v_vars_3668_; uint8_t v___x_3669_; lean_object* v___x_3670_; uint8_t v_isPossibleRef_3671_; 
v_fvarId_3664_ = lean_ctor_get(v___x_3663_, 0);
v_varMap_3665_ = lean_ctor_get(v___y_3653_, 3);
v___x_3666_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3665_, v_fvarId_3664_);
v___x_3667_ = lean_st_ref_get(v___y_3654_);
v_vars_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc_ref(v_vars_3668_);
lean_dec(v___x_3667_);
v___x_3669_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_3668_, v_fvarId_3664_);
lean_dec_ref(v_vars_3668_);
v___x_3670_ = lean_st_ref_get(v___y_3654_);
v_isPossibleRef_3671_ = lean_ctor_get_uint8(v___x_3666_, sizeof(void*)*2);
lean_dec_ref(v___x_3666_);
if (v_isPossibleRef_3671_ == 0)
{
lean_dec(v___x_3670_);
v_a_3657_ = v_b_3652_;
goto v___jp_3656_;
}
else
{
uint8_t v___x_3672_; 
lean_inc(v_a_3651_);
v___x_3672_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3649_, v_a_3651_);
if (v___x_3672_ == 0)
{
lean_dec(v___x_3670_);
v_a_3657_ = v_b_3652_;
goto v___jp_3656_;
}
else
{
uint8_t v___x_3673_; 
lean_inc_ref(v_ps_3650_);
v___x_3673_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(v_fvarId_3664_, v_args_3649_, v_ps_3650_);
if (v___x_3673_ == 0)
{
lean_dec(v___x_3670_);
v_a_3657_ = v_b_3652_;
goto v___jp_3656_;
}
else
{
if (v___x_3669_ == 0)
{
lean_object* v_borrows_3674_; uint8_t v___x_3675_; 
v_borrows_3674_ = lean_ctor_get(v___x_3670_, 1);
lean_inc_ref(v_borrows_3674_);
lean_dec(v___x_3670_);
v___x_3675_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_3674_, v_fvarId_3664_);
lean_dec_ref(v_borrows_3674_);
if (v___x_3675_ == 0)
{
lean_object* v___x_3676_; 
lean_inc(v_fvarId_3664_);
v___x_3676_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_3664_, v_b_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref_known(v___x_3676_, 1);
v_a_3657_ = v_a_3677_;
goto v___jp_3656_;
}
else
{
lean_dec(v_a_3651_);
lean_dec_ref(v_ps_3650_);
return v___x_3676_;
}
}
else
{
v_a_3657_ = v_b_3652_;
goto v___jp_3656_;
}
}
else
{
lean_dec(v___x_3670_);
v_a_3657_ = v_b_3652_;
goto v___jp_3656_;
}
}
}
}
}
}
v___jp_3656_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = lean_unsigned_to_nat(1u);
v___x_3659_ = lean_nat_add(v_a_3651_, v___x_3658_);
lean_dec(v_a_3651_);
v_a_3651_ = v___x_3659_;
v_b_3652_ = v_a_3657_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg___boxed(lean_object* v_upperBound_3678_, lean_object* v_args_3679_, lean_object* v_ps_3680_, lean_object* v_a_3681_, lean_object* v_b_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v_upperBound_3678_, v_args_3679_, v_ps_3680_, v_a_3681_, v_b_3682_, v___y_3683_, v___y_3684_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v_args_3679_);
lean_dec(v_upperBound_3678_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(lean_object* v_args_3687_, lean_object* v_ps_3688_, lean_object* v_k_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3697_ = lean_unsigned_to_nat(0u);
v___x_3698_ = lean_array_get_size(v_args_3687_);
v___x_3699_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v___x_3698_, v_args_3687_, v_ps_3688_, v___x_3697_, v_k_3689_, v_a_3690_, v_a_3691_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp___boxed(lean_object* v_args_3700_, lean_object* v_ps_3701_, lean_object* v_k_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(v_args_3700_, v_ps_3701_, v_k_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_a_3705_);
lean_dec(v_a_3704_);
lean_dec_ref(v_a_3703_);
lean_dec_ref(v_args_3700_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(lean_object* v_upperBound_3711_, lean_object* v_args_3712_, lean_object* v_ps_3713_, lean_object* v_inst_3714_, lean_object* v_R_3715_, lean_object* v_a_3716_, lean_object* v_b_3717_, lean_object* v_c_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v_upperBound_3711_, v_args_3712_, v_ps_3713_, v_a_3716_, v_b_3717_, v___y_3719_, v___y_3720_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___boxed(lean_object* v_upperBound_3727_, lean_object* v_args_3728_, lean_object* v_ps_3729_, lean_object* v_inst_3730_, lean_object* v_R_3731_, lean_object* v_a_3732_, lean_object* v_b_3733_, lean_object* v_c_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(v_upperBound_3727_, v_args_3728_, v_ps_3729_, v_inst_3730_, v_R_3731_, v_a_3732_, v_b_3733_, v_c_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec_ref(v_args_3728_);
lean_dec(v_upperBound_3727_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(lean_object* v_fvarId_3743_, lean_object* v_k_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v_varMap_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v_borrows_3751_; uint8_t v___x_3752_; lean_object* v___x_3753_; uint8_t v_isPossibleRef_3754_; 
v_varMap_3748_ = lean_ctor_get(v_a_3745_, 3);
v___x_3749_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3748_, v_fvarId_3743_);
v___x_3750_ = lean_st_ref_get(v_a_3746_);
v_borrows_3751_ = lean_ctor_get(v___x_3750_, 1);
lean_inc_ref(v_borrows_3751_);
lean_dec(v___x_3750_);
v___x_3752_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_3751_, v_fvarId_3743_);
lean_dec_ref(v_borrows_3751_);
v___x_3753_ = lean_st_ref_get(v_a_3746_);
v_isPossibleRef_3754_ = lean_ctor_get_uint8(v___x_3749_, sizeof(void*)*2);
lean_dec_ref(v___x_3749_);
if (v_isPossibleRef_3754_ == 0)
{
lean_object* v___x_3755_; 
lean_dec(v___x_3753_);
lean_dec(v_fvarId_3743_);
v___x_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3755_, 0, v_k_3744_);
return v___x_3755_;
}
else
{
if (v___x_3752_ == 0)
{
lean_object* v_vars_3756_; uint8_t v___x_3757_; 
v_vars_3756_ = lean_ctor_get(v___x_3753_, 0);
lean_inc_ref(v_vars_3756_);
lean_dec(v___x_3753_);
v___x_3757_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_3756_, v_fvarId_3743_);
lean_dec_ref(v_vars_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; 
v___x_3758_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_3743_, v_k_3744_, v_a_3745_);
return v___x_3758_;
}
else
{
lean_object* v___x_3759_; 
lean_dec(v_fvarId_3743_);
v___x_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3759_, 0, v_k_3744_);
return v___x_3759_;
}
}
else
{
lean_object* v___x_3760_; 
lean_dec(v___x_3753_);
lean_dec(v_fvarId_3743_);
v___x_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3760_, 0, v_k_3744_);
return v___x_3760_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg___boxed(lean_object* v_fvarId_3761_, lean_object* v_k_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3761_, v_k_3762_, v_a_3763_, v_a_3764_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(lean_object* v_fvarId_3767_, lean_object* v_k_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3767_, v_k_3768_, v_a_3769_, v_a_3770_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___boxed(lean_object* v_fvarId_3777_, lean_object* v_k_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(v_fvarId_3777_, v_k_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
lean_dec(v_a_3784_);
lean_dec_ref(v_a_3783_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(lean_object* v_a_3787_, lean_object* v_x_3788_){
_start:
{
if (lean_obj_tag(v_x_3788_) == 0)
{
return v_x_3788_;
}
else
{
lean_object* v_key_3789_; lean_object* v_value_3790_; lean_object* v_tail_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3800_; 
v_key_3789_ = lean_ctor_get(v_x_3788_, 0);
v_value_3790_ = lean_ctor_get(v_x_3788_, 1);
v_tail_3791_ = lean_ctor_get(v_x_3788_, 2);
v_isSharedCheck_3800_ = !lean_is_exclusive(v_x_3788_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3793_ = v_x_3788_;
v_isShared_3794_ = v_isSharedCheck_3800_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_tail_3791_);
lean_inc(v_value_3790_);
lean_inc(v_key_3789_);
lean_dec(v_x_3788_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3800_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
uint8_t v___x_3795_; 
v___x_3795_ = l_Lean_instBEqFVarId_beq(v_key_3789_, v_a_3787_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3796_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3787_, v_tail_3791_);
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 2, v___x_3796_);
v___x_3798_ = v___x_3793_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_key_3789_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_value_3790_);
lean_ctor_set(v_reuseFailAlloc_3799_, 2, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
else
{
lean_del_object(v___x_3793_);
lean_dec(v_value_3790_);
lean_dec(v_key_3789_);
return v_tail_3791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg___boxed(lean_object* v_a_3801_, lean_object* v_x_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3801_, v_x_3802_);
lean_dec(v_a_3801_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(lean_object* v_m_3804_, lean_object* v_a_3805_){
_start:
{
lean_object* v_size_3806_; lean_object* v_buckets_3807_; lean_object* v___x_3808_; uint64_t v___x_3809_; uint64_t v___x_3810_; uint64_t v___x_3811_; uint64_t v_fold_3812_; uint64_t v___x_3813_; uint64_t v___x_3814_; uint64_t v___x_3815_; size_t v___x_3816_; size_t v___x_3817_; size_t v___x_3818_; size_t v___x_3819_; size_t v___x_3820_; lean_object* v_bkt_3821_; uint8_t v___x_3822_; 
v_size_3806_ = lean_ctor_get(v_m_3804_, 0);
v_buckets_3807_ = lean_ctor_get(v_m_3804_, 1);
v___x_3808_ = lean_array_get_size(v_buckets_3807_);
v___x_3809_ = l_Lean_instHashableFVarId_hash(v_a_3805_);
v___x_3810_ = 32ULL;
v___x_3811_ = lean_uint64_shift_right(v___x_3809_, v___x_3810_);
v_fold_3812_ = lean_uint64_xor(v___x_3809_, v___x_3811_);
v___x_3813_ = 16ULL;
v___x_3814_ = lean_uint64_shift_right(v_fold_3812_, v___x_3813_);
v___x_3815_ = lean_uint64_xor(v_fold_3812_, v___x_3814_);
v___x_3816_ = lean_uint64_to_usize(v___x_3815_);
v___x_3817_ = lean_usize_of_nat(v___x_3808_);
v___x_3818_ = ((size_t)1ULL);
v___x_3819_ = lean_usize_sub(v___x_3817_, v___x_3818_);
v___x_3820_ = lean_usize_land(v___x_3816_, v___x_3819_);
v_bkt_3821_ = lean_array_uget_borrowed(v_buckets_3807_, v___x_3820_);
v___x_3822_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_3805_, v_bkt_3821_);
if (v___x_3822_ == 0)
{
return v_m_3804_;
}
else
{
lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3835_; 
lean_inc(v_bkt_3821_);
lean_inc_ref(v_buckets_3807_);
lean_inc(v_size_3806_);
v_isSharedCheck_3835_ = !lean_is_exclusive(v_m_3804_);
if (v_isSharedCheck_3835_ == 0)
{
lean_object* v_unused_3836_; lean_object* v_unused_3837_; 
v_unused_3836_ = lean_ctor_get(v_m_3804_, 1);
lean_dec(v_unused_3836_);
v_unused_3837_ = lean_ctor_get(v_m_3804_, 0);
lean_dec(v_unused_3837_);
v___x_3824_ = v_m_3804_;
v_isShared_3825_ = v_isSharedCheck_3835_;
goto v_resetjp_3823_;
}
else
{
lean_dec(v_m_3804_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3835_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3826_; lean_object* v_buckets_x27_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3833_; 
v___x_3826_ = lean_box(0);
v_buckets_x27_3827_ = lean_array_uset(v_buckets_3807_, v___x_3820_, v___x_3826_);
v___x_3828_ = lean_unsigned_to_nat(1u);
v___x_3829_ = lean_nat_sub(v_size_3806_, v___x_3828_);
lean_dec(v_size_3806_);
v___x_3830_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3805_, v_bkt_3821_);
v___x_3831_ = lean_array_uset(v_buckets_x27_3827_, v___x_3820_, v___x_3830_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 1, v___x_3831_);
lean_ctor_set(v___x_3824_, 0, v___x_3829_);
v___x_3833_ = v___x_3824_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3829_);
lean_ctor_set(v_reuseFailAlloc_3834_, 1, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg___boxed(lean_object* v_m_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_m_3838_, v_a_3839_);
lean_dec(v_a_3839_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(lean_object* v_as_3841_, size_t v_i_3842_, size_t v_stop_3843_, lean_object* v_b_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v_a_3849_; uint8_t v___x_3853_; 
v___x_3853_ = lean_usize_dec_eq(v_i_3842_, v_stop_3843_);
if (v___x_3853_ == 0)
{
lean_object* v___x_3854_; lean_object* v_fvarId_3855_; lean_object* v___x_3856_; 
v___x_3854_ = lean_array_uget_borrowed(v_as_3841_, v_i_3842_);
v_fvarId_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_fvarId_3855_);
v___x_3856_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3855_, v_b_3844_, v___y_3845_, v___y_3846_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3858_; lean_object* v_vars_3859_; lean_object* v_borrows_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3870_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3856_, 1);
v___x_3858_ = lean_st_ref_take(v___y_3846_);
v_vars_3859_ = lean_ctor_get(v___x_3858_, 0);
v_borrows_3860_ = lean_ctor_get(v___x_3858_, 1);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3862_ = v___x_3858_;
v_isShared_3863_ = v_isSharedCheck_3870_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_borrows_3860_);
lean_inc(v_vars_3859_);
lean_dec(v___x_3858_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3870_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v_vars_3864_; lean_object* v_borrows_3865_; lean_object* v___x_3867_; 
v_vars_3864_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_vars_3859_, v_fvarId_3855_);
v_borrows_3865_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_borrows_3860_, v_fvarId_3855_);
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 1, v_borrows_3865_);
lean_ctor_set(v___x_3862_, 0, v_vars_3864_);
v___x_3867_ = v___x_3862_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_vars_3864_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_borrows_3865_);
v___x_3867_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_st_ref_put(v___y_3846_, v___x_3867_);
v_a_3849_ = v_a_3857_;
goto v___jp_3848_;
}
}
}
else
{
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3871_; 
v_a_3871_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3856_, 1);
v_a_3849_ = v_a_3871_;
goto v___jp_3848_;
}
else
{
return v___x_3856_;
}
}
}
else
{
lean_object* v___x_3872_; 
v___x_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3872_, 0, v_b_3844_);
return v___x_3872_;
}
v___jp_3848_:
{
size_t v___x_3850_; size_t v___x_3851_; 
v___x_3850_ = ((size_t)1ULL);
v___x_3851_ = lean_usize_add(v_i_3842_, v___x_3850_);
v_i_3842_ = v___x_3851_;
v_b_3844_ = v_a_3849_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg___boxed(lean_object* v_as_3873_, lean_object* v_i_3874_, lean_object* v_stop_3875_, lean_object* v_b_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
size_t v_i_boxed_3880_; size_t v_stop_boxed_3881_; lean_object* v_res_3882_; 
v_i_boxed_3880_ = lean_unbox_usize(v_i_3874_);
lean_dec(v_i_3874_);
v_stop_boxed_3881_ = lean_unbox_usize(v_stop_3875_);
lean_dec(v_stop_3875_);
v_res_3882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_as_3873_, v_i_boxed_3880_, v_stop_boxed_3881_, v_b_3876_, v___y_3877_, v___y_3878_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec_ref(v_as_3873_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(lean_object* v_ps_3883_, lean_object* v_k_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3892_ = lean_unsigned_to_nat(0u);
v___x_3893_ = lean_array_get_size(v_ps_3883_);
v___x_3894_ = lean_nat_dec_lt(v___x_3892_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; 
v___x_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3895_, 0, v_k_3884_);
return v___x_3895_;
}
else
{
uint8_t v___x_3896_; 
v___x_3896_ = lean_nat_dec_le(v___x_3893_, v___x_3893_);
if (v___x_3896_ == 0)
{
if (v___x_3894_ == 0)
{
lean_object* v___x_3897_; 
v___x_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3897_, 0, v_k_3884_);
return v___x_3897_;
}
else
{
size_t v___x_3898_; size_t v___x_3899_; lean_object* v___x_3900_; 
v___x_3898_ = ((size_t)0ULL);
v___x_3899_ = lean_usize_of_nat(v___x_3893_);
v___x_3900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_ps_3883_, v___x_3898_, v___x_3899_, v_k_3884_, v_a_3885_, v_a_3886_);
return v___x_3900_;
}
}
else
{
size_t v___x_3901_; size_t v___x_3902_; lean_object* v___x_3903_; 
v___x_3901_ = ((size_t)0ULL);
v___x_3902_ = lean_usize_of_nat(v___x_3893_);
v___x_3903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_ps_3883_, v___x_3901_, v___x_3902_, v_k_3884_, v_a_3885_, v_a_3886_);
return v___x_3903_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams___boxed(lean_object* v_ps_3904_, lean_object* v_k_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_ps_3904_, v_k_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
lean_dec_ref(v_a_3908_);
lean_dec(v_a_3907_);
lean_dec_ref(v_a_3906_);
lean_dec_ref(v_ps_3904_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(lean_object* v_00_u03b2_3914_, lean_object* v_m_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_m_3915_, v_a_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___boxed(lean_object* v_00_u03b2_3918_, lean_object* v_m_3919_, lean_object* v_a_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(v_00_u03b2_3918_, v_m_3919_, v_a_3920_);
lean_dec(v_a_3920_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1(lean_object* v_as_3922_, size_t v_i_3923_, size_t v_stop_3924_, lean_object* v_b_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_as_3922_, v_i_3923_, v_stop_3924_, v_b_3925_, v___y_3926_, v___y_3927_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___boxed(lean_object* v_as_3934_, lean_object* v_i_3935_, lean_object* v_stop_3936_, lean_object* v_b_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
size_t v_i_boxed_3945_; size_t v_stop_boxed_3946_; lean_object* v_res_3947_; 
v_i_boxed_3945_ = lean_unbox_usize(v_i_3935_);
lean_dec(v_i_3935_);
v_stop_boxed_3946_ = lean_unbox_usize(v_stop_3936_);
lean_dec(v_stop_3936_);
v_res_3947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1(v_as_3934_, v_i_boxed_3945_, v_stop_boxed_3946_, v_b_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec_ref(v_as_3934_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0(lean_object* v_00_u03b2_3948_, lean_object* v_a_3949_, lean_object* v_x_3950_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3949_, v_x_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3952_, lean_object* v_a_3953_, lean_object* v_x_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0(v_00_u03b2_3952_, v_a_3953_, v_x_3954_);
lean_dec(v_a_3953_);
return v_res_3955_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(lean_object* v_msg_3957_){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0);
v___x_3959_ = lean_panic_fn_borrowed(v___x_3958_, v_msg_3957_);
return v___x_3959_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3960_; 
v___x_3960_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default___redArg();
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1(lean_object* v_msg_3961_){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0);
v___x_3963_ = lean_panic_fn_borrowed(v___x_3962_, v_msg_3961_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(lean_object* v_msg_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v_toApplicative_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_4037_; 
v___x_3972_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0);
v___x_3973_ = l_StateRefT_x27_instMonad___redArg(v___x_3972_);
v_toApplicative_3974_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_4037_ == 0)
{
lean_object* v_unused_4038_; 
v_unused_4038_ = lean_ctor_get(v___x_3973_, 1);
lean_dec(v_unused_4038_);
v___x_3976_ = v___x_3973_;
v_isShared_3977_ = v_isSharedCheck_4037_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_toApplicative_3974_);
lean_dec(v___x_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_4037_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v_toFunctor_3978_; lean_object* v_toSeq_3979_; lean_object* v_toSeqLeft_3980_; lean_object* v_toSeqRight_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_4035_; 
v_toFunctor_3978_ = lean_ctor_get(v_toApplicative_3974_, 0);
v_toSeq_3979_ = lean_ctor_get(v_toApplicative_3974_, 2);
v_toSeqLeft_3980_ = lean_ctor_get(v_toApplicative_3974_, 3);
v_toSeqRight_3981_ = lean_ctor_get(v_toApplicative_3974_, 4);
v_isSharedCheck_4035_ = !lean_is_exclusive(v_toApplicative_3974_);
if (v_isSharedCheck_4035_ == 0)
{
lean_object* v_unused_4036_; 
v_unused_4036_ = lean_ctor_get(v_toApplicative_3974_, 1);
lean_dec(v_unused_4036_);
v___x_3983_ = v_toApplicative_3974_;
v_isShared_3984_ = v_isSharedCheck_4035_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_toSeqRight_3981_);
lean_inc(v_toSeqLeft_3980_);
lean_inc(v_toSeq_3979_);
lean_inc(v_toFunctor_3978_);
lean_dec(v_toApplicative_3974_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_4035_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___f_3985_; lean_object* v___f_3986_; lean_object* v___f_3987_; lean_object* v___f_3988_; lean_object* v___x_3989_; lean_object* v___f_3990_; lean_object* v___f_3991_; lean_object* v___f_3992_; lean_object* v___x_3994_; 
v___f_3985_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__1));
v___f_3986_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3978_);
v___f_3987_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3987_, 0, v_toFunctor_3978_);
v___f_3988_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3988_, 0, v_toFunctor_3978_);
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___f_3987_);
lean_ctor_set(v___x_3989_, 1, v___f_3988_);
v___f_3990_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3990_, 0, v_toSeqRight_3981_);
v___f_3991_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3991_, 0, v_toSeqLeft_3980_);
v___f_3992_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3992_, 0, v_toSeq_3979_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 4, v___f_3990_);
lean_ctor_set(v___x_3983_, 3, v___f_3991_);
lean_ctor_set(v___x_3983_, 2, v___f_3992_);
lean_ctor_set(v___x_3983_, 1, v___f_3985_);
lean_ctor_set(v___x_3983_, 0, v___x_3989_);
v___x_3994_ = v___x_3983_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_3989_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v___f_3985_);
lean_ctor_set(v_reuseFailAlloc_4034_, 2, v___f_3992_);
lean_ctor_set(v_reuseFailAlloc_4034_, 3, v___f_3991_);
lean_ctor_set(v_reuseFailAlloc_4034_, 4, v___f_3990_);
v___x_3994_ = v_reuseFailAlloc_4034_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3996_; 
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 1, v___f_3986_);
lean_ctor_set(v___x_3976_, 0, v___x_3994_);
v___x_3996_ = v___x_3976_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_3994_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v___f_3986_);
v___x_3996_ = v_reuseFailAlloc_4033_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; lean_object* v_toApplicative_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4031_; 
v___x_3997_ = l_StateRefT_x27_instMonad___redArg(v___x_3996_);
v_toApplicative_3998_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4031_ == 0)
{
lean_object* v_unused_4032_; 
v_unused_4032_ = lean_ctor_get(v___x_3997_, 1);
lean_dec(v_unused_4032_);
v___x_4000_ = v___x_3997_;
v_isShared_4001_ = v_isSharedCheck_4031_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_toApplicative_3998_);
lean_dec(v___x_3997_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4031_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v_toFunctor_4002_; lean_object* v_toSeq_4003_; lean_object* v_toSeqLeft_4004_; lean_object* v_toSeqRight_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4029_; 
v_toFunctor_4002_ = lean_ctor_get(v_toApplicative_3998_, 0);
v_toSeq_4003_ = lean_ctor_get(v_toApplicative_3998_, 2);
v_toSeqLeft_4004_ = lean_ctor_get(v_toApplicative_3998_, 3);
v_toSeqRight_4005_ = lean_ctor_get(v_toApplicative_3998_, 4);
v_isSharedCheck_4029_ = !lean_is_exclusive(v_toApplicative_3998_);
if (v_isSharedCheck_4029_ == 0)
{
lean_object* v_unused_4030_; 
v_unused_4030_ = lean_ctor_get(v_toApplicative_3998_, 1);
lean_dec(v_unused_4030_);
v___x_4007_ = v_toApplicative_3998_;
v_isShared_4008_ = v_isSharedCheck_4029_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_toSeqRight_4005_);
lean_inc(v_toSeqLeft_4004_);
lean_inc(v_toSeq_4003_);
lean_inc(v_toFunctor_4002_);
lean_dec(v_toApplicative_3998_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4029_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___f_4009_; lean_object* v___f_4010_; lean_object* v___f_4011_; lean_object* v___f_4012_; lean_object* v___x_4013_; lean_object* v___f_4014_; lean_object* v___f_4015_; lean_object* v___f_4016_; lean_object* v___x_4018_; 
v___f_4009_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__3));
v___f_4010_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4002_);
v___f_4011_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4011_, 0, v_toFunctor_4002_);
v___f_4012_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4012_, 0, v_toFunctor_4002_);
v___x_4013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___f_4011_);
lean_ctor_set(v___x_4013_, 1, v___f_4012_);
v___f_4014_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4014_, 0, v_toSeqRight_4005_);
v___f_4015_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4015_, 0, v_toSeqLeft_4004_);
v___f_4016_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4016_, 0, v_toSeq_4003_);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 4, v___f_4014_);
lean_ctor_set(v___x_4007_, 3, v___f_4015_);
lean_ctor_set(v___x_4007_, 2, v___f_4016_);
lean_ctor_set(v___x_4007_, 1, v___f_4009_);
lean_ctor_set(v___x_4007_, 0, v___x_4013_);
v___x_4018_ = v___x_4007_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4013_);
lean_ctor_set(v_reuseFailAlloc_4028_, 1, v___f_4009_);
lean_ctor_set(v_reuseFailAlloc_4028_, 2, v___f_4016_);
lean_ctor_set(v_reuseFailAlloc_4028_, 3, v___f_4015_);
lean_ctor_set(v_reuseFailAlloc_4028_, 4, v___f_4014_);
v___x_4018_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
lean_object* v___x_4020_; 
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 1, v___f_4010_);
lean_ctor_set(v___x_4000_, 0, v___x_4018_);
v___x_4020_ = v___x_4000_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4018_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v___f_4010_);
v___x_4020_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___f_4024_; lean_object* v___x_15584__overap_4025_; lean_object* v___x_4026_; 
v___x_4021_ = l_StateRefT_x27_instMonad___redArg(v___x_4020_);
v___x_4022_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0);
v___x_4023_ = l_instInhabitedOfMonad___redArg(v___x_4021_, v___x_4022_);
v___f_4024_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4024_, 0, v___x_4023_);
v___x_15584__overap_4025_ = lean_panic_fn_borrowed(v___f_4024_, v_msg_3964_);
lean_dec_ref(v___f_4024_);
lean_inc(v___y_3970_);
lean_inc_ref(v___y_3969_);
lean_inc(v___y_3968_);
lean_inc_ref(v___y_3967_);
lean_inc(v___y_3966_);
lean_inc_ref(v___y_3965_);
v___x_4026_ = lean_apply_7(v___x_15584__overap_4025_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, lean_box(0));
return v___x_4026_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2___boxed(lean_object* v_msg_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v_msg_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
return v_res_4047_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2(void){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4050_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_4051_ = lean_unsigned_to_nat(9u);
v___x_4052_ = lean_unsigned_to_nat(625u);
v___x_4053_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__1));
v___x_4054_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__0));
v___x_4055_ = l_mkPanicMessageWithDecl(v___x_4054_, v___x_4053_, v___x_4052_, v___x_4051_, v___x_4050_);
return v___x_4055_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10(void){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4065_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9));
v___x_4066_ = lean_unsigned_to_nat(14u);
v___x_4067_ = lean_unsigned_to_nat(22u);
v___x_4068_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8));
v___x_4069_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7));
v___x_4070_ = l_mkPanicMessageWithDecl(v___x_4069_, v___x_4068_, v___x_4067_, v___x_4066_, v___x_4065_);
return v___x_4070_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4072_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_4073_ = lean_unsigned_to_nat(22u);
v___x_4074_ = lean_unsigned_to_nat(575u);
v___x_4075_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11));
v___x_4076_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_4077_ = l_mkPanicMessageWithDecl(v___x_4076_, v___x_4075_, v___x_4074_, v___x_4073_, v___x_4072_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(lean_object* v_code_4078_, lean_object* v_decl_4079_, lean_object* v_k_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v_fvarId_4088_; lean_object* v_value_4089_; lean_object* v_k_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v_k_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___x_4164_; 
v_fvarId_4088_ = lean_ctor_get(v_decl_4079_, 0);
lean_inc_n(v_fvarId_4088_, 2);
v_value_4089_ = lean_ctor_get(v_decl_4079_, 3);
lean_inc(v_value_4089_);
v___x_4164_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_4088_, v_k_4080_, v_a_4081_, v_a_4082_);
switch(lean_obj_tag(v_value_4089_))
{
case 4:
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4207_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4167_ = v___x_4164_;
v_isShared_4168_ = v_isSharedCheck_4207_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4164_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4207_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v_fvarId_4169_; lean_object* v_args_4170_; lean_object* v___x_4172_; 
v_fvarId_4169_ = lean_ctor_get(v_value_4089_, 0);
v_args_4170_ = lean_ctor_get(v_value_4089_, 1);
lean_inc(v_fvarId_4169_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set_tag(v___x_4167_, 1);
lean_ctor_set(v___x_4167_, 0, v_fvarId_4169_);
v___x_4172_ = v___x_4167_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_fvarId_4169_);
v___x_4172_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4173_; lean_object* v___y_4175_; 
lean_inc_ref(v_args_4170_);
v___x_4173_ = lean_array_push(v_args_4170_, v___x_4172_);
if (lean_obj_tag(v_code_4078_) == 0)
{
lean_object* v_decl_4178_; lean_object* v_k_4179_; size_t v___x_4180_; size_t v___x_4181_; uint8_t v___x_4182_; 
v_decl_4178_ = lean_ctor_get(v_code_4078_, 0);
v_k_4179_ = lean_ctor_get(v_code_4078_, 1);
v___x_4180_ = lean_ptr_addr(v_k_4179_);
v___x_4181_ = lean_ptr_addr(v_a_4165_);
v___x_4182_ = lean_usize_dec_eq(v___x_4180_, v___x_4181_);
if (v___x_4182_ == 0)
{
lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
v_isSharedCheck_4189_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4189_ == 0)
{
lean_object* v_unused_4190_; lean_object* v_unused_4191_; 
v_unused_4190_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4190_);
v_unused_4191_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4191_);
v___x_4184_ = v_code_4078_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_dec(v_code_4078_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
lean_ctor_set(v___x_4184_, 1, v_a_4165_);
lean_ctor_set(v___x_4184_, 0, v_decl_4079_);
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4188_, 1, v_a_4165_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
v___y_4175_ = v___x_4187_;
goto v___jp_4174_;
}
}
}
else
{
size_t v___x_4192_; size_t v___x_4193_; uint8_t v___x_4194_; 
v___x_4192_ = lean_ptr_addr(v_decl_4178_);
v___x_4193_ = lean_ptr_addr(v_decl_4079_);
v___x_4194_ = lean_usize_dec_eq(v___x_4192_, v___x_4193_);
if (v___x_4194_ == 0)
{
lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
v_isSharedCheck_4201_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4201_ == 0)
{
lean_object* v_unused_4202_; lean_object* v_unused_4203_; 
v_unused_4202_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4202_);
v_unused_4203_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4203_);
v___x_4196_ = v_code_4078_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_dec(v_code_4078_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
lean_ctor_set(v___x_4196_, 1, v_a_4165_);
lean_ctor_set(v___x_4196_, 0, v_decl_4079_);
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v_a_4165_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
v___y_4175_ = v___x_4199_;
goto v___jp_4174_;
}
}
}
else
{
lean_dec(v_a_4165_);
lean_dec_ref(v_decl_4079_);
v___y_4175_ = v_code_4078_;
goto v___jp_4174_;
}
}
}
else
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_dec(v_a_4165_);
lean_dec_ref(v_decl_4079_);
lean_dec_ref(v_code_4078_);
v___x_4204_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4205_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4204_);
v___y_4175_ = v___x_4205_;
goto v___jp_4174_;
}
v___jp_4174_:
{
lean_object* v___x_4176_; 
v___x_4176_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v___x_4173_, v___y_4175_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
lean_dec_ref(v___x_4173_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref_known(v___x_4176_, 1);
v_k_4091_ = v_a_4177_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
else
{
lean_dec_ref_known(v_value_4089_, 2);
lean_dec(v_fvarId_4088_);
return v___x_4176_;
}
}
}
}
}
case 5:
{
lean_object* v_a_4208_; lean_object* v_args_4209_; lean_object* v___y_4211_; 
v_a_4208_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4208_);
lean_dec_ref(v___x_4164_);
v_args_4209_ = lean_ctor_get(v_value_4089_, 1);
if (lean_obj_tag(v_code_4078_) == 0)
{
lean_object* v_decl_4214_; lean_object* v_k_4215_; size_t v___x_4216_; size_t v___x_4217_; uint8_t v___x_4218_; 
v_decl_4214_ = lean_ctor_get(v_code_4078_, 0);
v_k_4215_ = lean_ctor_get(v_code_4078_, 1);
v___x_4216_ = lean_ptr_addr(v_k_4215_);
v___x_4217_ = lean_ptr_addr(v_a_4208_);
v___x_4218_ = lean_usize_dec_eq(v___x_4216_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
v_isSharedCheck_4225_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4225_ == 0)
{
lean_object* v_unused_4226_; lean_object* v_unused_4227_; 
v_unused_4226_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4226_);
v_unused_4227_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4227_);
v___x_4220_ = v_code_4078_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_dec(v_code_4078_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 1, v_a_4208_);
lean_ctor_set(v___x_4220_, 0, v_decl_4079_);
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v_a_4208_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
v___y_4211_ = v___x_4223_;
goto v___jp_4210_;
}
}
}
else
{
size_t v___x_4228_; size_t v___x_4229_; uint8_t v___x_4230_; 
v___x_4228_ = lean_ptr_addr(v_decl_4214_);
v___x_4229_ = lean_ptr_addr(v_decl_4079_);
v___x_4230_ = lean_usize_dec_eq(v___x_4228_, v___x_4229_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
v_isSharedCheck_4237_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4237_ == 0)
{
lean_object* v_unused_4238_; lean_object* v_unused_4239_; 
v_unused_4238_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4238_);
v_unused_4239_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4239_);
v___x_4232_ = v_code_4078_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_dec(v_code_4078_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 1, v_a_4208_);
lean_ctor_set(v___x_4232_, 0, v_decl_4079_);
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v_a_4208_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
v___y_4211_ = v___x_4235_;
goto v___jp_4210_;
}
}
}
else
{
lean_dec(v_a_4208_);
lean_dec_ref(v_decl_4079_);
v___y_4211_ = v_code_4078_;
goto v___jp_4210_;
}
}
}
else
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
lean_dec(v_a_4208_);
lean_dec_ref(v_decl_4079_);
lean_dec_ref(v_code_4078_);
v___x_4240_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4241_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4240_);
v___y_4211_ = v___x_4241_;
goto v___jp_4210_;
}
v___jp_4210_:
{
lean_object* v___x_4212_; 
v___x_4212_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4209_, v___y_4211_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4212_, 1);
v_k_4091_ = v_a_4213_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
else
{
lean_dec_ref_known(v_value_4089_, 2);
lean_dec(v_fvarId_4088_);
return v___x_4212_;
}
}
}
case 6:
{
lean_object* v_a_4242_; lean_object* v_var_4243_; lean_object* v___x_4244_; lean_object* v_a_4245_; lean_object* v___x_4246_; lean_object* v_borrows_4247_; uint8_t v___x_4248_; 
v_a_4242_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4242_);
lean_dec_ref(v___x_4164_);
v_var_4243_ = lean_ctor_get(v_value_4089_, 1);
lean_inc(v_var_4243_);
v___x_4244_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4243_, v_a_4242_, v_a_4081_, v_a_4082_);
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref(v___x_4244_);
v___x_4246_ = lean_st_ref_get(v_a_4082_);
v_borrows_4247_ = lean_ctor_get(v___x_4246_, 1);
lean_inc_ref(v_borrows_4247_);
lean_dec(v___x_4246_);
v___x_4248_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4247_, v_fvarId_4088_);
lean_dec_ref(v_borrows_4247_);
if (v___x_4248_ == 0)
{
lean_object* v_varMap_4249_; lean_object* v___x_4250_; uint8_t v_isDefiniteRef_4251_; lean_object* v___x_4252_; uint8_t v___y_4254_; 
v_varMap_4249_ = lean_ctor_get(v_a_4081_, 3);
v___x_4250_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_4249_, v_fvarId_4088_);
v_isDefiniteRef_4251_ = lean_ctor_get_uint8(v___x_4250_, sizeof(void*)*2 + 1);
v___x_4252_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_4251_ == 0)
{
uint8_t v___x_4257_; 
v___x_4257_ = 1;
v___y_4254_ = v___x_4257_;
goto v___jp_4253_;
}
else
{
v___y_4254_ = v___x_4248_;
goto v___jp_4253_;
}
v___jp_4253_:
{
uint8_t v_persistent_4255_; lean_object* v___x_4256_; 
v_persistent_4255_ = lean_ctor_get_uint8(v___x_4250_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_4250_);
lean_inc(v_fvarId_4088_);
v___x_4256_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_4256_, 0, v_fvarId_4088_);
lean_ctor_set(v___x_4256_, 1, v___x_4252_);
lean_ctor_set(v___x_4256_, 2, v_a_4245_);
lean_ctor_set_uint8(v___x_4256_, sizeof(void*)*3, v___y_4254_);
lean_ctor_set_uint8(v___x_4256_, sizeof(void*)*3 + 1, v_persistent_4255_);
v_k_4129_ = v___x_4256_;
v___y_4130_ = v_a_4081_;
v___y_4131_ = v_a_4082_;
v___y_4132_ = v_a_4083_;
v___y_4133_ = v_a_4084_;
v___y_4134_ = v_a_4085_;
v___y_4135_ = v_a_4086_;
goto v___jp_4128_;
}
}
else
{
v_k_4129_ = v_a_4245_;
v___y_4130_ = v_a_4081_;
v___y_4131_ = v_a_4082_;
v___y_4132_ = v_a_4083_;
v___y_4133_ = v_a_4084_;
v___y_4134_ = v_a_4085_;
v___y_4135_ = v_a_4086_;
goto v___jp_4128_;
}
}
case 7:
{
lean_object* v_a_4258_; lean_object* v_var_4259_; lean_object* v___x_4260_; 
v_a_4258_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4258_);
lean_dec_ref(v___x_4164_);
v_var_4259_ = lean_ctor_get(v_value_4089_, 1);
lean_inc(v_var_4259_);
v___x_4260_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4259_, v_a_4258_, v_a_4081_, v_a_4082_);
if (lean_obj_tag(v_code_4078_) == 0)
{
lean_object* v_a_4261_; lean_object* v_decl_4262_; lean_object* v_k_4263_; size_t v___x_4264_; size_t v___x_4265_; uint8_t v___x_4266_; 
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
lean_inc(v_a_4261_);
lean_dec_ref(v___x_4260_);
v_decl_4262_ = lean_ctor_get(v_code_4078_, 0);
v_k_4263_ = lean_ctor_get(v_code_4078_, 1);
v___x_4264_ = lean_ptr_addr(v_k_4263_);
v___x_4265_ = lean_ptr_addr(v_a_4261_);
v___x_4266_ = lean_usize_dec_eq(v___x_4264_, v___x_4265_);
if (v___x_4266_ == 0)
{
lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
v_isSharedCheck_4273_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4273_ == 0)
{
lean_object* v_unused_4274_; lean_object* v_unused_4275_; 
v_unused_4274_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4274_);
v_unused_4275_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4275_);
v___x_4268_ = v_code_4078_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_dec(v_code_4078_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
lean_ctor_set(v___x_4268_, 1, v_a_4261_);
lean_ctor_set(v___x_4268_, 0, v_decl_4079_);
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4272_, 1, v_a_4261_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
v_k_4091_ = v___x_4271_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
else
{
size_t v___x_4276_; size_t v___x_4277_; uint8_t v___x_4278_; 
v___x_4276_ = lean_ptr_addr(v_decl_4262_);
v___x_4277_ = lean_ptr_addr(v_decl_4079_);
v___x_4278_ = lean_usize_dec_eq(v___x_4276_, v___x_4277_);
if (v___x_4278_ == 0)
{
lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
v_isSharedCheck_4285_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4285_ == 0)
{
lean_object* v_unused_4286_; lean_object* v_unused_4287_; 
v_unused_4286_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4286_);
v_unused_4287_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4287_);
v___x_4280_ = v_code_4078_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_dec(v_code_4078_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 1, v_a_4261_);
lean_ctor_set(v___x_4280_, 0, v_decl_4079_);
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_a_4261_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
v_k_4091_ = v___x_4283_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
else
{
lean_dec(v_a_4261_);
lean_dec_ref(v_decl_4079_);
v_k_4091_ = v_code_4078_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
else
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
lean_dec_ref(v___x_4260_);
lean_dec_ref(v_decl_4079_);
lean_dec_ref(v_code_4078_);
v___x_4288_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4289_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4288_);
v_k_4091_ = v___x_4289_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
case 8:
{
lean_object* v_a_4290_; lean_object* v_var_4291_; lean_object* v___x_4292_; 
v_a_4290_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4290_);
lean_dec_ref(v___x_4164_);
v_var_4291_ = lean_ctor_get(v_value_4089_, 2);
lean_inc(v_var_4291_);
v___x_4292_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4291_, v_a_4290_, v_a_4081_, v_a_4082_);
if (lean_obj_tag(v_code_4078_) == 0)
{
lean_object* v_a_4293_; lean_object* v_decl_4294_; lean_object* v_k_4295_; size_t v___x_4296_; size_t v___x_4297_; uint8_t v___x_4298_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
lean_inc(v_a_4293_);
lean_dec_ref(v___x_4292_);
v_decl_4294_ = lean_ctor_get(v_code_4078_, 0);
v_k_4295_ = lean_ctor_get(v_code_4078_, 1);
v___x_4296_ = lean_ptr_addr(v_k_4295_);
v___x_4297_ = lean_ptr_addr(v_a_4293_);
v___x_4298_ = lean_usize_dec_eq(v___x_4296_, v___x_4297_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
v_isSharedCheck_4305_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4305_ == 0)
{
lean_object* v_unused_4306_; lean_object* v_unused_4307_; 
v_unused_4306_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4306_);
v_unused_4307_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4307_);
v___x_4300_ = v_code_4078_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_dec(v_code_4078_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 1, v_a_4293_);
lean_ctor_set(v___x_4300_, 0, v_decl_4079_);
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4304_, 1, v_a_4293_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
v_k_4091_ = v___x_4303_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
else
{
size_t v___x_4308_; size_t v___x_4309_; uint8_t v___x_4310_; 
v___x_4308_ = lean_ptr_addr(v_decl_4294_);
v___x_4309_ = lean_ptr_addr(v_decl_4079_);
v___x_4310_ = lean_usize_dec_eq(v___x_4308_, v___x_4309_);
if (v___x_4310_ == 0)
{
lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
v_isSharedCheck_4317_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4317_ == 0)
{
lean_object* v_unused_4318_; lean_object* v_unused_4319_; 
v_unused_4318_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4318_);
v_unused_4319_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4319_);
v___x_4312_ = v_code_4078_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_dec(v_code_4078_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
lean_ctor_set(v___x_4312_, 1, v_a_4293_);
lean_ctor_set(v___x_4312_, 0, v_decl_4079_);
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4316_, 1, v_a_4293_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
v_k_4091_ = v___x_4315_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
else
{
lean_dec(v_a_4293_);
lean_dec_ref(v_decl_4079_);
v_k_4091_ = v_code_4078_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
else
{
lean_object* v___x_4320_; lean_object* v___x_4321_; 
lean_dec_ref(v___x_4292_);
lean_dec_ref(v_decl_4079_);
lean_dec_ref(v_code_4078_);
v___x_4320_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4321_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4320_);
v_k_4091_ = v___x_4321_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
case 9:
{
lean_object* v_a_4322_; lean_object* v_fn_4323_; lean_object* v_args_4324_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___x_4336_; 
v_a_4322_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4322_);
lean_dec_ref(v___x_4164_);
v_fn_4323_ = lean_ctor_get(v_value_4089_, 0);
v_args_4324_ = lean_ctor_get(v_value_4089_, 1);
lean_inc(v_fn_4323_);
v___x_4336_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_4323_, v_a_4086_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; uint8_t v___x_4338_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v_value_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; uint8_t v___y_4391_; uint8_t v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; uint8_t v___y_4400_; uint8_t v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; uint8_t v___y_4411_; lean_object* v___y_4412_; uint8_t v___y_4413_; lean_object* v___y_4421_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4337_);
lean_dec_ref_known(v___x_4336_, 1);
v___x_4338_ = 1;
if (lean_obj_tag(v_a_4337_) == 0)
{
lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4437_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10);
v___x_4438_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1(v___x_4437_);
v___y_4421_ = v___x_4438_;
goto v___jp_4420_;
}
else
{
lean_object* v_val_4439_; 
v_val_4439_ = lean_ctor_get(v_a_4337_, 0);
lean_inc(v_val_4439_);
lean_dec_ref_known(v_a_4337_, 1);
v___y_4421_ = v_val_4439_;
goto v___jp_4420_;
}
v___jp_4339_:
{
lean_object* v___x_4349_; 
v___x_4349_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_4338_, v_decl_4079_, v_value_4342_, v___y_4346_);
if (lean_obj_tag(v___x_4349_) == 0)
{
if (lean_obj_tag(v_code_4078_) == 0)
{
lean_object* v_a_4350_; lean_object* v_decl_4351_; lean_object* v_k_4352_; size_t v___x_4353_; size_t v___x_4354_; uint8_t v___x_4355_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___x_4349_, 1);
v_decl_4351_ = lean_ctor_get(v_code_4078_, 0);
v_k_4352_ = lean_ctor_get(v_code_4078_, 1);
v___x_4353_ = lean_ptr_addr(v_k_4352_);
v___x_4354_ = lean_ptr_addr(v___y_4340_);
v___x_4355_ = lean_usize_dec_eq(v___x_4353_, v___x_4354_);
if (v___x_4355_ == 0)
{
lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
v_isSharedCheck_4362_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4362_ == 0)
{
lean_object* v_unused_4363_; lean_object* v_unused_4364_; 
v_unused_4363_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4363_);
v_unused_4364_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4364_);
v___x_4357_ = v_code_4078_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_dec(v_code_4078_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 1, v___y_4340_);
lean_ctor_set(v___x_4357_, 0, v_a_4350_);
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4350_);
lean_ctor_set(v_reuseFailAlloc_4361_, 1, v___y_4340_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
v___y_4326_ = v___y_4344_;
v___y_4327_ = v___y_4347_;
v___y_4328_ = v___y_4346_;
v___y_4329_ = v___y_4345_;
v___y_4330_ = v___y_4343_;
v___y_4331_ = v___y_4341_;
v___y_4332_ = v___y_4348_;
v___y_4333_ = v___x_4360_;
goto v___jp_4325_;
}
}
}
else
{
size_t v___x_4365_; size_t v___x_4366_; uint8_t v___x_4367_; 
v___x_4365_ = lean_ptr_addr(v_decl_4351_);
v___x_4366_ = lean_ptr_addr(v_a_4350_);
v___x_4367_ = lean_usize_dec_eq(v___x_4365_, v___x_4366_);
if (v___x_4367_ == 0)
{
lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
v_isSharedCheck_4374_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4374_ == 0)
{
lean_object* v_unused_4375_; lean_object* v_unused_4376_; 
v_unused_4375_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4375_);
v_unused_4376_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4376_);
v___x_4369_ = v_code_4078_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_dec(v_code_4078_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 1, v___y_4340_);
lean_ctor_set(v___x_4369_, 0, v_a_4350_);
v___x_4372_ = v___x_4369_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_a_4350_);
lean_ctor_set(v_reuseFailAlloc_4373_, 1, v___y_4340_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
v___y_4326_ = v___y_4344_;
v___y_4327_ = v___y_4347_;
v___y_4328_ = v___y_4346_;
v___y_4329_ = v___y_4345_;
v___y_4330_ = v___y_4343_;
v___y_4331_ = v___y_4341_;
v___y_4332_ = v___y_4348_;
v___y_4333_ = v___x_4372_;
goto v___jp_4325_;
}
}
}
else
{
lean_dec(v_a_4350_);
lean_dec_ref(v___y_4340_);
v___y_4326_ = v___y_4344_;
v___y_4327_ = v___y_4347_;
v___y_4328_ = v___y_4346_;
v___y_4329_ = v___y_4345_;
v___y_4330_ = v___y_4343_;
v___y_4331_ = v___y_4341_;
v___y_4332_ = v___y_4348_;
v___y_4333_ = v_code_4078_;
goto v___jp_4325_;
}
}
}
else
{
lean_object* v___x_4377_; lean_object* v___x_4378_; 
lean_dec_ref_known(v___x_4349_, 1);
lean_dec_ref(v___y_4340_);
lean_dec_ref(v_code_4078_);
v___x_4377_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4378_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4377_);
v___y_4326_ = v___y_4344_;
v___y_4327_ = v___y_4347_;
v___y_4328_ = v___y_4346_;
v___y_4329_ = v___y_4345_;
v___y_4330_ = v___y_4343_;
v___y_4331_ = v___y_4341_;
v___y_4332_ = v___y_4348_;
v___y_4333_ = v___x_4378_;
goto v___jp_4325_;
}
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
lean_dec_ref(v___y_4341_);
lean_dec_ref(v___y_4340_);
lean_dec_ref_known(v_value_4089_, 2);
lean_dec(v_fvarId_4088_);
lean_dec_ref(v_code_4078_);
v_a_4379_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4349_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4349_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
v___jp_4387_:
{
if (v___y_4391_ == 0)
{
lean_inc_ref(v_value_4089_);
v___y_4340_ = v___y_4388_;
v___y_4341_ = v___y_4389_;
v_value_4342_ = v_value_4089_;
v___y_4343_ = v_a_4081_;
v___y_4344_ = v_a_4082_;
v___y_4345_ = v_a_4083_;
v___y_4346_ = v_a_4084_;
v___y_4347_ = v_a_4085_;
v___y_4348_ = v_a_4086_;
goto v___jp_4339_;
}
else
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4392_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__3));
lean_inc_ref(v___y_4390_);
v___x_4393_ = l_Lean_Name_mkStr2(v___y_4390_, v___x_4392_);
lean_inc_ref(v_args_4324_);
v___x_4394_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4393_);
lean_ctor_set(v___x_4394_, 1, v_args_4324_);
v___y_4340_ = v___y_4388_;
v___y_4341_ = v___y_4389_;
v_value_4342_ = v___x_4394_;
v___y_4343_ = v_a_4081_;
v___y_4344_ = v_a_4082_;
v___y_4345_ = v_a_4083_;
v___y_4346_ = v_a_4084_;
v___y_4347_ = v_a_4085_;
v___y_4348_ = v_a_4086_;
goto v___jp_4339_;
}
}
v___jp_4395_:
{
if (v___y_4400_ == 0)
{
lean_object* v___x_4401_; lean_object* v___x_4402_; uint8_t v___x_4403_; 
v___x_4401_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__3));
lean_inc_ref(v___y_4399_);
v___x_4402_ = l_Lean_Name_mkStr2(v___y_4399_, v___x_4401_);
v___x_4403_ = lean_name_eq(v_fn_4323_, v___x_4402_);
lean_dec(v___x_4402_);
if (v___x_4403_ == 0)
{
v___y_4388_ = v___y_4397_;
v___y_4389_ = v___y_4398_;
v___y_4390_ = v___y_4399_;
v___y_4391_ = v___x_4403_;
goto v___jp_4387_;
}
else
{
v___y_4388_ = v___y_4397_;
v___y_4389_ = v___y_4398_;
v___y_4390_ = v___y_4399_;
v___y_4391_ = v___y_4396_;
goto v___jp_4387_;
}
}
else
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4404_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__4));
lean_inc_ref(v___y_4399_);
v___x_4405_ = l_Lean_Name_mkStr2(v___y_4399_, v___x_4404_);
lean_inc_ref(v_args_4324_);
v___x_4406_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4405_);
lean_ctor_set(v___x_4406_, 1, v_args_4324_);
v___y_4340_ = v___y_4397_;
v___y_4341_ = v___y_4398_;
v_value_4342_ = v___x_4406_;
v___y_4343_ = v_a_4081_;
v___y_4344_ = v_a_4082_;
v___y_4345_ = v_a_4083_;
v___y_4346_ = v_a_4084_;
v___y_4347_ = v_a_4085_;
v___y_4348_ = v_a_4086_;
goto v___jp_4339_;
}
}
v___jp_4407_:
{
if (v___y_4413_ == 0)
{
lean_object* v___x_4414_; lean_object* v___x_4415_; uint8_t v___x_4416_; 
v___x_4414_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__2));
lean_inc_ref(v___y_4412_);
v___x_4415_ = l_Lean_Name_mkStr2(v___y_4412_, v___x_4414_);
v___x_4416_ = lean_name_eq(v_fn_4323_, v___x_4415_);
lean_dec(v___x_4415_);
if (v___x_4416_ == 0)
{
v___y_4396_ = v___y_4408_;
v___y_4397_ = v___y_4409_;
v___y_4398_ = v___y_4410_;
v___y_4399_ = v___y_4412_;
v___y_4400_ = v___x_4416_;
goto v___jp_4395_;
}
else
{
v___y_4396_ = v___y_4408_;
v___y_4397_ = v___y_4409_;
v___y_4398_ = v___y_4410_;
v___y_4399_ = v___y_4412_;
v___y_4400_ = v___y_4411_;
goto v___jp_4395_;
}
}
else
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4417_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5));
lean_inc_ref(v___y_4412_);
v___x_4418_ = l_Lean_Name_mkStr2(v___y_4412_, v___x_4417_);
lean_inc_ref(v_args_4324_);
v___x_4419_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
lean_ctor_set(v___x_4419_, 1, v_args_4324_);
v___y_4340_ = v___y_4409_;
v___y_4341_ = v___y_4410_;
v_value_4342_ = v___x_4419_;
v___y_4343_ = v_a_4081_;
v___y_4344_ = v_a_4082_;
v___y_4345_ = v_a_4083_;
v___y_4346_ = v_a_4084_;
v___y_4347_ = v_a_4085_;
v___y_4348_ = v_a_4086_;
goto v___jp_4339_;
}
}
v___jp_4420_:
{
lean_object* v_params_4422_; lean_object* v___x_4423_; 
v_params_4422_ = lean_ctor_get(v___y_4421_, 3);
lean_inc_ref_n(v_params_4422_, 2);
lean_dec_ref(v___y_4421_);
v___x_4423_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(v_args_4324_, v_params_4422_, v_a_4322_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; lean_object* v___x_4425_; lean_object* v_borrows_4426_; uint8_t v___x_4427_; lean_object* v___x_4428_; lean_object* v_borrows_4429_; uint8_t v___x_4430_; lean_object* v___x_4431_; lean_object* v_borrows_4432_; uint8_t v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; uint8_t v___x_4436_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_a_4424_);
lean_dec_ref_known(v___x_4423_, 1);
v___x_4425_ = lean_st_ref_get(v_a_4082_);
v_borrows_4426_ = lean_ctor_get(v___x_4425_, 1);
lean_inc_ref(v_borrows_4426_);
lean_dec(v___x_4425_);
v___x_4427_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4426_, v_fvarId_4088_);
lean_dec_ref(v_borrows_4426_);
v___x_4428_ = lean_st_ref_get(v_a_4082_);
v_borrows_4429_ = lean_ctor_get(v___x_4428_, 1);
lean_inc_ref(v_borrows_4429_);
lean_dec(v___x_4428_);
v___x_4430_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4429_, v_fvarId_4088_);
lean_dec_ref(v_borrows_4429_);
v___x_4431_ = lean_st_ref_get(v_a_4082_);
v_borrows_4432_ = lean_ctor_get(v___x_4431_, 1);
lean_inc_ref(v_borrows_4432_);
lean_dec(v___x_4431_);
v___x_4433_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4432_, v_fvarId_4088_);
lean_dec_ref(v_borrows_4432_);
v___x_4434_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0));
v___x_4435_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6));
v___x_4436_ = lean_name_eq(v_fn_4323_, v___x_4435_);
if (v___x_4436_ == 0)
{
v___y_4408_ = v___x_4433_;
v___y_4409_ = v_a_4424_;
v___y_4410_ = v_params_4422_;
v___y_4411_ = v___x_4430_;
v___y_4412_ = v___x_4434_;
v___y_4413_ = v___x_4436_;
goto v___jp_4407_;
}
else
{
v___y_4408_ = v___x_4433_;
v___y_4409_ = v_a_4424_;
v___y_4410_ = v_params_4422_;
v___y_4411_ = v___x_4430_;
v___y_4412_ = v___x_4434_;
v___y_4413_ = v___x_4427_;
goto v___jp_4407_;
}
}
else
{
lean_dec_ref(v_params_4422_);
lean_dec_ref_known(v_value_4089_, 2);
lean_dec(v_fvarId_4088_);
lean_dec_ref(v_decl_4079_);
lean_dec_ref(v_code_4078_);
return v___x_4423_;
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_dec_ref_known(v_value_4089_, 2);
lean_dec(v_a_4322_);
lean_dec(v_fvarId_4088_);
lean_dec_ref(v_decl_4079_);
lean_dec_ref(v_code_4078_);
v_a_4440_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4336_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4336_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
v___jp_4325_:
{
lean_object* v___x_4334_; 
v___x_4334_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_4324_, v___y_4331_, v___y_4333_, v___y_4330_, v___y_4326_, v___y_4329_, v___y_4328_, v___y_4327_, v___y_4332_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4334_, 1);
v_k_4091_ = v_a_4335_;
v___y_4092_ = v___y_4330_;
v___y_4093_ = v___y_4326_;
v___y_4094_ = v___y_4329_;
v___y_4095_ = v___y_4328_;
v___y_4096_ = v___y_4327_;
v___y_4097_ = v___y_4332_;
goto v___jp_4090_;
}
else
{
lean_dec_ref_known(v_value_4089_, 2);
lean_dec(v_fvarId_4088_);
return v___x_4334_;
}
}
}
case 10:
{
lean_object* v_a_4448_; lean_object* v_args_4449_; lean_object* v___y_4451_; 
v_a_4448_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4448_);
lean_dec_ref(v___x_4164_);
v_args_4449_ = lean_ctor_get(v_value_4089_, 1);
if (lean_obj_tag(v_code_4078_) == 0)
{
lean_object* v_decl_4454_; lean_object* v_k_4455_; size_t v___x_4456_; size_t v___x_4457_; uint8_t v___x_4458_; 
v_decl_4454_ = lean_ctor_get(v_code_4078_, 0);
v_k_4455_ = lean_ctor_get(v_code_4078_, 1);
v___x_4456_ = lean_ptr_addr(v_k_4455_);
v___x_4457_ = lean_ptr_addr(v_a_4448_);
v___x_4458_ = lean_usize_dec_eq(v___x_4456_, v___x_4457_);
if (v___x_4458_ == 0)
{
lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
v_isSharedCheck_4465_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4465_ == 0)
{
lean_object* v_unused_4466_; lean_object* v_unused_4467_; 
v_unused_4466_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4466_);
v_unused_4467_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4467_);
v___x_4460_ = v_code_4078_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_dec(v_code_4078_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 1, v_a_4448_);
lean_ctor_set(v___x_4460_, 0, v_decl_4079_);
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v_a_4448_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
v___y_4451_ = v___x_4463_;
goto v___jp_4450_;
}
}
}
else
{
size_t v___x_4468_; size_t v___x_4469_; uint8_t v___x_4470_; 
v___x_4468_ = lean_ptr_addr(v_decl_4454_);
v___x_4469_ = lean_ptr_addr(v_decl_4079_);
v___x_4470_ = lean_usize_dec_eq(v___x_4468_, v___x_4469_);
if (v___x_4470_ == 0)
{
lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
v_isSharedCheck_4477_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4477_ == 0)
{
lean_object* v_unused_4478_; lean_object* v_unused_4479_; 
v_unused_4478_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4478_);
v_unused_4479_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4479_);
v___x_4472_ = v_code_4078_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_dec(v_code_4078_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 1, v_a_4448_);
lean_ctor_set(v___x_4472_, 0, v_decl_4079_);
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4476_, 1, v_a_4448_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
v___y_4451_ = v___x_4475_;
goto v___jp_4450_;
}
}
}
else
{
lean_dec(v_a_4448_);
lean_dec_ref(v_decl_4079_);
v___y_4451_ = v_code_4078_;
goto v___jp_4450_;
}
}
}
else
{
lean_object* v___x_4480_; lean_object* v___x_4481_; 
lean_dec(v_a_4448_);
lean_dec_ref(v_decl_4079_);
lean_dec_ref(v_code_4078_);
v___x_4480_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4481_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4480_);
v___y_4451_ = v___x_4481_;
goto v___jp_4450_;
}
v___jp_4450_:
{
lean_object* v___x_4452_; 
v___x_4452_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4449_, v___y_4451_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v_a_4453_; 
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc(v_a_4453_);
lean_dec_ref_known(v___x_4452_, 1);
v_k_4091_ = v_a_4453_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
else
{
lean_dec_ref_known(v_value_4089_, 2);
lean_dec(v_fvarId_4088_);
return v___x_4452_;
}
}
}
case 12:
{
lean_object* v_a_4482_; lean_object* v_args_4483_; lean_object* v___y_4485_; 
v_a_4482_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4482_);
lean_dec_ref(v___x_4164_);
v_args_4483_ = lean_ctor_get(v_value_4089_, 2);
if (lean_obj_tag(v_code_4078_) == 0)
{
lean_object* v_decl_4488_; lean_object* v_k_4489_; size_t v___x_4490_; size_t v___x_4491_; uint8_t v___x_4492_; 
v_decl_4488_ = lean_ctor_get(v_code_4078_, 0);
v_k_4489_ = lean_ctor_get(v_code_4078_, 1);
v___x_4490_ = lean_ptr_addr(v_k_4489_);
v___x_4491_ = lean_ptr_addr(v_a_4482_);
v___x_4492_ = lean_usize_dec_eq(v___x_4490_, v___x_4491_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
v_isSharedCheck_4499_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4499_ == 0)
{
lean_object* v_unused_4500_; lean_object* v_unused_4501_; 
v_unused_4500_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4500_);
v_unused_4501_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4501_);
v___x_4494_ = v_code_4078_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_dec(v_code_4078_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 1, v_a_4482_);
lean_ctor_set(v___x_4494_, 0, v_decl_4079_);
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v_a_4482_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
v___y_4485_ = v___x_4497_;
goto v___jp_4484_;
}
}
}
else
{
size_t v___x_4502_; size_t v___x_4503_; uint8_t v___x_4504_; 
v___x_4502_ = lean_ptr_addr(v_decl_4488_);
v___x_4503_ = lean_ptr_addr(v_decl_4079_);
v___x_4504_ = lean_usize_dec_eq(v___x_4502_, v___x_4503_);
if (v___x_4504_ == 0)
{
lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
v_isSharedCheck_4511_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4511_ == 0)
{
lean_object* v_unused_4512_; lean_object* v_unused_4513_; 
v_unused_4512_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4512_);
v_unused_4513_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4513_);
v___x_4506_ = v_code_4078_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_dec(v_code_4078_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
lean_ctor_set(v___x_4506_, 1, v_a_4482_);
lean_ctor_set(v___x_4506_, 0, v_decl_4079_);
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4510_, 1, v_a_4482_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
v___y_4485_ = v___x_4509_;
goto v___jp_4484_;
}
}
}
else
{
lean_dec(v_a_4482_);
lean_dec_ref(v_decl_4079_);
v___y_4485_ = v_code_4078_;
goto v___jp_4484_;
}
}
}
else
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
lean_dec(v_a_4482_);
lean_dec_ref(v_decl_4079_);
lean_dec_ref(v_code_4078_);
v___x_4514_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4515_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4514_);
v___y_4485_ = v___x_4515_;
goto v___jp_4484_;
}
v___jp_4484_:
{
lean_object* v___x_4486_; 
v___x_4486_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4483_, v___y_4485_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; 
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4486_, 1);
v_k_4091_ = v_a_4487_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
else
{
lean_dec_ref_known(v_value_4089_, 3);
lean_dec(v_fvarId_4088_);
return v___x_4486_;
}
}
}
case 14:
{
lean_object* v_a_4516_; lean_object* v_fvarId_4517_; lean_object* v___x_4518_; 
v_a_4516_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4516_);
lean_dec_ref(v___x_4164_);
v_fvarId_4517_ = lean_ctor_get(v_value_4089_, 0);
lean_inc(v_fvarId_4517_);
v___x_4518_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_4517_, v_a_4516_, v_a_4081_, v_a_4082_);
if (lean_obj_tag(v_code_4078_) == 0)
{
lean_object* v_a_4519_; lean_object* v_decl_4520_; lean_object* v_k_4521_; size_t v___x_4522_; size_t v___x_4523_; uint8_t v___x_4524_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
lean_inc(v_a_4519_);
lean_dec_ref(v___x_4518_);
v_decl_4520_ = lean_ctor_get(v_code_4078_, 0);
v_k_4521_ = lean_ctor_get(v_code_4078_, 1);
v___x_4522_ = lean_ptr_addr(v_k_4521_);
v___x_4523_ = lean_ptr_addr(v_a_4519_);
v___x_4524_ = lean_usize_dec_eq(v___x_4522_, v___x_4523_);
if (v___x_4524_ == 0)
{
lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4531_; 
v_isSharedCheck_4531_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4531_ == 0)
{
lean_object* v_unused_4532_; lean_object* v_unused_4533_; 
v_unused_4532_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4532_);
v_unused_4533_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4533_);
v___x_4526_ = v_code_4078_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_dec(v_code_4078_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 1, v_a_4519_);
lean_ctor_set(v___x_4526_, 0, v_decl_4079_);
v___x_4529_ = v___x_4526_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4530_, 1, v_a_4519_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
v_k_4091_ = v___x_4529_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
else
{
size_t v___x_4534_; size_t v___x_4535_; uint8_t v___x_4536_; 
v___x_4534_ = lean_ptr_addr(v_decl_4520_);
v___x_4535_ = lean_ptr_addr(v_decl_4079_);
v___x_4536_ = lean_usize_dec_eq(v___x_4534_, v___x_4535_);
if (v___x_4536_ == 0)
{
lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
v_isSharedCheck_4543_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4543_ == 0)
{
lean_object* v_unused_4544_; lean_object* v_unused_4545_; 
v_unused_4544_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4544_);
v_unused_4545_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4545_);
v___x_4538_ = v_code_4078_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_dec(v_code_4078_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 1, v_a_4519_);
lean_ctor_set(v___x_4538_, 0, v_decl_4079_);
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4542_, 1, v_a_4519_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
v_k_4091_ = v___x_4541_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
else
{
lean_dec(v_a_4519_);
lean_dec_ref(v_decl_4079_);
v_k_4091_ = v_code_4078_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
else
{
lean_object* v___x_4546_; lean_object* v___x_4547_; 
lean_dec_ref(v___x_4518_);
lean_dec_ref(v_decl_4079_);
lean_dec_ref(v_code_4078_);
v___x_4546_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4547_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4546_);
v_k_4091_ = v___x_4547_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
case 15:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; 
lean_dec_ref(v___x_4164_);
lean_dec_ref(v_decl_4079_);
lean_dec_ref(v_code_4078_);
v___x_4548_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12);
v___x_4549_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v___x_4548_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v___x_4549_, 1);
v_k_4091_ = v_a_4550_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
else
{
lean_dec_ref_known(v_value_4089_, 1);
lean_dec(v_fvarId_4088_);
return v___x_4549_;
}
}
default: 
{
if (lean_obj_tag(v_code_4078_) == 0)
{
lean_object* v_a_4551_; lean_object* v_decl_4552_; lean_object* v_k_4553_; size_t v___x_4554_; size_t v___x_4555_; uint8_t v___x_4556_; 
v_a_4551_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4551_);
lean_dec_ref(v___x_4164_);
v_decl_4552_ = lean_ctor_get(v_code_4078_, 0);
v_k_4553_ = lean_ctor_get(v_code_4078_, 1);
v___x_4554_ = lean_ptr_addr(v_k_4553_);
v___x_4555_ = lean_ptr_addr(v_a_4551_);
v___x_4556_ = lean_usize_dec_eq(v___x_4554_, v___x_4555_);
if (v___x_4556_ == 0)
{
lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
v_isSharedCheck_4563_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4563_ == 0)
{
lean_object* v_unused_4564_; lean_object* v_unused_4565_; 
v_unused_4564_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4564_);
v_unused_4565_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4565_);
v___x_4558_ = v_code_4078_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_dec(v_code_4078_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 1, v_a_4551_);
lean_ctor_set(v___x_4558_, 0, v_decl_4079_);
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4562_, 1, v_a_4551_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
v_k_4091_ = v___x_4561_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
else
{
size_t v___x_4566_; size_t v___x_4567_; uint8_t v___x_4568_; 
v___x_4566_ = lean_ptr_addr(v_decl_4552_);
v___x_4567_ = lean_ptr_addr(v_decl_4079_);
v___x_4568_ = lean_usize_dec_eq(v___x_4566_, v___x_4567_);
if (v___x_4568_ == 0)
{
lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
v_isSharedCheck_4575_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4575_ == 0)
{
lean_object* v_unused_4576_; lean_object* v_unused_4577_; 
v_unused_4576_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4576_);
v_unused_4577_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4577_);
v___x_4570_ = v_code_4078_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_dec(v_code_4078_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
lean_ctor_set(v___x_4570_, 1, v_a_4551_);
lean_ctor_set(v___x_4570_, 0, v_decl_4079_);
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4574_, 1, v_a_4551_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
v_k_4091_ = v___x_4573_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
else
{
lean_dec(v_a_4551_);
lean_dec_ref(v_decl_4079_);
v_k_4091_ = v_code_4078_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
else
{
lean_object* v___x_4578_; lean_object* v___x_4579_; 
lean_dec_ref(v___x_4164_);
lean_dec_ref(v_decl_4079_);
lean_dec_ref(v_code_4078_);
v___x_4578_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4579_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4578_);
v_k_4091_ = v___x_4579_;
v___y_4092_ = v_a_4081_;
v___y_4093_ = v_a_4082_;
v___y_4094_ = v_a_4083_;
v___y_4095_ = v_a_4084_;
v___y_4096_ = v_a_4085_;
v___y_4097_ = v_a_4086_;
goto v___jp_4090_;
}
}
}
v___jp_4090_:
{
lean_object* v___x_4098_; 
v___x_4098_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(v_value_4089_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4118_; 
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4118_ == 0)
{
lean_object* v_unused_4119_; 
v_unused_4119_ = lean_ctor_get(v___x_4098_, 0);
lean_dec(v_unused_4119_);
v___x_4100_ = v___x_4098_;
v_isShared_4101_ = v_isSharedCheck_4118_;
goto v_resetjp_4099_;
}
else
{
lean_dec(v___x_4098_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4118_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4102_; lean_object* v_vars_4103_; lean_object* v_borrows_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4117_; 
v___x_4102_ = lean_st_ref_take(v___y_4093_);
v_vars_4103_ = lean_ctor_get(v___x_4102_, 0);
v_borrows_4104_ = lean_ctor_get(v___x_4102_, 1);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4106_ = v___x_4102_;
v_isShared_4107_ = v_isSharedCheck_4117_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_borrows_4104_);
lean_inc(v_vars_4103_);
lean_dec(v___x_4102_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4117_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v_vars_4108_; lean_object* v_borrows_4109_; lean_object* v___x_4111_; 
v_vars_4108_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_vars_4103_, v_fvarId_4088_);
v_borrows_4109_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_borrows_4104_, v_fvarId_4088_);
lean_dec(v_fvarId_4088_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 1, v_borrows_4109_);
lean_ctor_set(v___x_4106_, 0, v_vars_4108_);
v___x_4111_ = v___x_4106_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_vars_4108_);
lean_ctor_set(v_reuseFailAlloc_4116_, 1, v_borrows_4109_);
v___x_4111_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4112_; lean_object* v___x_4114_; 
v___x_4112_ = lean_st_ref_put(v___y_4093_, v___x_4111_);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v_k_4091_);
v___x_4114_ = v___x_4100_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_k_4091_);
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
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_dec_ref(v_k_4091_);
lean_dec(v_fvarId_4088_);
v_a_4120_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4098_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4098_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
v___jp_4128_:
{
if (lean_obj_tag(v_code_4078_) == 0)
{
lean_object* v_decl_4136_; lean_object* v_k_4137_; size_t v___x_4138_; size_t v___x_4139_; uint8_t v___x_4140_; 
v_decl_4136_ = lean_ctor_get(v_code_4078_, 0);
v_k_4137_ = lean_ctor_get(v_code_4078_, 1);
v___x_4138_ = lean_ptr_addr(v_k_4137_);
v___x_4139_ = lean_ptr_addr(v_k_4129_);
v___x_4140_ = lean_usize_dec_eq(v___x_4138_, v___x_4139_);
if (v___x_4140_ == 0)
{
lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
v_isSharedCheck_4147_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4147_ == 0)
{
lean_object* v_unused_4148_; lean_object* v_unused_4149_; 
v_unused_4148_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4148_);
v_unused_4149_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4149_);
v___x_4142_ = v_code_4078_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_dec(v_code_4078_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
lean_ctor_set(v___x_4142_, 1, v_k_4129_);
lean_ctor_set(v___x_4142_, 0, v_decl_4079_);
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4146_, 1, v_k_4129_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
v_k_4091_ = v___x_4145_;
v___y_4092_ = v___y_4130_;
v___y_4093_ = v___y_4131_;
v___y_4094_ = v___y_4132_;
v___y_4095_ = v___y_4133_;
v___y_4096_ = v___y_4134_;
v___y_4097_ = v___y_4135_;
goto v___jp_4090_;
}
}
}
else
{
size_t v___x_4150_; size_t v___x_4151_; uint8_t v___x_4152_; 
v___x_4150_ = lean_ptr_addr(v_decl_4136_);
v___x_4151_ = lean_ptr_addr(v_decl_4079_);
v___x_4152_ = lean_usize_dec_eq(v___x_4150_, v___x_4151_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
v_isSharedCheck_4159_ = !lean_is_exclusive(v_code_4078_);
if (v_isSharedCheck_4159_ == 0)
{
lean_object* v_unused_4160_; lean_object* v_unused_4161_; 
v_unused_4160_ = lean_ctor_get(v_code_4078_, 1);
lean_dec(v_unused_4160_);
v_unused_4161_ = lean_ctor_get(v_code_4078_, 0);
lean_dec(v_unused_4161_);
v___x_4154_ = v_code_4078_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_dec(v_code_4078_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 1, v_k_4129_);
lean_ctor_set(v___x_4154_, 0, v_decl_4079_);
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_decl_4079_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v_k_4129_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
v_k_4091_ = v___x_4157_;
v___y_4092_ = v___y_4130_;
v___y_4093_ = v___y_4131_;
v___y_4094_ = v___y_4132_;
v___y_4095_ = v___y_4133_;
v___y_4096_ = v___y_4134_;
v___y_4097_ = v___y_4135_;
goto v___jp_4090_;
}
}
}
else
{
lean_dec_ref(v_k_4129_);
lean_dec_ref(v_decl_4079_);
v_k_4091_ = v_code_4078_;
v___y_4092_ = v___y_4130_;
v___y_4093_ = v___y_4131_;
v___y_4094_ = v___y_4132_;
v___y_4095_ = v___y_4133_;
v___y_4096_ = v___y_4134_;
v___y_4097_ = v___y_4135_;
goto v___jp_4090_;
}
}
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
lean_dec_ref(v_k_4129_);
lean_dec_ref(v_decl_4079_);
lean_dec_ref(v_code_4078_);
v___x_4162_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4163_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4162_);
v_k_4091_ = v___x_4163_;
v___y_4092_ = v___y_4130_;
v___y_4093_ = v___y_4131_;
v___y_4094_ = v___y_4132_;
v___y_4095_ = v___y_4133_;
v___y_4096_ = v___y_4134_;
v___y_4097_ = v___y_4135_;
goto v___jp_4090_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___boxed(lean_object* v_code_4580_, lean_object* v_decl_4581_, lean_object* v_k_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(v_code_4580_, v_decl_4581_, v_k_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_);
lean_dec(v_a_4588_);
lean_dec_ref(v_a_4587_);
lean_dec(v_a_4586_);
lean_dec_ref(v_a_4585_);
lean_dec(v_a_4584_);
lean_dec_ref(v_a_4583_);
return v_res_4590_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0(void){
_start:
{
lean_object* v___x_4591_; 
v___x_4591_ = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___redArg();
return v___x_4591_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5(lean_object* v_msg_4592_){
_start:
{
lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4593_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0);
v___x_4594_ = lean_panic_fn_borrowed(v___x_4593_, v_msg_4592_);
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(lean_object* v_a_4595_, lean_object* v_b_4596_, lean_object* v_x_4597_){
_start:
{
if (lean_obj_tag(v_x_4597_) == 0)
{
lean_dec(v_b_4596_);
lean_dec(v_a_4595_);
return v_x_4597_;
}
else
{
lean_object* v_key_4598_; lean_object* v_value_4599_; lean_object* v_tail_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4612_; 
v_key_4598_ = lean_ctor_get(v_x_4597_, 0);
v_value_4599_ = lean_ctor_get(v_x_4597_, 1);
v_tail_4600_ = lean_ctor_get(v_x_4597_, 2);
v_isSharedCheck_4612_ = !lean_is_exclusive(v_x_4597_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4602_ = v_x_4597_;
v_isShared_4603_ = v_isSharedCheck_4612_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_tail_4600_);
lean_inc(v_value_4599_);
lean_inc(v_key_4598_);
lean_dec(v_x_4597_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4612_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
uint8_t v___x_4604_; 
v___x_4604_ = l_Lean_instBEqFVarId_beq(v_key_4598_, v_a_4595_);
if (v___x_4604_ == 0)
{
lean_object* v___x_4605_; lean_object* v___x_4607_; 
v___x_4605_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(v_a_4595_, v_b_4596_, v_tail_4600_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 2, v___x_4605_);
v___x_4607_ = v___x_4602_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_key_4598_);
lean_ctor_set(v_reuseFailAlloc_4608_, 1, v_value_4599_);
lean_ctor_set(v_reuseFailAlloc_4608_, 2, v___x_4605_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
else
{
lean_object* v___x_4610_; 
lean_dec(v_value_4599_);
lean_dec(v_key_4598_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 1, v_b_4596_);
lean_ctor_set(v___x_4602_, 0, v_a_4595_);
v___x_4610_ = v___x_4602_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4595_);
lean_ctor_set(v_reuseFailAlloc_4611_, 1, v_b_4596_);
lean_ctor_set(v_reuseFailAlloc_4611_, 2, v_tail_4600_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(lean_object* v_m_4613_, lean_object* v_a_4614_, lean_object* v_b_4615_){
_start:
{
lean_object* v_size_4616_; lean_object* v_buckets_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4660_; 
v_size_4616_ = lean_ctor_get(v_m_4613_, 0);
v_buckets_4617_ = lean_ctor_get(v_m_4613_, 1);
v_isSharedCheck_4660_ = !lean_is_exclusive(v_m_4613_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4619_ = v_m_4613_;
v_isShared_4620_ = v_isSharedCheck_4660_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_buckets_4617_);
lean_inc(v_size_4616_);
lean_dec(v_m_4613_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4660_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4621_; uint64_t v___x_4622_; uint64_t v___x_4623_; uint64_t v___x_4624_; uint64_t v_fold_4625_; uint64_t v___x_4626_; uint64_t v___x_4627_; uint64_t v___x_4628_; size_t v___x_4629_; size_t v___x_4630_; size_t v___x_4631_; size_t v___x_4632_; size_t v___x_4633_; lean_object* v_bkt_4634_; uint8_t v___x_4635_; 
v___x_4621_ = lean_array_get_size(v_buckets_4617_);
v___x_4622_ = l_Lean_instHashableFVarId_hash(v_a_4614_);
v___x_4623_ = 32ULL;
v___x_4624_ = lean_uint64_shift_right(v___x_4622_, v___x_4623_);
v_fold_4625_ = lean_uint64_xor(v___x_4622_, v___x_4624_);
v___x_4626_ = 16ULL;
v___x_4627_ = lean_uint64_shift_right(v_fold_4625_, v___x_4626_);
v___x_4628_ = lean_uint64_xor(v_fold_4625_, v___x_4627_);
v___x_4629_ = lean_uint64_to_usize(v___x_4628_);
v___x_4630_ = lean_usize_of_nat(v___x_4621_);
v___x_4631_ = ((size_t)1ULL);
v___x_4632_ = lean_usize_sub(v___x_4630_, v___x_4631_);
v___x_4633_ = lean_usize_land(v___x_4629_, v___x_4632_);
v_bkt_4634_ = lean_array_uget_borrowed(v_buckets_4617_, v___x_4633_);
v___x_4635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_4614_, v_bkt_4634_);
if (v___x_4635_ == 0)
{
lean_object* v___x_4636_; lean_object* v_size_x27_4637_; lean_object* v___x_4638_; lean_object* v_buckets_x27_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; 
v___x_4636_ = lean_unsigned_to_nat(1u);
v_size_x27_4637_ = lean_nat_add(v_size_4616_, v___x_4636_);
lean_dec(v_size_4616_);
lean_inc(v_bkt_4634_);
v___x_4638_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4638_, 0, v_a_4614_);
lean_ctor_set(v___x_4638_, 1, v_b_4615_);
lean_ctor_set(v___x_4638_, 2, v_bkt_4634_);
v_buckets_x27_4639_ = lean_array_uset(v_buckets_4617_, v___x_4633_, v___x_4638_);
v___x_4640_ = lean_unsigned_to_nat(4u);
v___x_4641_ = lean_nat_mul(v_size_x27_4637_, v___x_4640_);
v___x_4642_ = lean_unsigned_to_nat(3u);
v___x_4643_ = lean_nat_div(v___x_4641_, v___x_4642_);
lean_dec(v___x_4641_);
v___x_4644_ = lean_array_get_size(v_buckets_x27_4639_);
v___x_4645_ = lean_nat_dec_le(v___x_4643_, v___x_4644_);
lean_dec(v___x_4643_);
if (v___x_4645_ == 0)
{
lean_object* v_val_4646_; lean_object* v___x_4648_; 
v_val_4646_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(v_buckets_x27_4639_);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 1, v_val_4646_);
lean_ctor_set(v___x_4619_, 0, v_size_x27_4637_);
v___x_4648_ = v___x_4619_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_size_x27_4637_);
lean_ctor_set(v_reuseFailAlloc_4649_, 1, v_val_4646_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
else
{
lean_object* v___x_4651_; 
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 1, v_buckets_x27_4639_);
lean_ctor_set(v___x_4619_, 0, v_size_x27_4637_);
v___x_4651_ = v___x_4619_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_size_x27_4637_);
lean_ctor_set(v_reuseFailAlloc_4652_, 1, v_buckets_x27_4639_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
else
{
lean_object* v___x_4653_; lean_object* v_buckets_x27_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4658_; 
lean_inc(v_bkt_4634_);
v___x_4653_ = lean_box(0);
v_buckets_x27_4654_ = lean_array_uset(v_buckets_4617_, v___x_4633_, v___x_4653_);
v___x_4655_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(v_a_4614_, v_b_4615_, v_bkt_4634_);
v___x_4656_ = lean_array_uset(v_buckets_x27_4654_, v___x_4633_, v___x_4655_);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 1, v___x_4656_);
v___x_4658_ = v___x_4619_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_size_4616_);
lean_ctor_set(v_reuseFailAlloc_4659_, 1, v___x_4656_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__2(lean_object* v_a_4661_, lean_object* v_a_4662_){
_start:
{
if (lean_obj_tag(v_a_4661_) == 0)
{
lean_object* v___x_4663_; 
v___x_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4663_, 0, v_a_4662_);
return v___x_4663_;
}
else
{
lean_object* v_key_4664_; lean_object* v_value_4665_; lean_object* v_tail_4666_; lean_object* v_r_4667_; 
v_key_4664_ = lean_ctor_get(v_a_4661_, 0);
lean_inc(v_key_4664_);
v_value_4665_ = lean_ctor_get(v_a_4661_, 1);
lean_inc(v_value_4665_);
v_tail_4666_ = lean_ctor_get(v_a_4661_, 2);
lean_inc(v_tail_4666_);
lean_dec_ref_known(v_a_4661_, 3);
v_r_4667_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(v_a_4662_, v_key_4664_, v_value_4665_);
v_a_4661_ = v_tail_4666_;
v_a_4662_ = v_r_4667_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(lean_object* v_as_4669_, size_t v_sz_4670_, size_t v_i_4671_, lean_object* v_b_4672_){
_start:
{
uint8_t v___x_4673_; 
v___x_4673_ = lean_usize_dec_lt(v_i_4671_, v_sz_4670_);
if (v___x_4673_ == 0)
{
return v_b_4672_;
}
else
{
lean_object* v_a_4674_; lean_object* v___x_4675_; 
v_a_4674_ = lean_array_uget_borrowed(v_as_4669_, v_i_4671_);
lean_inc(v_a_4674_);
v___x_4675_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__2(v_a_4674_, v_b_4672_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
lean_inc(v_a_4676_);
lean_dec_ref_known(v___x_4675_, 1);
return v_a_4676_;
}
else
{
lean_object* v_a_4677_; size_t v___x_4678_; size_t v___x_4679_; 
v_a_4677_ = lean_ctor_get(v___x_4675_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v___x_4675_, 1);
v___x_4678_ = ((size_t)1ULL);
v___x_4679_ = lean_usize_add(v_i_4671_, v___x_4678_);
v_i_4671_ = v___x_4679_;
v_b_4672_ = v_a_4677_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3___boxed(lean_object* v_as_4681_, lean_object* v_sz_4682_, lean_object* v_i_4683_, lean_object* v_b_4684_){
_start:
{
size_t v_sz_boxed_4685_; size_t v_i_boxed_4686_; lean_object* v_res_4687_; 
v_sz_boxed_4685_ = lean_unbox_usize(v_sz_4682_);
lean_dec(v_sz_4682_);
v_i_boxed_4686_ = lean_unbox_usize(v_i_4683_);
lean_dec(v_i_4683_);
v_res_4687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(v_as_4681_, v_sz_boxed_4685_, v_i_boxed_4686_, v_b_4684_);
lean_dec_ref(v_as_4681_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(lean_object* v_m_4688_, lean_object* v_l_4689_){
_start:
{
lean_object* v_buckets_4690_; size_t v_sz_4691_; size_t v___x_4692_; lean_object* v___x_4693_; 
v_buckets_4690_ = lean_ctor_get(v_l_4689_, 1);
v_sz_4691_ = lean_array_size(v_buckets_4690_);
v___x_4692_ = ((size_t)0ULL);
v___x_4693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(v_buckets_4690_, v_sz_4691_, v___x_4692_, v_m_4688_);
return v___x_4693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1___boxed(lean_object* v_m_4694_, lean_object* v_l_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_m_4694_, v_l_4695_);
lean_dec_ref(v_l_4695_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(lean_object* v_a_4697_, lean_object* v_a_4698_){
_start:
{
if (lean_obj_tag(v_a_4697_) == 0)
{
lean_object* v___x_4699_; 
v___x_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4699_, 0, v_a_4698_);
return v___x_4699_;
}
else
{
lean_object* v_key_4700_; lean_object* v_value_4701_; lean_object* v_tail_4702_; lean_object* v_r_4703_; 
v_key_4700_ = lean_ctor_get(v_a_4697_, 0);
lean_inc(v_key_4700_);
v_value_4701_ = lean_ctor_get(v_a_4697_, 1);
lean_inc(v_value_4701_);
v_tail_4702_ = lean_ctor_get(v_a_4697_, 2);
lean_inc(v_tail_4702_);
lean_dec_ref_known(v_a_4697_, 3);
v_r_4703_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_a_4698_, v_key_4700_, v_value_4701_);
v_a_4697_ = v_tail_4702_;
v_a_4698_ = v_r_4703_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(lean_object* v_as_4705_, size_t v_sz_4706_, size_t v_i_4707_, lean_object* v_b_4708_){
_start:
{
uint8_t v___x_4709_; 
v___x_4709_ = lean_usize_dec_lt(v_i_4707_, v_sz_4706_);
if (v___x_4709_ == 0)
{
return v_b_4708_;
}
else
{
lean_object* v_a_4710_; lean_object* v___x_4711_; 
v_a_4710_ = lean_array_uget_borrowed(v_as_4705_, v_i_4707_);
lean_inc(v_a_4710_);
v___x_4711_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(v_a_4710_, v_b_4708_);
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_object* v_a_4712_; 
v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
lean_inc(v_a_4712_);
lean_dec_ref_known(v___x_4711_, 1);
return v_a_4712_;
}
else
{
lean_object* v_a_4713_; size_t v___x_4714_; size_t v___x_4715_; 
v_a_4713_ = lean_ctor_get(v___x_4711_, 0);
lean_inc(v_a_4713_);
lean_dec_ref_known(v___x_4711_, 1);
v___x_4714_ = ((size_t)1ULL);
v___x_4715_ = lean_usize_add(v_i_4707_, v___x_4714_);
v_i_4707_ = v___x_4715_;
v_b_4708_ = v_a_4713_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2___boxed(lean_object* v_as_4717_, lean_object* v_sz_4718_, lean_object* v_i_4719_, lean_object* v_b_4720_){
_start:
{
size_t v_sz_boxed_4721_; size_t v_i_boxed_4722_; lean_object* v_res_4723_; 
v_sz_boxed_4721_ = lean_unbox_usize(v_sz_4718_);
lean_dec(v_sz_4718_);
v_i_boxed_4722_ = lean_unbox_usize(v_i_4719_);
lean_dec(v_i_4719_);
v_res_4723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_as_4717_, v_sz_boxed_4721_, v_i_boxed_4722_, v_b_4720_);
lean_dec_ref(v_as_4717_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(lean_object* v_as_4724_, size_t v_i_4725_, size_t v_stop_4726_, lean_object* v_b_4727_){
_start:
{
lean_object* v___y_4729_; lean_object* v___y_4730_; uint8_t v___x_4735_; 
v___x_4735_ = lean_usize_dec_eq(v_i_4725_, v_stop_4726_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; lean_object* v_snd_4737_; lean_object* v_vars_4738_; lean_object* v_borrows_4739_; lean_object* v_vars_4740_; lean_object* v_borrows_4741_; lean_object* v___y_4743_; lean_object* v_size_4752_; lean_object* v_buckets_4753_; lean_object* v_size_4754_; uint8_t v___x_4755_; 
v___x_4736_ = lean_array_uget_borrowed(v_as_4724_, v_i_4725_);
v_snd_4737_ = lean_ctor_get(v___x_4736_, 1);
v_vars_4738_ = lean_ctor_get(v_b_4727_, 0);
lean_inc_ref(v_vars_4738_);
v_borrows_4739_ = lean_ctor_get(v_b_4727_, 1);
lean_inc_ref(v_borrows_4739_);
lean_dec_ref(v_b_4727_);
v_vars_4740_ = lean_ctor_get(v_snd_4737_, 0);
v_borrows_4741_ = lean_ctor_get(v_snd_4737_, 1);
v_size_4752_ = lean_ctor_get(v_vars_4738_, 0);
v_buckets_4753_ = lean_ctor_get(v_vars_4738_, 1);
v_size_4754_ = lean_ctor_get(v_vars_4740_, 0);
v___x_4755_ = lean_nat_dec_le(v_size_4752_, v_size_4754_);
if (v___x_4755_ == 0)
{
lean_object* v___x_4756_; 
v___x_4756_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_vars_4738_, v_vars_4740_);
v___y_4743_ = v___x_4756_;
goto v___jp_4742_;
}
else
{
size_t v_sz_4757_; size_t v___x_4758_; lean_object* v___x_4759_; 
lean_inc_ref(v_buckets_4753_);
lean_dec_ref(v_vars_4738_);
v_sz_4757_ = lean_array_size(v_buckets_4753_);
v___x_4758_ = ((size_t)0ULL);
lean_inc_ref(v_vars_4740_);
v___x_4759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_buckets_4753_, v_sz_4757_, v___x_4758_, v_vars_4740_);
lean_dec_ref(v_buckets_4753_);
v___y_4743_ = v___x_4759_;
goto v___jp_4742_;
}
v___jp_4742_:
{
lean_object* v_size_4744_; lean_object* v_buckets_4745_; lean_object* v_size_4746_; uint8_t v___x_4747_; 
v_size_4744_ = lean_ctor_get(v_borrows_4739_, 0);
v_buckets_4745_ = lean_ctor_get(v_borrows_4739_, 1);
v_size_4746_ = lean_ctor_get(v_borrows_4741_, 0);
v___x_4747_ = lean_nat_dec_le(v_size_4744_, v_size_4746_);
if (v___x_4747_ == 0)
{
lean_object* v___x_4748_; 
v___x_4748_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_borrows_4739_, v_borrows_4741_);
v___y_4729_ = v___y_4743_;
v___y_4730_ = v___x_4748_;
goto v___jp_4728_;
}
else
{
size_t v_sz_4749_; size_t v___x_4750_; lean_object* v___x_4751_; 
lean_inc_ref(v_buckets_4745_);
lean_dec_ref(v_borrows_4739_);
v_sz_4749_ = lean_array_size(v_buckets_4745_);
v___x_4750_ = ((size_t)0ULL);
lean_inc_ref(v_borrows_4741_);
v___x_4751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_buckets_4745_, v_sz_4749_, v___x_4750_, v_borrows_4741_);
lean_dec_ref(v_buckets_4745_);
v___y_4729_ = v___y_4743_;
v___y_4730_ = v___x_4751_;
goto v___jp_4728_;
}
}
}
else
{
return v_b_4727_;
}
v___jp_4728_:
{
lean_object* v___x_4731_; size_t v___x_4732_; size_t v___x_4733_; 
v___x_4731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4731_, 0, v___y_4729_);
lean_ctor_set(v___x_4731_, 1, v___y_4730_);
v___x_4732_ = ((size_t)1ULL);
v___x_4733_ = lean_usize_add(v_i_4725_, v___x_4732_);
v_i_4725_ = v___x_4733_;
v_b_4727_ = v___x_4731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8___boxed(lean_object* v_as_4760_, lean_object* v_i_4761_, lean_object* v_stop_4762_, lean_object* v_b_4763_){
_start:
{
size_t v_i_boxed_4764_; size_t v_stop_boxed_4765_; lean_object* v_res_4766_; 
v_i_boxed_4764_ = lean_unbox_usize(v_i_4761_);
lean_dec(v_i_4761_);
v_stop_boxed_4765_ = lean_unbox_usize(v_stop_4762_);
lean_dec(v_stop_4762_);
v_res_4766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_as_4760_, v_i_boxed_4764_, v_stop_boxed_4765_, v_b_4763_);
lean_dec_ref(v_as_4760_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(lean_object* v_as_4767_, size_t v_i_4768_, size_t v_stop_4769_, lean_object* v_b_4770_){
_start:
{
lean_object* v___y_4772_; uint8_t v___x_4776_; 
v___x_4776_ = lean_usize_dec_eq(v_i_4768_, v_stop_4769_);
if (v___x_4776_ == 0)
{
lean_object* v_resetTargets_4777_; lean_object* v_unconditionalBorrows_4778_; lean_object* v_derivedValMap_4779_; lean_object* v_varMap_4780_; lean_object* v_jpLiveVarMap_4781_; lean_object* v_idx_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4803_; 
v_resetTargets_4777_ = lean_ctor_get(v_b_4770_, 0);
v_unconditionalBorrows_4778_ = lean_ctor_get(v_b_4770_, 1);
v_derivedValMap_4779_ = lean_ctor_get(v_b_4770_, 2);
v_varMap_4780_ = lean_ctor_get(v_b_4770_, 3);
v_jpLiveVarMap_4781_ = lean_ctor_get(v_b_4770_, 4);
v_idx_4782_ = lean_ctor_get(v_b_4770_, 5);
v_isSharedCheck_4803_ = !lean_is_exclusive(v_b_4770_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4784_ = v_b_4770_;
v_isShared_4785_ = v_isSharedCheck_4803_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_idx_4782_);
lean_inc(v_jpLiveVarMap_4781_);
lean_inc(v_varMap_4780_);
lean_inc(v_derivedValMap_4779_);
lean_inc(v_unconditionalBorrows_4778_);
lean_inc(v_resetTargets_4777_);
lean_dec(v_b_4770_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4803_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4786_; lean_object* v_fvarId_4787_; lean_object* v_type_4788_; uint8_t v_borrow_4789_; uint8_t v___x_4790_; uint8_t v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v_varMap_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v_ctx_4798_; 
v___x_4786_ = lean_array_uget_borrowed(v_as_4767_, v_i_4768_);
v_fvarId_4787_ = lean_ctor_get(v___x_4786_, 0);
v_type_4788_ = lean_ctor_get(v___x_4786_, 2);
v_borrow_4789_ = lean_ctor_get_uint8(v___x_4786_, sizeof(void*)*3);
v___x_4790_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_4788_);
v___x_4791_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_4788_);
v___x_4792_ = lean_box(0);
lean_inc(v_idx_4782_);
v___x_4793_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4793_, 0, v_idx_4782_);
lean_ctor_set(v___x_4793_, 1, v___x_4792_);
lean_ctor_set_uint8(v___x_4793_, sizeof(void*)*2, v___x_4790_);
lean_ctor_set_uint8(v___x_4793_, sizeof(void*)*2 + 1, v___x_4791_);
lean_ctor_set_uint8(v___x_4793_, sizeof(void*)*2 + 2, v___x_4776_);
lean_inc(v_fvarId_4787_);
v_varMap_4794_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_4787_, v___x_4793_, v_varMap_4780_);
v___x_4795_ = lean_unsigned_to_nat(1u);
v___x_4796_ = lean_nat_add(v_idx_4782_, v___x_4795_);
lean_dec(v_idx_4782_);
if (v_isShared_4785_ == 0)
{
lean_ctor_set(v___x_4784_, 5, v___x_4796_);
lean_ctor_set(v___x_4784_, 3, v_varMap_4794_);
v_ctx_4798_ = v___x_4784_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_resetTargets_4777_);
lean_ctor_set(v_reuseFailAlloc_4802_, 1, v_unconditionalBorrows_4778_);
lean_ctor_set(v_reuseFailAlloc_4802_, 2, v_derivedValMap_4779_);
lean_ctor_set(v_reuseFailAlloc_4802_, 3, v_varMap_4794_);
lean_ctor_set(v_reuseFailAlloc_4802_, 4, v_jpLiveVarMap_4781_);
lean_ctor_set(v_reuseFailAlloc_4802_, 5, v___x_4796_);
v_ctx_4798_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
lean_object* v___x_4799_; lean_object* v_ctx_4800_; 
v___x_4799_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
lean_inc(v_fvarId_4787_);
v_ctx_4800_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_4798_, v___x_4799_, v_fvarId_4787_);
if (v_borrow_4789_ == 0)
{
v___y_4772_ = v_ctx_4800_;
goto v___jp_4771_;
}
else
{
if (v___x_4790_ == 0)
{
v___y_4772_ = v_ctx_4800_;
goto v___jp_4771_;
}
else
{
lean_object* v___x_4801_; 
lean_inc(v_fvarId_4787_);
v___x_4801_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(v_ctx_4800_, v_fvarId_4787_);
v___y_4772_ = v___x_4801_;
goto v___jp_4771_;
}
}
}
}
}
else
{
return v_b_4770_;
}
v___jp_4771_:
{
size_t v___x_4773_; size_t v___x_4774_; 
v___x_4773_ = ((size_t)1ULL);
v___x_4774_ = lean_usize_add(v_i_4768_, v___x_4773_);
v_i_4768_ = v___x_4774_;
v_b_4770_ = v___y_4772_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3___boxed(lean_object* v_as_4804_, lean_object* v_i_4805_, lean_object* v_stop_4806_, lean_object* v_b_4807_){
_start:
{
size_t v_i_boxed_4808_; size_t v_stop_boxed_4809_; lean_object* v_res_4810_; 
v_i_boxed_4808_ = lean_unbox_usize(v_i_4805_);
lean_dec(v_i_4805_);
v_stop_boxed_4809_ = lean_unbox_usize(v_stop_4806_);
lean_dec(v_stop_4806_);
v_res_4810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_as_4804_, v_i_boxed_4808_, v_stop_boxed_4809_, v_b_4807_);
lean_dec_ref(v_as_4804_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4_spec__7(lean_object* v_msg_4811_){
_start:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4812_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
v___x_4813_ = lean_panic_fn_borrowed(v___x_4812_, v_msg_4811_);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(lean_object* v_t_4814_, lean_object* v_k_4815_){
_start:
{
if (lean_obj_tag(v_t_4814_) == 0)
{
lean_object* v_k_4816_; lean_object* v_v_4817_; lean_object* v_l_4818_; lean_object* v_r_4819_; uint8_t v___x_4820_; 
v_k_4816_ = lean_ctor_get(v_t_4814_, 1);
v_v_4817_ = lean_ctor_get(v_t_4814_, 2);
v_l_4818_ = lean_ctor_get(v_t_4814_, 3);
v_r_4819_ = lean_ctor_get(v_t_4814_, 4);
v___x_4820_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4815_, v_k_4816_);
switch(v___x_4820_)
{
case 0:
{
v_t_4814_ = v_l_4818_;
goto _start;
}
case 1:
{
lean_inc(v_v_4817_);
return v_v_4817_;
}
default: 
{
v_t_4814_ = v_r_4819_;
goto _start;
}
}
}
else
{
lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4823_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3);
v___x_4824_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4_spec__7(v___x_4823_);
return v___x_4824_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4___boxed(lean_object* v_t_4825_, lean_object* v_k_4826_){
_start:
{
lean_object* v_res_4827_; 
v_res_4827_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(v_t_4825_, v_k_4826_);
lean_dec(v_k_4826_);
lean_dec(v_t_4825_);
return v_res_4827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(lean_object* v_discr_4828_, size_t v_sz_4829_, size_t v_i_4830_, lean_object* v_bs_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_){
_start:
{
uint8_t v___x_4839_; 
v___x_4839_ = lean_usize_dec_lt(v_i_4830_, v_sz_4829_);
if (v___x_4839_ == 0)
{
lean_object* v___x_4840_; 
lean_dec(v_discr_4828_);
v___x_4840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4840_, 0, v_bs_4831_);
return v___x_4840_;
}
else
{
lean_object* v_v_4841_; lean_object* v_fst_4842_; lean_object* v_snd_4843_; lean_object* v___x_4844_; lean_object* v_bs_x27_4845_; lean_object* v_a_4847_; 
v_v_4841_ = lean_array_uget_borrowed(v_bs_4831_, v_i_4830_);
v_fst_4842_ = lean_ctor_get(v_v_4841_, 0);
lean_inc(v_fst_4842_);
v_snd_4843_ = lean_ctor_get(v_v_4841_, 1);
lean_inc(v_snd_4843_);
v___x_4844_ = lean_unsigned_to_nat(0u);
v_bs_x27_4845_ = lean_array_uset(v_bs_4831_, v_i_4830_, v___x_4844_);
if (lean_obj_tag(v_fst_4842_) == 1)
{
lean_object* v_info_4852_; lean_object* v_code_4853_; lean_object* v_resetTargets_4854_; lean_object* v_unconditionalBorrows_4855_; lean_object* v_derivedValMap_4856_; lean_object* v_varMap_4857_; lean_object* v_jpLiveVarMap_4858_; lean_object* v_idx_4859_; lean_object* v___y_4861_; lean_object* v___x_4876_; 
v_info_4852_ = lean_ctor_get(v_fst_4842_, 0);
v_code_4853_ = lean_ctor_get(v_fst_4842_, 1);
v_resetTargets_4854_ = lean_ctor_get(v___y_4832_, 0);
v_unconditionalBorrows_4855_ = lean_ctor_get(v___y_4832_, 1);
v_derivedValMap_4856_ = lean_ctor_get(v___y_4832_, 2);
v_varMap_4857_ = lean_ctor_get(v___y_4832_, 3);
v_jpLiveVarMap_4858_ = lean_ctor_get(v___y_4832_, 4);
v_idx_4859_ = lean_ctor_get(v___y_4832_, 5);
v___x_4876_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_varMap_4857_, v_discr_4828_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_inc(v_varMap_4857_);
v___y_4861_ = v_varMap_4857_;
goto v___jp_4860_;
}
else
{
lean_object* v_val_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4898_; 
v_val_4877_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4879_ = v___x_4876_;
v_isShared_4880_ = v_isSharedCheck_4898_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_val_4877_);
lean_dec(v___x_4876_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4898_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
uint8_t v_persistent_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4895_; 
v_persistent_4881_ = lean_ctor_get_uint8(v_val_4877_, sizeof(void*)*2 + 2);
v_isSharedCheck_4895_ = !lean_is_exclusive(v_val_4877_);
if (v_isSharedCheck_4895_ == 0)
{
lean_object* v_unused_4896_; lean_object* v_unused_4897_; 
v_unused_4896_ = lean_ctor_get(v_val_4877_, 1);
lean_dec(v_unused_4896_);
v_unused_4897_ = lean_ctor_get(v_val_4877_, 0);
lean_dec(v_unused_4897_);
v___x_4883_ = v_val_4877_;
v_isShared_4884_ = v_isSharedCheck_4895_;
goto v_resetjp_4882_;
}
else
{
lean_dec(v_val_4877_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4895_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
uint8_t v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4889_; 
v___x_4885_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_info_4852_);
v___x_4886_ = lean_unsigned_to_nat(1u);
v___x_4887_ = lean_nat_add(v_idx_4859_, v___x_4886_);
lean_inc_ref(v_info_4852_);
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 0, v_info_4852_);
v___x_4889_ = v___x_4879_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_info_4852_);
v___x_4889_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
lean_object* v___x_4891_; 
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 1, v___x_4889_);
lean_ctor_set(v___x_4883_, 0, v___x_4887_);
v___x_4891_ = v___x_4883_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4887_);
lean_ctor_set(v_reuseFailAlloc_4893_, 1, v___x_4889_);
lean_ctor_set_uint8(v_reuseFailAlloc_4893_, sizeof(void*)*2 + 2, v_persistent_4881_);
v___x_4891_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
lean_object* v___x_4892_; 
lean_ctor_set_uint8(v___x_4891_, sizeof(void*)*2, v___x_4885_);
lean_ctor_set_uint8(v___x_4891_, sizeof(void*)*2 + 1, v___x_4885_);
lean_inc(v_varMap_4857_);
lean_inc(v_discr_4828_);
v___x_4892_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_4828_, v___x_4891_, v_varMap_4857_);
v___y_4861_ = v___x_4892_;
goto v___jp_4860_;
}
}
}
}
}
v___jp_4860_:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4862_ = lean_unsigned_to_nat(1u);
v___x_4863_ = lean_nat_add(v_idx_4859_, v___x_4862_);
lean_inc(v_jpLiveVarMap_4858_);
lean_inc(v_derivedValMap_4856_);
lean_inc(v_unconditionalBorrows_4855_);
lean_inc_ref(v_resetTargets_4854_);
v___x_4864_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4864_, 0, v_resetTargets_4854_);
lean_ctor_set(v___x_4864_, 1, v_unconditionalBorrows_4855_);
lean_ctor_set(v___x_4864_, 2, v_derivedValMap_4856_);
lean_ctor_set(v___x_4864_, 3, v___y_4861_);
lean_ctor_set(v___x_4864_, 4, v_jpLiveVarMap_4858_);
lean_ctor_set(v___x_4864_, 5, v___x_4863_);
lean_inc_ref(v_code_4853_);
v___x_4865_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_snd_4843_, v_code_4853_, v___x_4864_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
lean_dec_ref_known(v___x_4864_, 6);
lean_dec(v_snd_4843_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_object* v_a_4866_; lean_object* v___x_4867_; 
v_a_4866_ = lean_ctor_get(v___x_4865_, 0);
lean_inc(v_a_4866_);
lean_dec_ref_known(v___x_4865_, 1);
v___x_4867_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_fst_4842_, v_a_4866_);
v_a_4847_ = v___x_4867_;
goto v___jp_4846_;
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
lean_dec_ref_known(v_fst_4842_, 2);
lean_dec_ref(v_bs_x27_4845_);
lean_dec(v_discr_4828_);
v_a_4868_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4865_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4865_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4873_; 
if (v_isShared_4871_ == 0)
{
v___x_4873_ = v___x_4870_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4868_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
}
else
{
lean_object* v_code_4899_; lean_object* v___x_4900_; 
v_code_4899_ = lean_ctor_get(v_fst_4842_, 0);
lean_inc_ref(v_code_4899_);
v___x_4900_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_snd_4843_, v_code_4899_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
lean_dec(v_snd_4843_);
if (lean_obj_tag(v___x_4900_) == 0)
{
lean_object* v_a_4901_; lean_object* v___x_4902_; 
v_a_4901_ = lean_ctor_get(v___x_4900_, 0);
lean_inc(v_a_4901_);
lean_dec_ref_known(v___x_4900_, 1);
v___x_4902_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_fst_4842_, v_a_4901_);
v_a_4847_ = v___x_4902_;
goto v___jp_4846_;
}
else
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
lean_dec_ref_known(v_fst_4842_, 1);
lean_dec_ref(v_bs_x27_4845_);
lean_dec(v_discr_4828_);
v_a_4903_ = lean_ctor_get(v___x_4900_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4900_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4905_ = v___x_4900_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4900_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4906_ == 0)
{
v___x_4908_ = v___x_4905_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4903_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
}
v___jp_4846_:
{
size_t v___x_4848_; size_t v___x_4849_; lean_object* v___x_4850_; 
v___x_4848_ = ((size_t)1ULL);
v___x_4849_ = lean_usize_add(v_i_4830_, v___x_4848_);
v___x_4850_ = lean_array_uset(v_bs_x27_4845_, v_i_4830_, v_a_4847_);
v_i_4830_ = v___x_4849_;
v_bs_4831_ = v___x_4850_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7___boxed(lean_object* v_discr_4911_, lean_object* v_sz_4912_, lean_object* v_i_4913_, lean_object* v_bs_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_){
_start:
{
size_t v_sz_boxed_4922_; size_t v_i_boxed_4923_; lean_object* v_res_4924_; 
v_sz_boxed_4922_ = lean_unbox_usize(v_sz_4912_);
lean_dec(v_sz_4912_);
v_i_boxed_4923_ = lean_unbox_usize(v_i_4913_);
lean_dec(v_i_4913_);
v_res_4924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(v_discr_4911_, v_sz_boxed_4922_, v_i_boxed_4923_, v_bs_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
lean_dec(v___y_4920_);
lean_dec_ref(v___y_4919_);
lean_dec(v___y_4918_);
lean_dec_ref(v___y_4917_);
lean_dec(v___y_4916_);
lean_dec_ref(v___y_4915_);
return v_res_4924_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1(void){
_start:
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
v___x_4926_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_4927_ = lean_unsigned_to_nat(59u);
v___x_4928_ = lean_unsigned_to_nat(655u);
v___x_4929_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__0));
v___x_4930_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_4931_ = l_mkPanicMessageWithDecl(v___x_4930_, v___x_4929_, v___x_4928_, v___x_4927_, v___x_4926_);
return v___x_4931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(lean_object* v_code_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_){
_start:
{
switch(lean_obj_tag(v_code_4932_))
{
case 0:
{
lean_object* v_decl_4940_; lean_object* v_k_4941_; lean_object* v_fvarId_4942_; lean_object* v_type_4943_; lean_object* v_value_4944_; lean_object* v___y_4946_; 
v_decl_4940_ = lean_ctor_get(v_code_4932_, 0);
lean_inc_ref(v_decl_4940_);
v_k_4941_ = lean_ctor_get(v_code_4932_, 1);
v_fvarId_4942_ = lean_ctor_get(v_decl_4940_, 0);
v_type_4943_ = lean_ctor_get(v_decl_4940_, 2);
v_value_4944_ = lean_ctor_get(v_decl_4940_, 3);
if (lean_obj_tag(v_value_4944_) == 5)
{
lean_object* v_i_4965_; lean_object* v___x_4966_; 
v_i_4965_ = lean_ctor_get(v_value_4944_, 0);
lean_inc_ref(v_i_4965_);
v___x_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4966_, 0, v_i_4965_);
v___y_4946_ = v___x_4966_;
goto v___jp_4945_;
}
else
{
lean_object* v___x_4967_; 
v___x_4967_ = lean_box(0);
v___y_4946_ = v___x_4967_;
goto v___jp_4945_;
}
v___jp_4945_:
{
lean_object* v_resetTargets_4947_; lean_object* v_unconditionalBorrows_4948_; lean_object* v_derivedValMap_4949_; lean_object* v_varMap_4950_; lean_object* v_jpLiveVarMap_4951_; lean_object* v_idx_4952_; uint8_t v___x_4953_; uint8_t v___x_4954_; uint8_t v___x_4955_; lean_object* v_varInfo_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v_ctx_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v_resetTargets_4947_ = lean_ctor_get(v_a_4933_, 0);
v_unconditionalBorrows_4948_ = lean_ctor_get(v_a_4933_, 1);
v_derivedValMap_4949_ = lean_ctor_get(v_a_4933_, 2);
v_varMap_4950_ = lean_ctor_get(v_a_4933_, 3);
v_jpLiveVarMap_4951_ = lean_ctor_get(v_a_4933_, 4);
v_idx_4952_ = lean_ctor_get(v_a_4933_, 5);
v___x_4953_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_4943_);
v___x_4954_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_4943_);
v___x_4955_ = l_Lean_Compiler_LCNF_LetValue_isPersistent(v_value_4944_);
lean_inc(v_idx_4952_);
v_varInfo_4956_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_varInfo_4956_, 0, v_idx_4952_);
lean_ctor_set(v_varInfo_4956_, 1, v___y_4946_);
lean_ctor_set_uint8(v_varInfo_4956_, sizeof(void*)*2, v___x_4953_);
lean_ctor_set_uint8(v_varInfo_4956_, sizeof(void*)*2 + 1, v___x_4954_);
lean_ctor_set_uint8(v_varInfo_4956_, sizeof(void*)*2 + 2, v___x_4955_);
lean_inc(v_varMap_4950_);
lean_inc(v_fvarId_4942_);
v___x_4957_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_4942_, v_varInfo_4956_, v_varMap_4950_);
v___x_4958_ = lean_unsigned_to_nat(1u);
v___x_4959_ = lean_nat_add(v_idx_4952_, v___x_4958_);
lean_inc(v_jpLiveVarMap_4951_);
lean_inc(v_derivedValMap_4949_);
lean_inc(v_unconditionalBorrows_4948_);
lean_inc_ref(v_resetTargets_4947_);
v_ctx_4960_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_ctx_4960_, 0, v_resetTargets_4947_);
lean_ctor_set(v_ctx_4960_, 1, v_unconditionalBorrows_4948_);
lean_ctor_set(v_ctx_4960_, 2, v_derivedValMap_4949_);
lean_ctor_set(v_ctx_4960_, 3, v___x_4957_);
lean_ctor_set(v_ctx_4960_, 4, v_jpLiveVarMap_4951_);
lean_ctor_set(v_ctx_4960_, 5, v___x_4959_);
lean_inc_ref(v_decl_4940_);
v___x_4961_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(v_ctx_4960_, v_decl_4940_);
lean_inc_ref(v_k_4941_);
v___x_4962_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_4941_, v___x_4961_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; lean_object* v___x_4964_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_a_4963_);
lean_dec_ref_known(v___x_4962_, 1);
v___x_4964_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(v_code_4932_, v_decl_4940_, v_a_4963_, v___x_4961_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
lean_dec_ref(v___x_4961_);
return v___x_4964_;
}
else
{
lean_dec_ref(v___x_4961_);
lean_dec_ref_known(v_code_4932_, 2);
lean_dec_ref(v_decl_4940_);
return v___x_4962_;
}
}
}
case 2:
{
lean_object* v_decl_4968_; lean_object* v_k_4969_; lean_object* v_fst_4971_; lean_object* v_snd_4972_; lean_object* v_params_5021_; lean_object* v_type_5022_; lean_object* v_value_5023_; uint8_t v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; uint8_t v___x_5027_; 
v_decl_4968_ = lean_ctor_get(v_code_4932_, 0);
v_k_4969_ = lean_ctor_get(v_code_4932_, 1);
v_params_5021_ = lean_ctor_get(v_decl_4968_, 2);
v_type_5022_ = lean_ctor_get(v_decl_4968_, 3);
v_value_5023_ = lean_ctor_get(v_decl_4968_, 4);
v___x_5024_ = 1;
v___x_5025_ = lean_unsigned_to_nat(0u);
v___x_5026_ = lean_array_get_size(v_params_5021_);
v___x_5027_ = lean_nat_dec_lt(v___x_5025_, v___x_5026_);
if (v___x_5027_ == 0)
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5028_ = lean_st_ref_get(v_a_4934_);
v___x_5029_ = lean_st_ref_take(v_a_4934_);
lean_dec(v___x_5029_);
v___x_5030_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5031_ = lean_st_ref_put(v_a_4934_, v___x_5030_);
lean_inc_ref(v_value_5023_);
v___x_5032_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_value_5023_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
if (lean_obj_tag(v___x_5032_) == 0)
{
lean_object* v_a_5033_; lean_object* v___x_5034_; 
v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc(v_a_5033_);
lean_dec_ref_known(v___x_5032_, 1);
v___x_5034_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5021_, v_a_5033_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_object* v_a_5035_; lean_object* v___x_5036_; 
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_a_5035_);
lean_dec_ref_known(v___x_5034_, 1);
lean_inc_ref(v_params_5021_);
lean_inc_ref(v_type_5022_);
lean_inc_ref(v_decl_4968_);
v___x_5036_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5024_, v_decl_4968_, v_type_5022_, v_params_5021_, v_a_5035_, v_a_4936_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_a_5037_);
lean_dec_ref_known(v___x_5036_, 1);
v___x_5038_ = lean_st_ref_get(v_a_4934_);
v___x_5039_ = lean_st_ref_take(v_a_4934_);
lean_dec(v___x_5039_);
v___x_5040_ = lean_st_ref_put(v_a_4934_, v___x_5028_);
v_fst_4971_ = v_a_5037_;
v_snd_4972_ = v___x_5038_;
goto v___jp_4970_;
}
else
{
lean_object* v_a_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5048_; 
lean_dec(v___x_5028_);
lean_dec_ref_known(v_code_4932_, 2);
v_a_5041_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_5043_ = v___x_5036_;
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_a_5041_);
lean_dec(v___x_5036_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5046_; 
if (v_isShared_5044_ == 0)
{
v___x_5046_ = v___x_5043_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5041_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
}
else
{
lean_dec(v___x_5028_);
lean_dec_ref_known(v_code_4932_, 2);
return v___x_5034_;
}
}
else
{
lean_dec(v___x_5028_);
lean_dec_ref_known(v_code_4932_, 2);
return v___x_5032_;
}
}
else
{
size_t v___x_5049_; size_t v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5049_ = ((size_t)0ULL);
v___x_5050_ = lean_usize_of_nat(v___x_5026_);
lean_inc_ref(v_a_4933_);
v___x_5051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_params_5021_, v___x_5049_, v___x_5050_, v_a_4933_);
v___x_5052_ = lean_st_ref_get(v_a_4934_);
v___x_5053_ = lean_st_ref_take(v_a_4934_);
lean_dec(v___x_5053_);
v___x_5054_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5055_ = lean_st_ref_put(v_a_4934_, v___x_5054_);
lean_inc_ref(v_value_5023_);
v___x_5056_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_value_5023_, v___x_5051_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
if (lean_obj_tag(v___x_5056_) == 0)
{
lean_object* v_a_5057_; lean_object* v___x_5058_; 
v_a_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc(v_a_5057_);
lean_dec_ref_known(v___x_5056_, 1);
v___x_5058_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5021_, v_a_5057_, v___x_5051_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
lean_dec_ref(v___x_5051_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_object* v_a_5059_; lean_object* v___x_5060_; 
v_a_5059_ = lean_ctor_get(v___x_5058_, 0);
lean_inc(v_a_5059_);
lean_dec_ref_known(v___x_5058_, 1);
lean_inc_ref(v_params_5021_);
lean_inc_ref(v_type_5022_);
lean_inc_ref(v_decl_4968_);
v___x_5060_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5024_, v_decl_4968_, v_type_5022_, v_params_5021_, v_a_5059_, v_a_4936_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5061_);
lean_dec_ref_known(v___x_5060_, 1);
v___x_5062_ = lean_st_ref_get(v_a_4934_);
v___x_5063_ = lean_st_ref_take(v_a_4934_);
lean_dec(v___x_5063_);
v___x_5064_ = lean_st_ref_put(v_a_4934_, v___x_5052_);
v_fst_4971_ = v_a_5061_;
v_snd_4972_ = v___x_5062_;
goto v___jp_4970_;
}
else
{
lean_object* v_a_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5072_; 
lean_dec(v___x_5052_);
lean_dec_ref_known(v_code_4932_, 2);
v_a_5065_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5067_ = v___x_5060_;
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_a_5065_);
lean_dec(v___x_5060_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5070_; 
if (v_isShared_5068_ == 0)
{
v___x_5070_ = v___x_5067_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5065_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
else
{
lean_dec(v___x_5052_);
lean_dec_ref_known(v_code_4932_, 2);
return v___x_5058_;
}
}
else
{
lean_dec(v___x_5052_);
lean_dec_ref(v___x_5051_);
lean_dec_ref_known(v_code_4932_, 2);
return v___x_5056_;
}
}
v___jp_4970_:
{
lean_object* v_fvarId_4973_; lean_object* v_resetTargets_4974_; lean_object* v_unconditionalBorrows_4975_; lean_object* v_derivedValMap_4976_; lean_object* v_varMap_4977_; lean_object* v_jpLiveVarMap_4978_; lean_object* v_idx_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v_fvarId_4973_ = lean_ctor_get(v_fst_4971_, 0);
v_resetTargets_4974_ = lean_ctor_get(v_a_4933_, 0);
v_unconditionalBorrows_4975_ = lean_ctor_get(v_a_4933_, 1);
v_derivedValMap_4976_ = lean_ctor_get(v_a_4933_, 2);
v_varMap_4977_ = lean_ctor_get(v_a_4933_, 3);
v_jpLiveVarMap_4978_ = lean_ctor_get(v_a_4933_, 4);
v_idx_4979_ = lean_ctor_get(v_a_4933_, 5);
lean_inc(v_jpLiveVarMap_4978_);
lean_inc(v_fvarId_4973_);
v___x_4980_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_4973_, v_snd_4972_, v_jpLiveVarMap_4978_);
lean_inc(v_idx_4979_);
lean_inc(v_varMap_4977_);
lean_inc(v_derivedValMap_4976_);
lean_inc(v_unconditionalBorrows_4975_);
lean_inc_ref(v_resetTargets_4974_);
v___x_4981_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4981_, 0, v_resetTargets_4974_);
lean_ctor_set(v___x_4981_, 1, v_unconditionalBorrows_4975_);
lean_ctor_set(v___x_4981_, 2, v_derivedValMap_4976_);
lean_ctor_set(v___x_4981_, 3, v_varMap_4977_);
lean_ctor_set(v___x_4981_, 4, v___x_4980_);
lean_ctor_set(v___x_4981_, 5, v_idx_4979_);
lean_inc_ref(v_k_4969_);
v___x_4982_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_4969_, v___x_4981_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
lean_dec_ref_known(v___x_4981_, 6);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_5020_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_4985_ = v___x_4982_;
v_isShared_4986_ = v_isSharedCheck_5020_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v___x_4982_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_5020_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
size_t v___x_4987_; size_t v___x_4988_; uint8_t v___x_4989_; 
v___x_4987_ = lean_ptr_addr(v_k_4969_);
v___x_4988_ = lean_ptr_addr(v_a_4983_);
v___x_4989_ = lean_usize_dec_eq(v___x_4987_, v___x_4988_);
if (v___x_4989_ == 0)
{
lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4999_; 
v_isSharedCheck_4999_ = !lean_is_exclusive(v_code_4932_);
if (v_isSharedCheck_4999_ == 0)
{
lean_object* v_unused_5000_; lean_object* v_unused_5001_; 
v_unused_5000_ = lean_ctor_get(v_code_4932_, 1);
lean_dec(v_unused_5000_);
v_unused_5001_ = lean_ctor_get(v_code_4932_, 0);
lean_dec(v_unused_5001_);
v___x_4991_ = v_code_4932_;
v_isShared_4992_ = v_isSharedCheck_4999_;
goto v_resetjp_4990_;
}
else
{
lean_dec(v_code_4932_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4999_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
lean_ctor_set(v___x_4991_, 1, v_a_4983_);
lean_ctor_set(v___x_4991_, 0, v_fst_4971_);
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_fst_4971_);
lean_ctor_set(v_reuseFailAlloc_4998_, 1, v_a_4983_);
v___x_4994_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4996_; 
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v___x_4994_);
v___x_4996_ = v___x_4985_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v___x_4994_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
}
else
{
size_t v___x_5002_; size_t v___x_5003_; uint8_t v___x_5004_; 
v___x_5002_ = lean_ptr_addr(v_decl_4968_);
v___x_5003_ = lean_ptr_addr(v_fst_4971_);
v___x_5004_ = lean_usize_dec_eq(v___x_5002_, v___x_5003_);
if (v___x_5004_ == 0)
{
lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5014_; 
v_isSharedCheck_5014_ = !lean_is_exclusive(v_code_4932_);
if (v_isSharedCheck_5014_ == 0)
{
lean_object* v_unused_5015_; lean_object* v_unused_5016_; 
v_unused_5015_ = lean_ctor_get(v_code_4932_, 1);
lean_dec(v_unused_5015_);
v_unused_5016_ = lean_ctor_get(v_code_4932_, 0);
lean_dec(v_unused_5016_);
v___x_5006_ = v_code_4932_;
v_isShared_5007_ = v_isSharedCheck_5014_;
goto v_resetjp_5005_;
}
else
{
lean_dec(v_code_4932_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5014_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
lean_ctor_set(v___x_5006_, 1, v_a_4983_);
lean_ctor_set(v___x_5006_, 0, v_fst_4971_);
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_fst_4971_);
lean_ctor_set(v_reuseFailAlloc_5013_, 1, v_a_4983_);
v___x_5009_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5011_; 
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v___x_5009_);
v___x_5011_ = v___x_4985_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v___x_5009_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
}
}
else
{
lean_object* v___x_5018_; 
lean_dec(v_a_4983_);
lean_dec_ref(v_fst_4971_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v_code_4932_);
v___x_5018_ = v___x_4985_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_code_4932_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
}
}
}
else
{
lean_dec_ref(v_fst_4971_);
lean_dec_ref_known(v_code_4932_, 2);
return v___x_4982_;
}
}
}
case 3:
{
lean_object* v_fvarId_5073_; lean_object* v_args_5074_; lean_object* v_jpLiveVarMap_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v_fvarId_5073_ = lean_ctor_get(v_code_4932_, 0);
v_args_5074_ = lean_ctor_get(v_code_4932_, 1);
lean_inc_ref(v_args_5074_);
v_jpLiveVarMap_5075_ = lean_ctor_get(v_a_4933_, 4);
v___x_5076_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(v_jpLiveVarMap_5075_, v_fvarId_5073_);
v___x_5077_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_5076_, v_a_4933_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_object* v_a_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; uint8_t v___x_5081_; lean_object* v___x_5082_; 
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_a_5078_);
lean_dec_ref_known(v___x_5077_, 1);
v___x_5079_ = lean_st_ref_take(v_a_4934_);
lean_dec(v___x_5079_);
v___x_5080_ = lean_st_ref_put(v_a_4934_, v_a_5078_);
v___x_5081_ = 1;
v___x_5082_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_5081_, v_fvarId_5073_, v_a_4936_);
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_object* v_a_5083_; lean_object* v___y_5085_; 
v_a_5083_ = lean_ctor_get(v___x_5082_, 0);
lean_inc(v_a_5083_);
lean_dec_ref_known(v___x_5082_, 1);
if (lean_obj_tag(v_a_5083_) == 0)
{
lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5106_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10);
v___x_5107_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5(v___x_5106_);
v___y_5085_ = v___x_5107_;
goto v___jp_5084_;
}
else
{
lean_object* v_val_5108_; 
v_val_5108_ = lean_ctor_get(v_a_5083_, 0);
lean_inc(v_val_5108_);
lean_dec_ref_known(v_a_5083_, 1);
v___y_5085_ = v_val_5108_;
goto v___jp_5084_;
}
v___jp_5084_:
{
lean_object* v_params_5086_; lean_object* v___x_5087_; 
v_params_5086_ = lean_ctor_get(v___y_5085_, 2);
lean_inc_ref(v_params_5086_);
lean_dec_ref(v___y_5085_);
v___x_5087_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_5074_, v_params_5086_, v_code_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v_a_5088_; lean_object* v___x_5089_; 
v_a_5088_ = lean_ctor_get(v___x_5087_, 0);
lean_inc(v_a_5088_);
lean_dec_ref_known(v___x_5087_, 1);
v___x_5089_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_5074_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
lean_dec_ref(v_args_5074_);
if (lean_obj_tag(v___x_5089_) == 0)
{
lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5096_; 
v_isSharedCheck_5096_ = !lean_is_exclusive(v___x_5089_);
if (v_isSharedCheck_5096_ == 0)
{
lean_object* v_unused_5097_; 
v_unused_5097_ = lean_ctor_get(v___x_5089_, 0);
lean_dec(v_unused_5097_);
v___x_5091_ = v___x_5089_;
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
else
{
lean_dec(v___x_5089_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5094_; 
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 0, v_a_5088_);
v___x_5094_ = v___x_5091_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_a_5088_);
v___x_5094_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
return v___x_5094_;
}
}
}
else
{
lean_object* v_a_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5105_; 
lean_dec(v_a_5088_);
v_a_5098_ = lean_ctor_get(v___x_5089_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5089_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5100_ = v___x_5089_;
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_a_5098_);
lean_dec(v___x_5089_);
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
lean_dec_ref(v_args_5074_);
return v___x_5087_;
}
}
}
else
{
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
lean_dec_ref(v_args_5074_);
lean_dec_ref_known(v_code_4932_, 2);
v_a_5109_ = lean_ctor_get(v___x_5082_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5082_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_5082_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_5082_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5114_; 
if (v_isShared_5112_ == 0)
{
v___x_5114_ = v___x_5111_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5109_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
return v___x_5114_;
}
}
}
}
else
{
lean_object* v_a_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5124_; 
lean_dec_ref(v_args_5074_);
lean_dec_ref_known(v_code_4932_, 2);
v_a_5117_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5119_ = v___x_5077_;
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_a_5117_);
lean_dec(v___x_5077_);
v___x_5119_ = lean_box(0);
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
v_resetjp_5118_:
{
lean_object* v___x_5122_; 
if (v_isShared_5120_ == 0)
{
v___x_5122_ = v___x_5119_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5123_; 
v_reuseFailAlloc_5123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5123_, 0, v_a_5117_);
v___x_5122_ = v_reuseFailAlloc_5123_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
return v___x_5122_;
}
}
}
}
case 4:
{
lean_object* v_cases_5125_; lean_object* v_typeName_5126_; lean_object* v_resultType_5127_; lean_object* v_discr_5128_; lean_object* v_alts_5129_; size_t v_sz_5130_; size_t v___x_5131_; lean_object* v___x_5132_; 
v_cases_5125_ = lean_ctor_get(v_code_4932_, 0);
v_typeName_5126_ = lean_ctor_get(v_cases_5125_, 0);
v_resultType_5127_ = lean_ctor_get(v_cases_5125_, 1);
v_discr_5128_ = lean_ctor_get(v_cases_5125_, 2);
v_alts_5129_ = lean_ctor_get(v_cases_5125_, 3);
v_sz_5130_ = lean_array_size(v_alts_5129_);
v___x_5131_ = ((size_t)0ULL);
lean_inc_ref(v_alts_5129_);
lean_inc_ref(v_cases_5125_);
v___x_5132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(v_cases_5125_, v_sz_5130_, v___x_5131_, v_alts_5129_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v_a_5133_; lean_object* v___y_5135_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; uint8_t v___x_5183_; 
v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_a_5133_);
lean_dec_ref_known(v___x_5132_, 1);
v___x_5180_ = lean_unsigned_to_nat(0u);
v___x_5181_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5182_ = lean_array_get_size(v_a_5133_);
v___x_5183_ = lean_nat_dec_lt(v___x_5180_, v___x_5182_);
if (v___x_5183_ == 0)
{
v___y_5135_ = v___x_5181_;
goto v___jp_5134_;
}
else
{
uint8_t v___x_5184_; 
v___x_5184_ = lean_nat_dec_le(v___x_5182_, v___x_5182_);
if (v___x_5184_ == 0)
{
if (v___x_5183_ == 0)
{
v___y_5135_ = v___x_5181_;
goto v___jp_5134_;
}
else
{
size_t v___x_5185_; lean_object* v___x_5186_; 
v___x_5185_ = lean_usize_of_nat(v___x_5182_);
v___x_5186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_a_5133_, v___x_5131_, v___x_5185_, v___x_5181_);
v___y_5135_ = v___x_5186_;
goto v___jp_5134_;
}
}
else
{
size_t v___x_5187_; lean_object* v___x_5188_; 
v___x_5187_ = lean_usize_of_nat(v___x_5182_);
v___x_5188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_a_5133_, v___x_5131_, v___x_5187_, v___x_5181_);
v___y_5135_ = v___x_5188_;
goto v___jp_5134_;
}
}
v___jp_5134_:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; 
v___x_5136_ = lean_st_ref_take(v_a_4934_);
lean_dec(v___x_5136_);
v___x_5137_ = lean_st_ref_put(v_a_4934_, v___y_5135_);
lean_inc(v_discr_5128_);
v___x_5138_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_discr_5128_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_5138_) == 0)
{
size_t v_sz_5139_; lean_object* v___x_5140_; 
lean_dec_ref_known(v___x_5138_, 1);
v_sz_5139_ = lean_array_size(v_a_5133_);
lean_inc(v_discr_5128_);
v___x_5140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(v_discr_5128_, v_sz_5139_, v___x_5131_, v_a_5133_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_object* v_a_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5163_; 
v_a_5141_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5143_ = v___x_5140_;
v_isShared_5144_ = v_isSharedCheck_5163_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_a_5141_);
lean_dec(v___x_5140_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5163_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
size_t v___x_5145_; size_t v___x_5146_; uint8_t v___x_5147_; 
v___x_5145_ = lean_ptr_addr(v_alts_5129_);
v___x_5146_ = lean_ptr_addr(v_a_5141_);
v___x_5147_ = lean_usize_dec_eq(v___x_5145_, v___x_5146_);
if (v___x_5147_ == 0)
{
lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5158_; 
lean_inc(v_discr_5128_);
lean_inc_ref(v_resultType_5127_);
lean_inc(v_typeName_5126_);
v_isSharedCheck_5158_ = !lean_is_exclusive(v_code_4932_);
if (v_isSharedCheck_5158_ == 0)
{
lean_object* v_unused_5159_; 
v_unused_5159_ = lean_ctor_get(v_code_4932_, 0);
lean_dec(v_unused_5159_);
v___x_5149_ = v_code_4932_;
v_isShared_5150_ = v_isSharedCheck_5158_;
goto v_resetjp_5148_;
}
else
{
lean_dec(v_code_4932_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5158_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5151_; lean_object* v___x_5153_; 
v___x_5151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5151_, 0, v_typeName_5126_);
lean_ctor_set(v___x_5151_, 1, v_resultType_5127_);
lean_ctor_set(v___x_5151_, 2, v_discr_5128_);
lean_ctor_set(v___x_5151_, 3, v_a_5141_);
if (v_isShared_5150_ == 0)
{
lean_ctor_set(v___x_5149_, 0, v___x_5151_);
v___x_5153_ = v___x_5149_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v___x_5151_);
v___x_5153_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
lean_object* v___x_5155_; 
if (v_isShared_5144_ == 0)
{
lean_ctor_set(v___x_5143_, 0, v___x_5153_);
v___x_5155_ = v___x_5143_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5153_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
}
else
{
lean_object* v___x_5161_; 
lean_dec(v_a_5141_);
if (v_isShared_5144_ == 0)
{
lean_ctor_set(v___x_5143_, 0, v_code_4932_);
v___x_5161_ = v___x_5143_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_code_4932_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
else
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5171_; 
lean_dec_ref_known(v_code_4932_, 1);
v_a_5164_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5166_ = v___x_5140_;
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5140_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5169_; 
if (v_isShared_5167_ == 0)
{
v___x_5169_ = v___x_5166_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
else
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5179_; 
lean_dec(v_a_5133_);
lean_dec_ref_known(v_code_4932_, 1);
v_a_5172_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5174_ = v___x_5138_;
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5138_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5177_; 
if (v_isShared_5175_ == 0)
{
v___x_5177_ = v___x_5174_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
}
}
}
}
}
else
{
lean_object* v_a_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5196_; 
lean_dec_ref_known(v_code_4932_, 1);
v_a_5189_ = lean_ctor_get(v___x_5132_, 0);
v_isSharedCheck_5196_ = !lean_is_exclusive(v___x_5132_);
if (v_isSharedCheck_5196_ == 0)
{
v___x_5191_ = v___x_5132_;
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_a_5189_);
lean_dec(v___x_5132_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v___x_5194_; 
if (v_isShared_5192_ == 0)
{
v___x_5194_ = v___x_5191_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5195_; 
v_reuseFailAlloc_5195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5195_, 0, v_a_5189_);
v___x_5194_ = v_reuseFailAlloc_5195_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
return v___x_5194_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; 
v_fvarId_5197_ = lean_ctor_get(v_code_4932_, 0);
v___x_5198_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5199_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_5198_, v_a_4933_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v_varMap_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; 
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
lean_inc(v_a_5200_);
lean_dec_ref_known(v___x_5199_, 1);
v___x_5201_ = lean_st_ref_take(v_a_4934_);
lean_dec(v___x_5201_);
v___x_5202_ = lean_st_ref_put(v_a_4934_, v_a_5200_);
v_varMap_5203_ = lean_ctor_get(v_a_4933_, 3);
v___x_5204_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_5203_, v_fvarId_5197_);
lean_inc(v_fvarId_5197_);
v___x_5205_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_5197_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_5205_) == 0)
{
lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5229_; 
v_isSharedCheck_5229_ = !lean_is_exclusive(v___x_5205_);
if (v_isSharedCheck_5229_ == 0)
{
lean_object* v_unused_5230_; 
v_unused_5230_ = lean_ctor_get(v___x_5205_, 0);
lean_dec(v_unused_5230_);
v___x_5207_ = v___x_5205_;
v_isShared_5208_ = v_isSharedCheck_5229_;
goto v_resetjp_5206_;
}
else
{
lean_dec(v___x_5205_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5229_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5209_; uint8_t v_isPossibleRef_5210_; 
v___x_5209_ = lean_st_ref_get(v_a_4934_);
v_isPossibleRef_5210_ = lean_ctor_get_uint8(v___x_5204_, sizeof(void*)*2);
if (v_isPossibleRef_5210_ == 0)
{
lean_object* v___x_5212_; 
lean_dec(v___x_5209_);
lean_dec_ref(v___x_5204_);
if (v_isShared_5208_ == 0)
{
lean_ctor_set(v___x_5207_, 0, v_code_4932_);
v___x_5212_ = v___x_5207_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v_code_4932_);
v___x_5212_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
return v___x_5212_;
}
}
else
{
uint8_t v_isDefiniteRef_5214_; uint8_t v_persistent_5215_; lean_object* v_borrows_5216_; uint8_t v___x_5217_; 
v_isDefiniteRef_5214_ = lean_ctor_get_uint8(v___x_5204_, sizeof(void*)*2 + 1);
v_persistent_5215_ = lean_ctor_get_uint8(v___x_5204_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_5204_);
v_borrows_5216_ = lean_ctor_get(v___x_5209_, 1);
lean_inc_ref(v_borrows_5216_);
lean_dec(v___x_5209_);
v___x_5217_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_5216_, v_fvarId_5197_);
lean_dec_ref(v_borrows_5216_);
if (v___x_5217_ == 0)
{
lean_object* v___x_5219_; 
if (v_isShared_5208_ == 0)
{
lean_ctor_set(v___x_5207_, 0, v_code_4932_);
v___x_5219_ = v___x_5207_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5220_; 
v_reuseFailAlloc_5220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5220_, 0, v_code_4932_);
v___x_5219_ = v_reuseFailAlloc_5220_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
return v___x_5219_;
}
}
else
{
lean_object* v___x_5221_; uint8_t v___y_5223_; 
lean_inc(v_fvarId_5197_);
v___x_5221_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_5214_ == 0)
{
v___y_5223_ = v___x_5217_;
goto v___jp_5222_;
}
else
{
uint8_t v___x_5228_; 
v___x_5228_ = 0;
v___y_5223_ = v___x_5228_;
goto v___jp_5222_;
}
v___jp_5222_:
{
lean_object* v___x_5224_; lean_object* v___x_5226_; 
v___x_5224_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_5224_, 0, v_fvarId_5197_);
lean_ctor_set(v___x_5224_, 1, v___x_5221_);
lean_ctor_set(v___x_5224_, 2, v_code_4932_);
lean_ctor_set_uint8(v___x_5224_, sizeof(void*)*3, v___y_5223_);
lean_ctor_set_uint8(v___x_5224_, sizeof(void*)*3 + 1, v_persistent_5215_);
if (v_isShared_5208_ == 0)
{
lean_ctor_set(v___x_5207_, 0, v___x_5224_);
v___x_5226_ = v___x_5207_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v___x_5224_);
v___x_5226_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
return v___x_5226_;
}
}
}
}
}
}
else
{
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5238_; 
lean_dec_ref(v___x_5204_);
lean_dec_ref_known(v_code_4932_, 1);
v_a_5231_ = lean_ctor_get(v___x_5205_, 0);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5205_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5233_ = v___x_5205_;
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v___x_5205_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5236_; 
if (v_isShared_5234_ == 0)
{
v___x_5236_ = v___x_5233_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_a_5231_);
v___x_5236_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
return v___x_5236_;
}
}
}
}
else
{
lean_object* v_a_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5246_; 
lean_dec_ref_known(v_code_4932_, 1);
v_a_5239_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5241_ = v___x_5199_;
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_a_5239_);
lean_dec(v___x_5199_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5244_; 
if (v_isShared_5242_ == 0)
{
v___x_5244_ = v___x_5241_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
return v___x_5244_;
}
}
}
}
case 6:
{
lean_object* v___x_5247_; lean_object* v___x_5248_; 
v___x_5247_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5248_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_5247_, v_a_4933_);
if (lean_obj_tag(v___x_5248_) == 0)
{
lean_object* v_a_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5258_; 
v_a_5249_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5251_ = v___x_5248_;
v_isShared_5252_ = v_isSharedCheck_5258_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5248_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5258_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5256_; 
v___x_5253_ = lean_st_ref_take(v_a_4934_);
lean_dec(v___x_5253_);
v___x_5254_ = lean_st_ref_put(v_a_4934_, v_a_5249_);
if (v_isShared_5252_ == 0)
{
lean_ctor_set(v___x_5251_, 0, v_code_4932_);
v___x_5256_ = v___x_5251_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v_code_4932_);
v___x_5256_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
return v___x_5256_;
}
}
}
else
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5266_; 
lean_dec_ref_known(v_code_4932_, 1);
v_a_5259_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5261_ = v___x_5248_;
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___x_5248_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
}
case 8:
{
lean_object* v_fvarId_5267_; lean_object* v_i_5268_; lean_object* v_y_5269_; lean_object* v_k_5270_; lean_object* v___x_5271_; 
v_fvarId_5267_ = lean_ctor_get(v_code_4932_, 0);
v_i_5268_ = lean_ctor_get(v_code_4932_, 1);
v_y_5269_ = lean_ctor_get(v_code_4932_, 2);
v_k_5270_ = lean_ctor_get(v_code_4932_, 3);
lean_inc_ref(v_k_5270_);
v___x_5271_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5270_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
if (lean_obj_tag(v___x_5271_) == 0)
{
lean_object* v_a_5272_; lean_object* v___x_5273_; 
v_a_5272_ = lean_ctor_get(v___x_5271_, 0);
lean_inc(v_a_5272_);
lean_dec_ref_known(v___x_5271_, 1);
lean_inc(v_fvarId_5267_);
v___x_5273_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_5267_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_5273_) == 0)
{
lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5297_; 
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5297_ == 0)
{
lean_object* v_unused_5298_; 
v_unused_5298_ = lean_ctor_get(v___x_5273_, 0);
lean_dec(v_unused_5298_);
v___x_5275_ = v___x_5273_;
v_isShared_5276_ = v_isSharedCheck_5297_;
goto v_resetjp_5274_;
}
else
{
lean_dec(v___x_5273_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5297_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
size_t v___x_5277_; size_t v___x_5278_; uint8_t v___x_5279_; 
v___x_5277_ = lean_ptr_addr(v_k_5270_);
v___x_5278_ = lean_ptr_addr(v_a_5272_);
v___x_5279_ = lean_usize_dec_eq(v___x_5277_, v___x_5278_);
if (v___x_5279_ == 0)
{
lean_object* v___x_5281_; uint8_t v_isShared_5282_; uint8_t v_isSharedCheck_5289_; 
lean_inc(v_y_5269_);
lean_inc(v_i_5268_);
lean_inc(v_fvarId_5267_);
v_isSharedCheck_5289_ = !lean_is_exclusive(v_code_4932_);
if (v_isSharedCheck_5289_ == 0)
{
lean_object* v_unused_5290_; lean_object* v_unused_5291_; lean_object* v_unused_5292_; lean_object* v_unused_5293_; 
v_unused_5290_ = lean_ctor_get(v_code_4932_, 3);
lean_dec(v_unused_5290_);
v_unused_5291_ = lean_ctor_get(v_code_4932_, 2);
lean_dec(v_unused_5291_);
v_unused_5292_ = lean_ctor_get(v_code_4932_, 1);
lean_dec(v_unused_5292_);
v_unused_5293_ = lean_ctor_get(v_code_4932_, 0);
lean_dec(v_unused_5293_);
v___x_5281_ = v_code_4932_;
v_isShared_5282_ = v_isSharedCheck_5289_;
goto v_resetjp_5280_;
}
else
{
lean_dec(v_code_4932_);
v___x_5281_ = lean_box(0);
v_isShared_5282_ = v_isSharedCheck_5289_;
goto v_resetjp_5280_;
}
v_resetjp_5280_:
{
lean_object* v___x_5284_; 
if (v_isShared_5282_ == 0)
{
lean_ctor_set(v___x_5281_, 3, v_a_5272_);
v___x_5284_ = v___x_5281_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v_fvarId_5267_);
lean_ctor_set(v_reuseFailAlloc_5288_, 1, v_i_5268_);
lean_ctor_set(v_reuseFailAlloc_5288_, 2, v_y_5269_);
lean_ctor_set(v_reuseFailAlloc_5288_, 3, v_a_5272_);
v___x_5284_ = v_reuseFailAlloc_5288_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
lean_object* v___x_5286_; 
if (v_isShared_5276_ == 0)
{
lean_ctor_set(v___x_5275_, 0, v___x_5284_);
v___x_5286_ = v___x_5275_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v___x_5284_);
v___x_5286_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
return v___x_5286_;
}
}
}
}
else
{
lean_object* v___x_5295_; 
lean_dec(v_a_5272_);
if (v_isShared_5276_ == 0)
{
lean_ctor_set(v___x_5275_, 0, v_code_4932_);
v___x_5295_ = v___x_5275_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_code_4932_);
v___x_5295_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
return v___x_5295_;
}
}
}
}
else
{
lean_object* v_a_5299_; lean_object* v___x_5301_; uint8_t v_isShared_5302_; uint8_t v_isSharedCheck_5306_; 
lean_dec(v_a_5272_);
lean_dec_ref_known(v_code_4932_, 4);
v_a_5299_ = lean_ctor_get(v___x_5273_, 0);
v_isSharedCheck_5306_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5306_ == 0)
{
v___x_5301_ = v___x_5273_;
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
else
{
lean_inc(v_a_5299_);
lean_dec(v___x_5273_);
v___x_5301_ = lean_box(0);
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
v_resetjp_5300_:
{
lean_object* v___x_5304_; 
if (v_isShared_5302_ == 0)
{
v___x_5304_ = v___x_5301_;
goto v_reusejp_5303_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_a_5299_);
v___x_5304_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5303_;
}
v_reusejp_5303_:
{
return v___x_5304_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_4932_, 4);
return v___x_5271_;
}
}
case 9:
{
lean_object* v_fvarId_5307_; lean_object* v_i_5308_; lean_object* v_offset_5309_; lean_object* v_y_5310_; lean_object* v_ty_5311_; lean_object* v_k_5312_; lean_object* v___x_5313_; 
v_fvarId_5307_ = lean_ctor_get(v_code_4932_, 0);
v_i_5308_ = lean_ctor_get(v_code_4932_, 1);
v_offset_5309_ = lean_ctor_get(v_code_4932_, 2);
v_y_5310_ = lean_ctor_get(v_code_4932_, 3);
v_ty_5311_ = lean_ctor_get(v_code_4932_, 4);
v_k_5312_ = lean_ctor_get(v_code_4932_, 5);
lean_inc_ref(v_k_5312_);
v___x_5313_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5312_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
if (lean_obj_tag(v___x_5313_) == 0)
{
lean_object* v_a_5314_; lean_object* v___x_5315_; 
v_a_5314_ = lean_ctor_get(v___x_5313_, 0);
lean_inc(v_a_5314_);
lean_dec_ref_known(v___x_5313_, 1);
lean_inc(v_fvarId_5307_);
v___x_5315_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_5307_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_5315_) == 0)
{
lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5341_; 
v_isSharedCheck_5341_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5341_ == 0)
{
lean_object* v_unused_5342_; 
v_unused_5342_ = lean_ctor_get(v___x_5315_, 0);
lean_dec(v_unused_5342_);
v___x_5317_ = v___x_5315_;
v_isShared_5318_ = v_isSharedCheck_5341_;
goto v_resetjp_5316_;
}
else
{
lean_dec(v___x_5315_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5341_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
size_t v___x_5319_; size_t v___x_5320_; uint8_t v___x_5321_; 
v___x_5319_ = lean_ptr_addr(v_k_5312_);
v___x_5320_ = lean_ptr_addr(v_a_5314_);
v___x_5321_ = lean_usize_dec_eq(v___x_5319_, v___x_5320_);
if (v___x_5321_ == 0)
{
lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5331_; 
lean_inc_ref(v_ty_5311_);
lean_inc(v_y_5310_);
lean_inc(v_offset_5309_);
lean_inc(v_i_5308_);
lean_inc(v_fvarId_5307_);
v_isSharedCheck_5331_ = !lean_is_exclusive(v_code_4932_);
if (v_isSharedCheck_5331_ == 0)
{
lean_object* v_unused_5332_; lean_object* v_unused_5333_; lean_object* v_unused_5334_; lean_object* v_unused_5335_; lean_object* v_unused_5336_; lean_object* v_unused_5337_; 
v_unused_5332_ = lean_ctor_get(v_code_4932_, 5);
lean_dec(v_unused_5332_);
v_unused_5333_ = lean_ctor_get(v_code_4932_, 4);
lean_dec(v_unused_5333_);
v_unused_5334_ = lean_ctor_get(v_code_4932_, 3);
lean_dec(v_unused_5334_);
v_unused_5335_ = lean_ctor_get(v_code_4932_, 2);
lean_dec(v_unused_5335_);
v_unused_5336_ = lean_ctor_get(v_code_4932_, 1);
lean_dec(v_unused_5336_);
v_unused_5337_ = lean_ctor_get(v_code_4932_, 0);
lean_dec(v_unused_5337_);
v___x_5323_ = v_code_4932_;
v_isShared_5324_ = v_isSharedCheck_5331_;
goto v_resetjp_5322_;
}
else
{
lean_dec(v_code_4932_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5331_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5326_; 
if (v_isShared_5324_ == 0)
{
lean_ctor_set(v___x_5323_, 5, v_a_5314_);
v___x_5326_ = v___x_5323_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_fvarId_5307_);
lean_ctor_set(v_reuseFailAlloc_5330_, 1, v_i_5308_);
lean_ctor_set(v_reuseFailAlloc_5330_, 2, v_offset_5309_);
lean_ctor_set(v_reuseFailAlloc_5330_, 3, v_y_5310_);
lean_ctor_set(v_reuseFailAlloc_5330_, 4, v_ty_5311_);
lean_ctor_set(v_reuseFailAlloc_5330_, 5, v_a_5314_);
v___x_5326_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
lean_object* v___x_5328_; 
if (v_isShared_5318_ == 0)
{
lean_ctor_set(v___x_5317_, 0, v___x_5326_);
v___x_5328_ = v___x_5317_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v___x_5326_);
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
lean_object* v___x_5339_; 
lean_dec(v_a_5314_);
if (v_isShared_5318_ == 0)
{
lean_ctor_set(v___x_5317_, 0, v_code_4932_);
v___x_5339_ = v___x_5317_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_code_4932_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
return v___x_5339_;
}
}
}
}
else
{
lean_object* v_a_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5350_; 
lean_dec(v_a_5314_);
lean_dec_ref_known(v_code_4932_, 6);
v_a_5343_ = lean_ctor_get(v___x_5315_, 0);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5345_ = v___x_5315_;
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_a_5343_);
lean_dec(v___x_5315_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v___x_5348_; 
if (v_isShared_5346_ == 0)
{
v___x_5348_ = v___x_5345_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_a_5343_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_4932_, 6);
return v___x_5313_;
}
}
default: 
{
lean_object* v___x_5351_; lean_object* v___x_5352_; 
lean_dec_ref(v_code_4932_);
v___x_5351_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1);
v___x_5352_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v___x_5351_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
return v___x_5352_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(lean_object* v_cases_5353_, size_t v_sz_5354_, size_t v_i_5355_, lean_object* v_bs_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_){
_start:
{
uint8_t v___x_5364_; 
v___x_5364_ = lean_usize_dec_lt(v_i_5355_, v_sz_5354_);
if (v___x_5364_ == 0)
{
lean_object* v___x_5365_; 
lean_dec_ref(v_cases_5353_);
v___x_5365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5365_, 0, v_bs_5356_);
return v___x_5365_;
}
else
{
lean_object* v_v_5366_; lean_object* v___x_5367_; lean_object* v_bs_x27_5368_; lean_object* v___x_5369_; lean_object* v_a_5371_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; 
v_v_5366_ = lean_array_uget(v_bs_5356_, v_i_5355_);
v___x_5367_ = lean_unsigned_to_nat(0u);
v_bs_x27_5368_ = lean_array_uset(v_bs_5356_, v_i_5355_, v___x_5367_);
v___x_5369_ = lean_st_ref_get(v___y_5358_);
v___x_5380_ = lean_st_ref_take(v___y_5358_);
lean_dec(v___x_5380_);
v___x_5381_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5382_ = lean_st_ref_put(v___y_5358_, v___x_5381_);
if (lean_obj_tag(v_v_5366_) == 1)
{
lean_object* v_info_5383_; lean_object* v_code_5384_; lean_object* v_discr_5385_; lean_object* v_resetTargets_5386_; lean_object* v_unconditionalBorrows_5387_; lean_object* v_derivedValMap_5388_; lean_object* v_varMap_5389_; lean_object* v_jpLiveVarMap_5390_; lean_object* v_idx_5391_; lean_object* v___y_5393_; lean_object* v___x_5408_; 
v_info_5383_ = lean_ctor_get(v_v_5366_, 0);
v_code_5384_ = lean_ctor_get(v_v_5366_, 1);
v_discr_5385_ = lean_ctor_get(v_cases_5353_, 2);
v_resetTargets_5386_ = lean_ctor_get(v___y_5357_, 0);
v_unconditionalBorrows_5387_ = lean_ctor_get(v___y_5357_, 1);
v_derivedValMap_5388_ = lean_ctor_get(v___y_5357_, 2);
v_varMap_5389_ = lean_ctor_get(v___y_5357_, 3);
v_jpLiveVarMap_5390_ = lean_ctor_get(v___y_5357_, 4);
v_idx_5391_ = lean_ctor_get(v___y_5357_, 5);
v___x_5408_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_varMap_5389_, v_discr_5385_);
if (lean_obj_tag(v___x_5408_) == 0)
{
lean_inc(v_varMap_5389_);
v___y_5393_ = v_varMap_5389_;
goto v___jp_5392_;
}
else
{
lean_object* v_val_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5430_; 
v_val_5409_ = lean_ctor_get(v___x_5408_, 0);
v_isSharedCheck_5430_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5430_ == 0)
{
v___x_5411_ = v___x_5408_;
v_isShared_5412_ = v_isSharedCheck_5430_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_val_5409_);
lean_dec(v___x_5408_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5430_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
uint8_t v_persistent_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5427_; 
v_persistent_5413_ = lean_ctor_get_uint8(v_val_5409_, sizeof(void*)*2 + 2);
v_isSharedCheck_5427_ = !lean_is_exclusive(v_val_5409_);
if (v_isSharedCheck_5427_ == 0)
{
lean_object* v_unused_5428_; lean_object* v_unused_5429_; 
v_unused_5428_ = lean_ctor_get(v_val_5409_, 1);
lean_dec(v_unused_5428_);
v_unused_5429_ = lean_ctor_get(v_val_5409_, 0);
lean_dec(v_unused_5429_);
v___x_5415_ = v_val_5409_;
v_isShared_5416_ = v_isSharedCheck_5427_;
goto v_resetjp_5414_;
}
else
{
lean_dec(v_val_5409_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5427_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
uint8_t v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5421_; 
v___x_5417_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_info_5383_);
v___x_5418_ = lean_unsigned_to_nat(1u);
v___x_5419_ = lean_nat_add(v_idx_5391_, v___x_5418_);
lean_inc_ref(v_info_5383_);
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 0, v_info_5383_);
v___x_5421_ = v___x_5411_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v_info_5383_);
v___x_5421_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
lean_object* v___x_5423_; 
if (v_isShared_5416_ == 0)
{
lean_ctor_set(v___x_5415_, 1, v___x_5421_);
lean_ctor_set(v___x_5415_, 0, v___x_5419_);
v___x_5423_ = v___x_5415_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v___x_5419_);
lean_ctor_set(v_reuseFailAlloc_5425_, 1, v___x_5421_);
lean_ctor_set_uint8(v_reuseFailAlloc_5425_, sizeof(void*)*2 + 2, v_persistent_5413_);
v___x_5423_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
lean_object* v___x_5424_; 
lean_ctor_set_uint8(v___x_5423_, sizeof(void*)*2, v___x_5417_);
lean_ctor_set_uint8(v___x_5423_, sizeof(void*)*2 + 1, v___x_5417_);
lean_inc(v_varMap_5389_);
lean_inc(v_discr_5385_);
v___x_5424_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_5385_, v___x_5423_, v_varMap_5389_);
v___y_5393_ = v___x_5424_;
goto v___jp_5392_;
}
}
}
}
}
v___jp_5392_:
{
lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5394_ = lean_unsigned_to_nat(1u);
v___x_5395_ = lean_nat_add(v_idx_5391_, v___x_5394_);
lean_inc(v_jpLiveVarMap_5390_);
lean_inc(v_derivedValMap_5388_);
lean_inc(v_unconditionalBorrows_5387_);
lean_inc_ref(v_resetTargets_5386_);
v___x_5396_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5396_, 0, v_resetTargets_5386_);
lean_ctor_set(v___x_5396_, 1, v_unconditionalBorrows_5387_);
lean_ctor_set(v___x_5396_, 2, v_derivedValMap_5388_);
lean_ctor_set(v___x_5396_, 3, v___y_5393_);
lean_ctor_set(v___x_5396_, 4, v_jpLiveVarMap_5390_);
lean_ctor_set(v___x_5396_, 5, v___x_5395_);
lean_inc_ref(v_code_5384_);
v___x_5397_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5384_, v___x_5396_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_);
lean_dec_ref_known(v___x_5396_, 6);
if (lean_obj_tag(v___x_5397_) == 0)
{
lean_object* v_a_5398_; lean_object* v___x_5399_; 
v_a_5398_ = lean_ctor_get(v___x_5397_, 0);
lean_inc(v_a_5398_);
lean_dec_ref_known(v___x_5397_, 1);
v___x_5399_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_5366_, v_a_5398_);
v_a_5371_ = v___x_5399_;
goto v___jp_5370_;
}
else
{
lean_object* v_a_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5407_; 
lean_dec_ref_known(v_v_5366_, 2);
lean_dec(v___x_5369_);
lean_dec_ref(v_bs_x27_5368_);
lean_dec_ref(v_cases_5353_);
v_a_5400_ = lean_ctor_get(v___x_5397_, 0);
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5397_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5402_ = v___x_5397_;
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_a_5400_);
lean_dec(v___x_5397_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5405_; 
if (v_isShared_5403_ == 0)
{
v___x_5405_ = v___x_5402_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_a_5400_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
}
}
else
{
lean_object* v_code_5431_; lean_object* v___x_5432_; 
v_code_5431_ = lean_ctor_get(v_v_5366_, 0);
lean_inc_ref(v_code_5431_);
v___x_5432_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5431_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_);
if (lean_obj_tag(v___x_5432_) == 0)
{
lean_object* v_a_5433_; lean_object* v___x_5434_; 
v_a_5433_ = lean_ctor_get(v___x_5432_, 0);
lean_inc(v_a_5433_);
lean_dec_ref_known(v___x_5432_, 1);
v___x_5434_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_5366_, v_a_5433_);
v_a_5371_ = v___x_5434_;
goto v___jp_5370_;
}
else
{
lean_object* v_a_5435_; lean_object* v___x_5437_; uint8_t v_isShared_5438_; uint8_t v_isSharedCheck_5442_; 
lean_dec_ref_known(v_v_5366_, 1);
lean_dec(v___x_5369_);
lean_dec_ref(v_bs_x27_5368_);
lean_dec_ref(v_cases_5353_);
v_a_5435_ = lean_ctor_get(v___x_5432_, 0);
v_isSharedCheck_5442_ = !lean_is_exclusive(v___x_5432_);
if (v_isSharedCheck_5442_ == 0)
{
v___x_5437_ = v___x_5432_;
v_isShared_5438_ = v_isSharedCheck_5442_;
goto v_resetjp_5436_;
}
else
{
lean_inc(v_a_5435_);
lean_dec(v___x_5432_);
v___x_5437_ = lean_box(0);
v_isShared_5438_ = v_isSharedCheck_5442_;
goto v_resetjp_5436_;
}
v_resetjp_5436_:
{
lean_object* v___x_5440_; 
if (v_isShared_5438_ == 0)
{
v___x_5440_ = v___x_5437_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v_a_5435_);
v___x_5440_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
return v___x_5440_;
}
}
}
}
v___jp_5370_:
{
lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; size_t v___x_5376_; size_t v___x_5377_; lean_object* v___x_5378_; 
v___x_5372_ = lean_st_ref_get(v___y_5358_);
v___x_5373_ = lean_st_ref_take(v___y_5358_);
lean_dec(v___x_5373_);
v___x_5374_ = lean_st_ref_put(v___y_5358_, v___x_5369_);
v___x_5375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5375_, 0, v_a_5371_);
lean_ctor_set(v___x_5375_, 1, v___x_5372_);
v___x_5376_ = ((size_t)1ULL);
v___x_5377_ = lean_usize_add(v_i_5355_, v___x_5376_);
v___x_5378_ = lean_array_uset(v_bs_x27_5368_, v_i_5355_, v___x_5375_);
v_i_5355_ = v___x_5377_;
v_bs_5356_ = v___x_5378_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6___boxed(lean_object* v_cases_5443_, lean_object* v_sz_5444_, lean_object* v_i_5445_, lean_object* v_bs_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_){
_start:
{
size_t v_sz_boxed_5454_; size_t v_i_boxed_5455_; lean_object* v_res_5456_; 
v_sz_boxed_5454_ = lean_unbox_usize(v_sz_5444_);
lean_dec(v_sz_5444_);
v_i_boxed_5455_ = lean_unbox_usize(v_i_5445_);
lean_dec(v_i_5445_);
v_res_5456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(v_cases_5443_, v_sz_boxed_5454_, v_i_boxed_5455_, v_bs_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
lean_dec(v___y_5450_);
lean_dec_ref(v___y_5449_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
return v_res_5456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___boxed(lean_object* v_code_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_){
_start:
{
lean_object* v_res_5465_; 
v_res_5465_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_);
lean_dec(v_a_5463_);
lean_dec_ref(v_a_5462_);
lean_dec(v_a_5461_);
lean_dec_ref(v_a_5460_);
lean_dec(v_a_5459_);
lean_dec_ref(v_a_5458_);
return v_res_5465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1(lean_object* v_00_u03b2_5466_, lean_object* v_m_5467_, lean_object* v_a_5468_, lean_object* v_b_5469_){
_start:
{
lean_object* v___x_5470_; 
v___x_5470_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(v_m_5467_, v_a_5468_, v_b_5469_);
return v___x_5470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_5471_, lean_object* v_a_5472_, lean_object* v_b_5473_, lean_object* v_x_5474_){
_start:
{
lean_object* v___x_5475_; 
v___x_5475_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(v_a_5472_, v_b_5473_, v_x_5474_);
return v___x_5475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(lean_object* v_decl_5476_, lean_object* v_code_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_){
_start:
{
lean_object* v_toSignature_5485_; lean_object* v_params_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; uint8_t v___x_5489_; 
v_toSignature_5485_ = lean_ctor_get(v_decl_5476_, 0);
v_params_5486_ = lean_ctor_get(v_toSignature_5485_, 3);
v___x_5487_ = lean_unsigned_to_nat(0u);
v___x_5488_ = lean_array_get_size(v_params_5486_);
v___x_5489_ = lean_nat_dec_lt(v___x_5487_, v___x_5488_);
if (v___x_5489_ == 0)
{
lean_object* v___x_5490_; 
v___x_5490_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_, v_a_5483_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; lean_object* v___x_5492_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_a_5491_);
lean_dec_ref_known(v___x_5490_, 1);
v___x_5492_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5486_, v_a_5491_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_, v_a_5483_);
return v___x_5492_;
}
else
{
return v___x_5490_;
}
}
else
{
size_t v___x_5493_; size_t v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; 
v___x_5493_ = ((size_t)0ULL);
v___x_5494_ = lean_usize_of_nat(v___x_5488_);
lean_inc_ref(v_a_5478_);
v___x_5495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_params_5486_, v___x_5493_, v___x_5494_, v_a_5478_);
v___x_5496_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5477_, v___x_5495_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_, v_a_5483_);
if (lean_obj_tag(v___x_5496_) == 0)
{
lean_object* v_a_5497_; lean_object* v___x_5498_; 
v_a_5497_ = lean_ctor_get(v___x_5496_, 0);
lean_inc(v_a_5497_);
lean_dec_ref_known(v___x_5496_, 1);
v___x_5498_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5486_, v_a_5497_, v___x_5495_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_, v_a_5483_);
lean_dec_ref(v___x_5495_);
return v___x_5498_;
}
else
{
lean_dec_ref(v___x_5495_);
return v___x_5496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go___boxed(lean_object* v_decl_5499_, lean_object* v_code_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_){
_start:
{
lean_object* v_res_5508_; 
v_res_5508_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(v_decl_5499_, v_code_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_);
lean_dec(v_a_5506_);
lean_dec_ref(v_a_5505_);
lean_dec(v_a_5504_);
lean_dec_ref(v_a_5503_);
lean_dec(v_a_5502_);
lean_dec_ref(v_a_5501_);
lean_dec_ref(v_decl_5499_);
return v_res_5508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(lean_object* v_f_5509_, lean_object* v_v_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_){
_start:
{
if (lean_obj_tag(v_v_5510_) == 0)
{
lean_object* v_code_5516_; lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5540_; 
v_code_5516_ = lean_ctor_get(v_v_5510_, 0);
v_isSharedCheck_5540_ = !lean_is_exclusive(v_v_5510_);
if (v_isSharedCheck_5540_ == 0)
{
v___x_5518_ = v_v_5510_;
v_isShared_5519_ = v_isSharedCheck_5540_;
goto v_resetjp_5517_;
}
else
{
lean_inc(v_code_5516_);
lean_dec(v_v_5510_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5540_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v___x_5520_; 
lean_inc(v___y_5514_);
lean_inc_ref(v___y_5513_);
lean_inc(v___y_5512_);
lean_inc_ref(v___y_5511_);
v___x_5520_ = lean_apply_6(v_f_5509_, v_code_5516_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_, lean_box(0));
if (lean_obj_tag(v___x_5520_) == 0)
{
lean_object* v_a_5521_; lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5531_; 
v_a_5521_ = lean_ctor_get(v___x_5520_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5523_ = v___x_5520_;
v_isShared_5524_ = v_isSharedCheck_5531_;
goto v_resetjp_5522_;
}
else
{
lean_inc(v_a_5521_);
lean_dec(v___x_5520_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5531_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v___x_5526_; 
if (v_isShared_5519_ == 0)
{
lean_ctor_set(v___x_5518_, 0, v_a_5521_);
v___x_5526_ = v___x_5518_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5521_);
v___x_5526_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
lean_object* v___x_5528_; 
if (v_isShared_5524_ == 0)
{
lean_ctor_set(v___x_5523_, 0, v___x_5526_);
v___x_5528_ = v___x_5523_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5526_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
else
{
lean_object* v_a_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5539_; 
lean_del_object(v___x_5518_);
v_a_5532_ = lean_ctor_get(v___x_5520_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5539_ == 0)
{
v___x_5534_ = v___x_5520_;
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5520_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5537_; 
if (v_isShared_5535_ == 0)
{
v___x_5537_ = v___x_5534_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
v___x_5537_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
return v___x_5537_;
}
}
}
}
}
else
{
lean_object* v___x_5541_; 
lean_dec_ref(v_f_5509_);
v___x_5541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5541_, 0, v_v_5510_);
return v___x_5541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg___boxed(lean_object* v_f_5542_, lean_object* v_v_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_){
_start:
{
lean_object* v_res_5549_; 
v_res_5549_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v_f_5542_, v_v_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_);
lean_dec(v___y_5547_);
lean_dec_ref(v___y_5546_);
lean_dec(v___y_5545_);
lean_dec_ref(v___y_5544_);
return v_res_5549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(uint8_t v_pu_5550_, lean_object* v_f_5551_, lean_object* v_v_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_){
_start:
{
lean_object* v___x_5558_; 
v___x_5558_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v_f_5551_, v_v_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_);
return v___x_5558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___boxed(lean_object* v_pu_5559_, lean_object* v_f_5560_, lean_object* v_v_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_){
_start:
{
uint8_t v_pu_boxed_5567_; lean_object* v_res_5568_; 
v_pu_boxed_5567_ = lean_unbox(v_pu_5559_);
v_res_5568_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(v_pu_boxed_5567_, v_f_5560_, v_v_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
lean_dec(v___y_5565_);
lean_dec_ref(v___y_5564_);
lean_dec(v___y_5563_);
lean_dec_ref(v___y_5562_);
return v_res_5568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(lean_object* v_decl_5569_, lean_object* v_code_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_){
_start:
{
lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; 
lean_inc_ref(v_code_5570_);
v___x_5576_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets(v_code_5570_);
v___x_5577_ = lean_box(0);
v___x_5578_ = lean_box(1);
v___x_5579_ = lean_unsigned_to_nat(0u);
v___x_5580_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5580_, 0, v___x_5576_);
lean_ctor_set(v___x_5580_, 1, v___x_5577_);
lean_ctor_set(v___x_5580_, 2, v___x_5578_);
lean_ctor_set(v___x_5580_, 3, v___x_5578_);
lean_ctor_set(v___x_5580_, 4, v___x_5578_);
lean_ctor_set(v___x_5580_, 5, v___x_5579_);
v___x_5581_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5582_ = lean_st_mk_ref(v___x_5581_);
v___x_5583_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(v_decl_5569_, v_code_5570_, v___x_5580_, v___x_5582_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_);
lean_dec_ref_known(v___x_5580_, 6);
if (lean_obj_tag(v___x_5583_) == 0)
{
lean_object* v_a_5584_; lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5592_; 
v_a_5584_ = lean_ctor_get(v___x_5583_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5583_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5586_ = v___x_5583_;
v_isShared_5587_ = v_isSharedCheck_5592_;
goto v_resetjp_5585_;
}
else
{
lean_inc(v_a_5584_);
lean_dec(v___x_5583_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5592_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5588_; lean_object* v___x_5590_; 
v___x_5588_ = lean_st_ref_get(v___x_5582_);
lean_dec(v___x_5582_);
lean_dec(v___x_5588_);
if (v_isShared_5587_ == 0)
{
v___x_5590_ = v___x_5586_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5584_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
return v___x_5590_;
}
}
}
else
{
lean_dec(v___x_5582_);
return v___x_5583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0___boxed(lean_object* v_decl_5593_, lean_object* v_code_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_){
_start:
{
lean_object* v_res_5600_; 
v_res_5600_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(v_decl_5593_, v_code_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_);
lean_dec(v___y_5598_);
lean_dec_ref(v___y_5597_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec_ref(v_decl_5593_);
return v_res_5600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(lean_object* v_decl_5601_, lean_object* v_a_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_){
_start:
{
lean_object* v_toSignature_5607_; lean_object* v_value_5608_; uint8_t v_recursive_5609_; lean_object* v_inlineAttr_x3f_5610_; lean_object* v___f_5611_; lean_object* v___x_5612_; 
v_toSignature_5607_ = lean_ctor_get(v_decl_5601_, 0);
lean_inc_ref(v_toSignature_5607_);
v_value_5608_ = lean_ctor_get(v_decl_5601_, 1);
lean_inc_ref(v_value_5608_);
v_recursive_5609_ = lean_ctor_get_uint8(v_decl_5601_, sizeof(void*)*3);
v_inlineAttr_x3f_5610_ = lean_ctor_get(v_decl_5601_, 2);
lean_inc(v_inlineAttr_x3f_5610_);
v___f_5611_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5611_, 0, v_decl_5601_);
v___x_5612_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v___f_5611_, v_value_5608_, v_a_5602_, v_a_5603_, v_a_5604_, v_a_5605_);
if (lean_obj_tag(v___x_5612_) == 0)
{
lean_object* v_a_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5621_; 
v_a_5613_ = lean_ctor_get(v___x_5612_, 0);
v_isSharedCheck_5621_ = !lean_is_exclusive(v___x_5612_);
if (v_isSharedCheck_5621_ == 0)
{
v___x_5615_ = v___x_5612_;
v_isShared_5616_ = v_isSharedCheck_5621_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_a_5613_);
lean_dec(v___x_5612_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5621_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v___x_5617_; lean_object* v___x_5619_; 
v___x_5617_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_5617_, 0, v_toSignature_5607_);
lean_ctor_set(v___x_5617_, 1, v_a_5613_);
lean_ctor_set(v___x_5617_, 2, v_inlineAttr_x3f_5610_);
lean_ctor_set_uint8(v___x_5617_, sizeof(void*)*3, v_recursive_5609_);
if (v_isShared_5616_ == 0)
{
lean_ctor_set(v___x_5615_, 0, v___x_5617_);
v___x_5619_ = v___x_5615_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v___x_5617_);
v___x_5619_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
return v___x_5619_;
}
}
}
else
{
lean_object* v_a_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5629_; 
lean_dec(v_inlineAttr_x3f_5610_);
lean_dec_ref(v_toSignature_5607_);
v_a_5622_ = lean_ctor_get(v___x_5612_, 0);
v_isSharedCheck_5629_ = !lean_is_exclusive(v___x_5612_);
if (v_isSharedCheck_5629_ == 0)
{
v___x_5624_ = v___x_5612_;
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_a_5622_);
lean_dec(v___x_5612_);
v___x_5624_ = lean_box(0);
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
v_resetjp_5623_:
{
lean_object* v___x_5627_; 
if (v_isShared_5625_ == 0)
{
v___x_5627_ = v___x_5624_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5628_; 
v_reuseFailAlloc_5628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5628_, 0, v_a_5622_);
v___x_5627_ = v_reuseFailAlloc_5628_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
return v___x_5627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___boxed(lean_object* v_decl_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_){
_start:
{
lean_object* v_res_5636_; 
v_res_5636_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(v_decl_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_);
lean_dec(v_a_5634_);
lean_dec_ref(v_a_5633_);
lean_dec(v_a_5632_);
lean_dec_ref(v_a_5631_);
return v_res_5636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(size_t v_sz_5637_, size_t v_i_5638_, lean_object* v_bs_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_){
_start:
{
uint8_t v___x_5645_; 
v___x_5645_ = lean_usize_dec_lt(v_i_5638_, v_sz_5637_);
if (v___x_5645_ == 0)
{
lean_object* v___x_5646_; 
v___x_5646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5646_, 0, v_bs_5639_);
return v___x_5646_;
}
else
{
lean_object* v_v_5647_; lean_object* v___x_5648_; lean_object* v_bs_x27_5649_; lean_object* v___x_5650_; 
v_v_5647_ = lean_array_uget(v_bs_5639_, v_i_5638_);
v___x_5648_ = lean_unsigned_to_nat(0u);
v_bs_x27_5649_ = lean_array_uset(v_bs_5639_, v_i_5638_, v___x_5648_);
v___x_5650_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(v_v_5647_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_);
if (lean_obj_tag(v___x_5650_) == 0)
{
lean_object* v_a_5651_; size_t v___x_5652_; size_t v___x_5653_; lean_object* v___x_5654_; 
v_a_5651_ = lean_ctor_get(v___x_5650_, 0);
lean_inc(v_a_5651_);
lean_dec_ref_known(v___x_5650_, 1);
v___x_5652_ = ((size_t)1ULL);
v___x_5653_ = lean_usize_add(v_i_5638_, v___x_5652_);
v___x_5654_ = lean_array_uset(v_bs_x27_5649_, v_i_5638_, v_a_5651_);
v_i_5638_ = v___x_5653_;
v_bs_5639_ = v___x_5654_;
goto _start;
}
else
{
lean_object* v_a_5656_; lean_object* v___x_5658_; uint8_t v_isShared_5659_; uint8_t v_isSharedCheck_5663_; 
lean_dec_ref(v_bs_x27_5649_);
v_a_5656_ = lean_ctor_get(v___x_5650_, 0);
v_isSharedCheck_5663_ = !lean_is_exclusive(v___x_5650_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5658_ = v___x_5650_;
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
else
{
lean_inc(v_a_5656_);
lean_dec(v___x_5650_);
v___x_5658_ = lean_box(0);
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
v_resetjp_5657_:
{
lean_object* v___x_5661_; 
if (v_isShared_5659_ == 0)
{
v___x_5661_ = v___x_5658_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_a_5656_);
v___x_5661_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
return v___x_5661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0___boxed(lean_object* v_sz_5664_, lean_object* v_i_5665_, lean_object* v_bs_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_){
_start:
{
size_t v_sz_boxed_5672_; size_t v_i_boxed_5673_; lean_object* v_res_5674_; 
v_sz_boxed_5672_ = lean_unbox_usize(v_sz_5664_);
lean_dec(v_sz_5664_);
v_i_boxed_5673_ = lean_unbox_usize(v_i_5665_);
lean_dec(v_i_5665_);
v_res_5674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(v_sz_boxed_5672_, v_i_boxed_5673_, v_bs_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_);
lean_dec(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v___y_5668_);
lean_dec_ref(v___y_5667_);
return v_res_5674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc(lean_object* v_decls_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_){
_start:
{
size_t v_sz_5681_; size_t v___x_5682_; lean_object* v___x_5683_; 
v_sz_5681_ = lean_array_size(v_decls_5675_);
v___x_5682_ = ((size_t)0ULL);
v___x_5683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(v_sz_5681_, v___x_5682_, v_decls_5675_, v_a_5676_, v_a_5677_, v_a_5678_, v_a_5679_);
return v___x_5683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc___boxed(lean_object* v_decls_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_){
_start:
{
lean_object* v_res_5690_; 
v_res_5690_ = l_Lean_Compiler_LCNF_runExplicitRc(v_decls_5684_, v_a_5685_, v_a_5686_, v_a_5687_, v_a_5688_);
lean_dec(v_a_5688_);
lean_dec_ref(v_a_5687_);
lean_dec(v_a_5686_);
lean_dec_ref(v_a_5685_);
return v_res_5690_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_explicitRc___closed__3(void){
_start:
{
lean_object* v___x_5695_; lean_object* v___x_5696_; uint8_t v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; 
v___x_5695_ = lean_unsigned_to_nat(0u);
v___x_5696_ = ((lean_object*)(l_Lean_Compiler_LCNF_explicitRc___closed__2));
v___x_5697_ = 2;
v___x_5698_ = ((lean_object*)(l_Lean_Compiler_LCNF_explicitRc___closed__1));
v___x_5699_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_5698_, v___x_5697_, v___x_5696_, v___x_5695_);
return v___x_5699_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_explicitRc(void){
_start:
{
lean_object* v___x_5700_; 
v___x_5700_ = lean_obj_once(&l_Lean_Compiler_LCNF_explicitRc___closed__3, &l_Lean_Compiler_LCNF_explicitRc___closed__3_once, _init_l_Lean_Compiler_LCNF_explicitRc___closed__3);
return v___x_5700_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; 
v___x_5756_ = lean_unsigned_to_nat(3791338971u);
v___x_5757_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5758_ = l_Lean_Name_num___override(v___x_5757_, v___x_5756_);
return v___x_5758_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; 
v___x_5760_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5761_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5762_ = l_Lean_Name_str___override(v___x_5761_, v___x_5760_);
return v___x_5762_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; 
v___x_5764_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5765_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5766_ = l_Lean_Name_str___override(v___x_5765_, v___x_5764_);
return v___x_5766_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; 
v___x_5767_ = lean_unsigned_to_nat(2u);
v___x_5768_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5769_ = l_Lean_Name_num___override(v___x_5768_, v___x_5767_);
return v___x_5769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5771_; uint8_t v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; 
v___x_5771_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5772_ = 1;
v___x_5773_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5774_ = l_Lean_registerTraceClass(v___x_5771_, v___x_5772_, v___x_5773_);
return v___x_5774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2____boxed(lean_object* v_a_5775_){
_start:
{
lean_object* v_res_5776_; 
v_res_5776_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_();
return v_res_5776_;
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
