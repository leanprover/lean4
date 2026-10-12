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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(lean_object* v_a_4_, lean_object* v_x_5_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4_ = stack[0].m_obj;
lean_object* v_x_5_ = stack[1].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_4_, v_x_5_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_12_, lean_object* v_x_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_12_, v_x_13_);
lean_dec(v_x_13_);
lean_dec(v_a_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
return v_x_16_;
}
else
{
lean_object* v_key_18_; lean_object* v_value_19_; lean_object* v_tail_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_43_; 
v_key_18_ = lean_ctor_get(v_x_17_, 0);
v_value_19_ = lean_ctor_get(v_x_17_, 1);
v_tail_20_ = lean_ctor_get(v_x_17_, 2);
v_isSharedCheck_43_ = !lean_is_exclusive(v_x_17_);
if (v_isSharedCheck_43_ == 0)
{
v___x_22_ = v_x_17_;
v_isShared_23_ = v_isSharedCheck_43_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_tail_20_);
lean_inc(v_value_19_);
lean_inc(v_key_18_);
lean_dec(v_x_17_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_43_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; uint64_t v_fold_28_; uint64_t v___x_29_; uint64_t v___x_30_; uint64_t v___x_31_; size_t v___x_32_; size_t v___x_33_; size_t v___x_34_; size_t v___x_35_; size_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_24_ = lean_array_get_size(v_x_16_);
v___x_25_ = l_Lean_instHashableFVarId_hash(v_key_18_);
v___x_26_ = 32ULL;
v___x_27_ = lean_uint64_shift_right(v___x_25_, v___x_26_);
v_fold_28_ = lean_uint64_xor(v___x_25_, v___x_27_);
v___x_29_ = 16ULL;
v___x_30_ = lean_uint64_shift_right(v_fold_28_, v___x_29_);
v___x_31_ = lean_uint64_xor(v_fold_28_, v___x_30_);
v___x_32_ = lean_uint64_to_usize(v___x_31_);
v___x_33_ = lean_usize_of_nat(v___x_24_);
v___x_34_ = ((size_t)1ULL);
v___x_35_ = lean_usize_sub(v___x_33_, v___x_34_);
v___x_36_ = lean_usize_land(v___x_32_, v___x_35_);
v___x_37_ = lean_array_uget_borrowed(v_x_16_, v___x_36_);
lean_inc(v___x_37_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 2, v___x_37_);
v___x_39_ = v___x_22_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_key_18_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_value_19_);
lean_ctor_set(v_reuseFailAlloc_42_, 2, v___x_37_);
v___x_39_ = v_reuseFailAlloc_42_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_40_; 
v___x_40_ = lean_array_uset(v_x_16_, v___x_36_, v___x_39_);
v_x_16_ = v___x_40_;
v_x_17_ = v_tail_20_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3___redArg(lean_object* v_i_44_, lean_object* v_source_45_, lean_object* v_target_46_){
_start:
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = lean_array_get_size(v_source_45_);
v___x_48_ = lean_nat_dec_lt(v_i_44_, v___x_47_);
if (v___x_48_ == 0)
{
lean_dec_ref(v_source_45_);
lean_dec(v_i_44_);
return v_target_46_;
}
else
{
lean_object* v_es_49_; lean_object* v___x_50_; lean_object* v_source_51_; lean_object* v_target_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_es_49_ = lean_array_fget(v_source_45_, v_i_44_);
v___x_50_ = lean_box(0);
v_source_51_ = lean_array_fset(v_source_45_, v_i_44_, v___x_50_);
v_target_52_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5___redArg(v_target_46_, v_es_49_);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_add(v_i_44_, v___x_53_);
lean_dec(v_i_44_);
v_i_44_ = v___x_54_;
v_source_45_ = v_source_51_;
v_target_46_ = v_target_52_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(lean_object* v_data_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v_nbuckets_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_57_ = lean_array_get_size(v_data_56_);
v___x_58_ = lean_unsigned_to_nat(2u);
v_nbuckets_59_ = lean_nat_mul(v___x_57_, v___x_58_);
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = lean_box(0);
v___x_62_ = lean_mk_array(v_nbuckets_59_, v___x_61_);
v___x_63_ = lean_array_propagate_mark(v_data_56_, v___x_62_);
v___x_64_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3___redArg(v___x_60_, v_data_56_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(lean_object* v_m_65_, lean_object* v_a_66_, lean_object* v_b_67_){
_start:
{
lean_object* v_size_68_; lean_object* v_buckets_69_; lean_object* v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v_fold_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; size_t v___x_78_; size_t v___x_79_; size_t v___x_80_; size_t v___x_81_; size_t v___x_82_; lean_object* v_bkt_83_; uint8_t v___x_84_; 
v_size_68_ = lean_ctor_get(v_m_65_, 0);
v_buckets_69_ = lean_ctor_get(v_m_65_, 1);
v___x_70_ = lean_array_get_size(v_buckets_69_);
v___x_71_ = l_Lean_instHashableFVarId_hash(v_a_66_);
v___x_72_ = 32ULL;
v___x_73_ = lean_uint64_shift_right(v___x_71_, v___x_72_);
v_fold_74_ = lean_uint64_xor(v___x_71_, v___x_73_);
v___x_75_ = 16ULL;
v___x_76_ = lean_uint64_shift_right(v_fold_74_, v___x_75_);
v___x_77_ = lean_uint64_xor(v_fold_74_, v___x_76_);
v___x_78_ = lean_uint64_to_usize(v___x_77_);
v___x_79_ = lean_usize_of_nat(v___x_70_);
v___x_80_ = ((size_t)1ULL);
v___x_81_ = lean_usize_sub(v___x_79_, v___x_80_);
v___x_82_ = lean_usize_land(v___x_78_, v___x_81_);
v_bkt_83_ = lean_array_uget_borrowed(v_buckets_69_, v___x_82_);
v___x_84_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_66_, v_bkt_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_105_; 
lean_inc_ref(v_buckets_69_);
lean_inc(v_size_68_);
v_isSharedCheck_105_ = !lean_is_exclusive(v_m_65_);
if (v_isSharedCheck_105_ == 0)
{
lean_object* v_unused_106_; lean_object* v_unused_107_; 
v_unused_106_ = lean_ctor_get(v_m_65_, 1);
lean_dec(v_unused_106_);
v_unused_107_ = lean_ctor_get(v_m_65_, 0);
lean_dec(v_unused_107_);
v___x_86_ = v_m_65_;
v_isShared_87_ = v_isSharedCheck_105_;
goto v_resetjp_85_;
}
else
{
lean_dec(v_m_65_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_105_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v_size_x27_89_; lean_object* v___x_90_; lean_object* v_buckets_x27_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_88_ = lean_unsigned_to_nat(1u);
v_size_x27_89_ = lean_nat_add(v_size_68_, v___x_88_);
lean_dec(v_size_68_);
lean_inc(v_bkt_83_);
v___x_90_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_90_, 0, v_a_66_);
lean_ctor_set(v___x_90_, 1, v_b_67_);
lean_ctor_set(v___x_90_, 2, v_bkt_83_);
v_buckets_x27_91_ = lean_array_uset(v_buckets_69_, v___x_82_, v___x_90_);
v___x_92_ = lean_unsigned_to_nat(4u);
v___x_93_ = lean_nat_mul(v_size_x27_89_, v___x_92_);
v___x_94_ = lean_unsigned_to_nat(3u);
v___x_95_ = lean_nat_div(v___x_93_, v___x_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_array_get_size(v_buckets_x27_91_);
v___x_97_ = lean_nat_dec_le(v___x_95_, v___x_96_);
lean_dec(v___x_95_);
if (v___x_97_ == 0)
{
lean_object* v_val_98_; lean_object* v___x_100_; 
v_val_98_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(v_buckets_x27_91_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v_val_98_);
lean_ctor_set(v___x_86_, 0, v_size_x27_89_);
v___x_100_ = v___x_86_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_size_x27_89_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_val_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
else
{
lean_object* v___x_103_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v_buckets_x27_91_);
lean_ctor_set(v___x_86_, 0, v_size_x27_89_);
v___x_103_ = v___x_86_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_size_x27_89_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_buckets_x27_91_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
else
{
lean_dec(v_b_67_);
lean_dec(v_a_66_);
return v_m_65_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_112_ = lean_unsigned_to_nat(61u);
v___x_113_ = lean_unsigned_to_nat(49u);
v___x_114_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__1));
v___x_115_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_116_ = l_mkPanicMessageWithDecl(v___x_115_, v___x_114_, v___x_113_, v___x_112_, v___x_111_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(lean_object* v_code_117_, lean_object* v_s_118_){
_start:
{
switch(lean_obj_tag(v_code_117_))
{
case 0:
{
lean_object* v_decl_119_; lean_object* v_value_120_; 
v_decl_119_ = lean_ctor_get(v_code_117_, 0);
v_value_120_ = lean_ctor_get(v_decl_119_, 3);
if (lean_obj_tag(v_value_120_) == 11)
{
lean_object* v_k_121_; lean_object* v_var_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_inc_ref(v_value_120_);
v_k_121_ = lean_ctor_get(v_code_117_, 1);
lean_inc_ref(v_k_121_);
lean_dec_ref_known(v_code_117_, 2);
v_var_122_ = lean_ctor_get(v_value_120_, 1);
lean_inc(v_var_122_);
lean_dec_ref_known(v_value_120_, 2);
v___x_123_ = lean_box(0);
v___x_124_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_s_118_, v_var_122_, v___x_123_);
v_code_117_ = v_k_121_;
v_s_118_ = v___x_124_;
goto _start;
}
else
{
lean_object* v_k_126_; 
v_k_126_ = lean_ctor_get(v_code_117_, 1);
lean_inc_ref(v_k_126_);
lean_dec_ref_known(v_code_117_, 2);
v_code_117_ = v_k_126_;
goto _start;
}
}
case 2:
{
lean_object* v_decl_128_; lean_object* v_k_129_; lean_object* v_value_130_; lean_object* v___x_131_; 
v_decl_128_ = lean_ctor_get(v_code_117_, 0);
lean_inc_ref(v_decl_128_);
v_k_129_ = lean_ctor_get(v_code_117_, 1);
lean_inc_ref(v_k_129_);
lean_dec_ref_known(v_code_117_, 2);
v_value_130_ = lean_ctor_get(v_decl_128_, 4);
lean_inc_ref(v_value_130_);
lean_dec_ref(v_decl_128_);
v___x_131_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(v_value_130_, v_s_118_);
v_code_117_ = v_k_129_;
v_s_118_ = v___x_131_;
goto _start;
}
case 3:
{
lean_dec_ref_known(v_code_117_, 2);
return v_s_118_;
}
case 4:
{
lean_object* v_cases_133_; lean_object* v_alts_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_cases_133_ = lean_ctor_get(v_code_117_, 0);
lean_inc_ref(v_cases_133_);
lean_dec_ref_known(v_code_117_, 1);
v_alts_134_ = lean_ctor_get(v_cases_133_, 3);
lean_inc_ref(v_alts_134_);
lean_dec_ref(v_cases_133_);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_array_get_size(v_alts_134_);
v___x_137_ = lean_nat_dec_lt(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_dec_ref(v_alts_134_);
return v_s_118_;
}
else
{
uint8_t v___x_138_; 
v___x_138_ = lean_nat_dec_le(v___x_136_, v___x_136_);
if (v___x_138_ == 0)
{
if (v___x_137_ == 0)
{
lean_dec_ref(v_alts_134_);
return v_s_118_;
}
else
{
size_t v___x_139_; size_t v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((size_t)0ULL);
v___x_140_ = lean_usize_of_nat(v___x_136_);
v___x_141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(v_alts_134_, v___x_139_, v___x_140_, v_s_118_);
lean_dec_ref(v_alts_134_);
return v___x_141_;
}
}
else
{
size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; 
v___x_142_ = ((size_t)0ULL);
v___x_143_ = lean_usize_of_nat(v___x_136_);
v___x_144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(v_alts_134_, v___x_142_, v___x_143_, v_s_118_);
lean_dec_ref(v_alts_134_);
return v___x_144_;
}
}
}
case 5:
{
lean_dec_ref_known(v_code_117_, 1);
return v_s_118_;
}
case 6:
{
lean_dec_ref_known(v_code_117_, 1);
return v_s_118_;
}
case 8:
{
lean_object* v_k_145_; 
v_k_145_ = lean_ctor_get(v_code_117_, 3);
lean_inc_ref(v_k_145_);
lean_dec_ref_known(v_code_117_, 4);
v_code_117_ = v_k_145_;
goto _start;
}
case 9:
{
lean_object* v_k_147_; 
v_k_147_ = lean_ctor_get(v_code_117_, 5);
lean_inc_ref(v_k_147_);
lean_dec_ref_known(v_code_117_, 6);
v_code_117_ = v_k_147_;
goto _start;
}
default: 
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec_ref(v_s_118_);
lean_dec_ref(v_code_117_);
v___x_149_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3);
v___x_150_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__2(v___x_149_);
return v___x_150_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(lean_object* v_as_151_, size_t v_i_152_, size_t v_stop_153_, lean_object* v_b_154_){
_start:
{
lean_object* v___y_156_; uint8_t v___x_161_; 
v___x_161_ = lean_usize_dec_eq(v_i_152_, v_stop_153_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
v___x_162_ = lean_array_uget_borrowed(v_as_151_, v_i_152_);
switch(lean_obj_tag(v___x_162_))
{
case 0:
{
lean_object* v_code_163_; 
v_code_163_ = lean_ctor_get(v___x_162_, 2);
lean_inc_ref(v_code_163_);
v___y_156_ = v_code_163_;
goto v___jp_155_;
}
case 1:
{
lean_object* v_code_164_; 
v_code_164_ = lean_ctor_get(v___x_162_, 1);
lean_inc_ref(v_code_164_);
v___y_156_ = v_code_164_;
goto v___jp_155_;
}
default: 
{
lean_object* v_code_165_; 
v_code_165_ = lean_ctor_get(v___x_162_, 0);
lean_inc_ref(v_code_165_);
v___y_156_ = v_code_165_;
goto v___jp_155_;
}
}
}
else
{
return v_b_154_;
}
v___jp_155_:
{
lean_object* v___x_157_; size_t v___x_158_; size_t v___x_159_; 
v___x_157_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(v___y_156_, v_b_154_);
v___x_158_ = ((size_t)1ULL);
v___x_159_ = lean_usize_add(v_i_152_, v___x_158_);
v_i_152_ = v___x_159_;
v_b_154_ = v___x_157_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_151_ = stack[0].m_obj;
size_t v_i_152_ = stack[1].m_num;
size_t v_stop_153_ = stack[2].m_num;
lean_object* v_b_154_ = stack[3].m_obj;
lean_object* v_res_166_;
v_res_166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(v_as_151_, v_i_152_, v_stop_153_, v_b_154_);
stack->m_obj
 = v_res_166_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1___boxed(lean_object* v_as_167_, lean_object* v_i_168_, lean_object* v_stop_169_, lean_object* v_b_170_){
_start:
{
size_t v_i_boxed_171_; size_t v_stop_boxed_172_; lean_object* v_res_173_; 
v_i_boxed_171_ = lean_unbox_usize(v_i_168_);
lean_dec(v_i_168_);
v_stop_boxed_172_ = lean_unbox_usize(v_stop_169_);
lean_dec(v_stop_169_);
v_res_173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(v_as_167_, v_i_boxed_171_, v_stop_boxed_172_, v_b_170_);
lean_dec_ref(v_as_167_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0(lean_object* v_00_u03b2_174_, lean_object* v_m_175_, lean_object* v_a_176_, lean_object* v_b_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_m_175_, v_a_176_, v_b_177_);
return v___x_178_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0(lean_object* v_00_u03b2_179_, lean_object* v_a_180_, lean_object* v_x_181_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_180_, v_x_181_);
return v___x_182_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_180_ = stack[1].m_obj;
lean_object* v_x_181_ = stack[2].m_obj;
uint8_t v_res_183_;
v_res_183_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0(lean_box(0), v_a_180_, v_x_181_);
stack->m_num = v_res_183_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_184_, lean_object* v_a_185_, lean_object* v_x_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0(v_00_u03b2_184_, v_a_185_, v_x_186_);
lean_dec(v_x_186_);
lean_dec(v_a_185_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1(lean_object* v_00_u03b2_189_, lean_object* v_data_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(v_data_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_192_, lean_object* v_i_193_, lean_object* v_source_194_, lean_object* v_target_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3___redArg(v_i_193_, v_source_194_, v_target_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_197_, lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5___redArg(v_x_198_, v_x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets(lean_object* v_code_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_203_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(v_code_201_, v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_box(0);
v___x_211_ = lean_unsigned_to_nat(16u);
v___x_212_ = lean_mk_array(v___x_211_, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
return v___x_218_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars(void){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__0(lean_object* v___x_220_, lean_object* v___x_221_, lean_object* v_a_222_, lean_object* v_b_223_, lean_object* v_acc_224_){
_start:
{
lean_object* v_r_225_; lean_object* v___x_226_; 
v_r_225_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_220_, v___x_221_, v_acc_224_, v_a_222_, v_b_223_);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v_r_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__1(lean_object* v___x_227_, lean_object* v___f_228_, lean_object* v_a_229_, lean_object* v_x_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_227_, v___f_228_, v_a_229_, v___y_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union(lean_object* v_liveVars1_262_, lean_object* v_liveVars2_263_){
_start:
{
lean_object* v_vars_264_; lean_object* v_borrows_265_; lean_object* v_vars_266_; lean_object* v_borrows_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_302_; 
v_vars_264_ = lean_ctor_get(v_liveVars1_262_, 0);
lean_inc_ref(v_vars_264_);
v_borrows_265_ = lean_ctor_get(v_liveVars1_262_, 1);
lean_inc_ref(v_borrows_265_);
lean_dec_ref(v_liveVars1_262_);
v_vars_266_ = lean_ctor_get(v_liveVars2_263_, 0);
v_borrows_267_ = lean_ctor_get(v_liveVars2_263_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v_liveVars2_263_);
if (v_isSharedCheck_302_ == 0)
{
v___x_269_ = v_liveVars2_263_;
v_isShared_270_ = v_isSharedCheck_302_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_borrows_267_);
lean_inc(v_vars_266_);
lean_dec(v_liveVars2_263_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_302_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v_size_272_; lean_object* v_buckets_273_; lean_object* v_size_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___y_278_; uint8_t v___x_295_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v_size_272_ = lean_ctor_get(v_vars_264_, 0);
v_buckets_273_ = lean_ctor_get(v_vars_264_, 1);
v_size_274_ = lean_ctor_get(v_vars_266_, 0);
v___x_275_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_276_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_295_ = lean_nat_dec_le(v_size_272_, v_size_274_);
if (v___x_295_ == 0)
{
lean_object* v___f_296_; lean_object* v___x_297_; 
v___f_296_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__13));
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_296_, v___x_275_, v___x_276_, v_vars_264_, v_vars_266_);
v___y_278_ = v___x_297_;
goto v___jp_277_;
}
else
{
lean_object* v___f_298_; size_t v_sz_299_; size_t v___x_300_; lean_object* v___x_301_; 
lean_inc_ref(v_buckets_273_);
lean_dec_ref(v_vars_264_);
v___f_298_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__14));
v_sz_299_ = lean_array_size(v_buckets_273_);
v___x_300_ = ((size_t)0ULL);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_271_, v_buckets_273_, v___f_298_, v_sz_299_, v___x_300_, v_vars_266_);
v___y_278_ = v___x_301_;
goto v___jp_277_;
}
v___jp_277_:
{
lean_object* v_size_279_; lean_object* v_buckets_280_; lean_object* v_size_281_; uint8_t v___x_282_; 
v_size_279_ = lean_ctor_get(v_borrows_265_, 0);
v_buckets_280_ = lean_ctor_get(v_borrows_265_, 1);
v_size_281_ = lean_ctor_get(v_borrows_267_, 0);
v___x_282_ = lean_nat_dec_le(v_size_279_, v_size_281_);
if (v___x_282_ == 0)
{
lean_object* v___f_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___f_283_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__13));
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_283_, v___x_275_, v___x_276_, v_borrows_265_, v_borrows_267_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_284_);
lean_ctor_set(v___x_269_, 0, v___y_278_);
v___x_286_ = v___x_269_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___y_278_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
else
{
lean_object* v___f_288_; size_t v_sz_289_; size_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
lean_inc_ref(v_buckets_280_);
lean_dec_ref(v_borrows_265_);
v___f_288_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__14));
v_sz_289_ = lean_array_size(v_buckets_280_);
v___x_290_ = ((size_t)0ULL);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_271_, v_buckets_280_, v___f_288_, v_sz_289_, v___x_290_, v_borrows_267_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_291_);
lean_ctor_set(v___x_269_, 0, v___y_278_);
v___x_293_ = v___x_269_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___y_278_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_erase(lean_object* v_liveVars_303_, lean_object* v_fvarId_304_){
_start:
{
lean_object* v_vars_305_; lean_object* v_borrows_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_317_; 
v_vars_305_ = lean_ctor_get(v_liveVars_303_, 0);
v_borrows_306_ = lean_ctor_get(v_liveVars_303_, 1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_liveVars_303_);
if (v_isSharedCheck_317_ == 0)
{
v___x_308_ = v_liveVars_303_;
v_isShared_309_ = v_isSharedCheck_317_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_borrows_306_);
lean_inc(v_vars_305_);
lean_dec(v_liveVars_303_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_317_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_vars_312_; lean_object* v_borrows_313_; lean_object* v___x_315_; 
v___x_310_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_311_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
lean_inc(v_fvarId_304_);
v_vars_312_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_310_, v___x_311_, v_vars_305_, v_fvarId_304_);
v_borrows_313_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_310_, v___x_311_, v_borrows_306_, v_fvarId_304_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v_borrows_313_);
lean_ctor_set(v___x_308_, 0, v_vars_312_);
v___x_315_ = v___x_308_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_vars_312_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_borrows_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_insertBorrow(lean_object* v_liveVars_318_, lean_object* v_fvarId_319_){
_start:
{
lean_object* v_vars_320_; lean_object* v_borrows_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_332_; 
v_vars_320_ = lean_ctor_get(v_liveVars_318_, 0);
v_borrows_321_ = lean_ctor_get(v_liveVars_318_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_liveVars_318_);
if (v_isSharedCheck_332_ == 0)
{
v___x_323_ = v_liveVars_318_;
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_borrows_321_);
lean_inc(v_vars_320_);
lean_dec(v_liveVars_318_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_325_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_326_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_327_ = lean_box(0);
v___x_328_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_325_, v___x_326_, v_borrows_321_, v_fvarId_319_, v___x_327_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_328_);
v___x_330_ = v___x_323_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_vars_320_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_insertLive(lean_object* v_liveVars_333_, lean_object* v_fvarId_334_){
_start:
{
lean_object* v_vars_335_; lean_object* v_borrows_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_347_; 
v_vars_335_ = lean_ctor_get(v_liveVars_333_, 0);
v_borrows_336_ = lean_ctor_get(v_liveVars_333_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_liveVars_333_);
if (v_isSharedCheck_347_ == 0)
{
v___x_338_ = v_liveVars_333_;
v_isShared_339_ = v_isSharedCheck_347_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_borrows_336_);
lean_inc(v_vars_335_);
lean_dec(v_liveVars_333_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_347_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_340_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_341_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_342_ = lean_box(0);
v___x_343_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_340_, v___x_341_, v_vars_335_, v_fvarId_334_, v___x_342_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_343_);
v___x_345_ = v___x_338_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_borrows_336_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(lean_object* v_fvarId_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_varMap_359_; lean_object* v___f_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_varMap_359_ = lean_ctor_get(v_a_357_, 3);
v___f_360_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_361_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_varMap_359_);
v___x_362_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_360_, v___x_361_, v_varMap_359_, v_fvarId_356_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_356_ = stack[0].m_obj;
lean_object* v_a_357_ = stack[1].m_obj;
lean_object* v_res_364_;
v_res_364_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(v_fvarId_356_, v_a_357_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___boxed(lean_object* v_fvarId_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(v_fvarId_365_, v_a_366_);
lean_dec_ref(v_a_366_);
return v_res_368_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(lean_object* v_fvarId_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_varMap_377_; lean_object* v___f_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_varMap_377_ = lean_ctor_get(v_a_370_, 3);
v___f_378_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_379_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_varMap_377_);
v___x_380_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_378_, v___x_379_, v_varMap_377_, v_fvarId_369_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_369_ = stack[0].m_obj;
lean_object* v_a_370_ = stack[1].m_obj;
lean_object* v_a_371_ = stack[2].m_obj;
lean_object* v_a_372_ = stack[3].m_obj;
lean_object* v_a_373_ = stack[4].m_obj;
lean_object* v_a_374_ = stack[5].m_obj;
lean_object* v_a_375_ = stack[6].m_obj;
lean_object* v_res_382_;
v_res_382_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(v_fvarId_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___boxed(lean_object* v_fvarId_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(v_fvarId_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
return v_res_391_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(lean_object* v_fvarId_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_jpLiveVarMap_395_; lean_object* v___f_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_jpLiveVarMap_395_ = lean_ctor_get(v_a_393_, 4);
v___f_396_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_397_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
lean_inc(v_jpLiveVarMap_395_);
v___x_398_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_396_, v___x_397_, v_jpLiveVarMap_395_, v_fvarId_392_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_392_ = stack[0].m_obj;
lean_object* v_a_393_ = stack[1].m_obj;
lean_object* v_res_400_;
v_res_400_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(v_fvarId_392_, v_a_393_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg___boxed(lean_object* v_fvarId_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(v_fvarId_401_, v_a_402_);
lean_dec_ref(v_a_402_);
return v_res_404_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(lean_object* v_fvarId_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_jpLiveVarMap_413_; lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_jpLiveVarMap_413_ = lean_ctor_get(v_a_406_, 4);
v___f_414_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_415_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
lean_inc(v_jpLiveVarMap_413_);
v___x_416_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_414_, v___x_415_, v_jpLiveVarMap_413_, v_fvarId_405_);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_405_ = stack[0].m_obj;
lean_object* v_a_406_ = stack[1].m_obj;
lean_object* v_a_407_ = stack[2].m_obj;
lean_object* v_a_408_ = stack[3].m_obj;
lean_object* v_a_409_ = stack[4].m_obj;
lean_object* v_a_410_ = stack[5].m_obj;
lean_object* v_a_411_ = stack[6].m_obj;
lean_object* v_res_418_;
v_res_418_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(v_fvarId_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
stack->m_obj
 = v_res_418_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___boxed(lean_object* v_fvarId_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(v_fvarId_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
return v_res_427_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg(lean_object* v_fvarId_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v_vars_434_; uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_431_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_432_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_433_ = lean_st_ref_get(v_a_429_);
v_vars_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc_ref(v_vars_434_);
lean_dec(v___x_433_);
v___x_435_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_431_, v___x_432_, v_vars_434_, v_fvarId_428_);
lean_dec_ref(v_vars_434_);
v___x_436_ = lean_box(v___x_435_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_428_ = stack[0].m_obj;
lean_object* v_a_429_ = stack[1].m_obj;
lean_object* v_res_438_;
v_res_438_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg(v_fvarId_428_, v_a_429_);
stack->m_obj
 = v_res_438_;
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
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(lean_object* v_fvarId_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
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
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_443_ = stack[0].m_obj;
lean_object* v_a_444_ = stack[1].m_obj;
lean_object* v_a_445_ = stack[2].m_obj;
lean_object* v_a_446_ = stack[3].m_obj;
lean_object* v_a_447_ = stack[4].m_obj;
lean_object* v_a_448_ = stack[5].m_obj;
lean_object* v_a_449_ = stack[6].m_obj;
lean_object* v_res_458_;
v_res_458_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(v_fvarId_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
stack->m_obj
 = v_res_458_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___boxed(lean_object* v_fvarId_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(v_fvarId_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
return v_res_467_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(lean_object* v_fvarId_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_borrows_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_471_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_472_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_473_ = lean_st_ref_get(v_a_469_);
v_borrows_474_ = lean_ctor_get(v___x_473_, 1);
lean_inc_ref(v_borrows_474_);
lean_dec(v___x_473_);
v___x_475_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_471_, v___x_472_, v_borrows_474_, v_fvarId_468_);
lean_dec_ref(v_borrows_474_);
v___x_476_ = lean_box(v___x_475_);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_468_ = stack[0].m_obj;
lean_object* v_a_469_ = stack[1].m_obj;
lean_object* v_res_478_;
v_res_478_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(v_fvarId_468_, v_a_469_);
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg___boxed(lean_object* v_fvarId_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(v_fvarId_479_, v_a_480_);
lean_dec(v_a_480_);
return v_res_482_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(lean_object* v_fvarId_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_borrows_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_491_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_492_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_493_ = lean_st_ref_get(v_a_485_);
v_borrows_494_ = lean_ctor_get(v___x_493_, 1);
lean_inc_ref(v_borrows_494_);
lean_dec(v___x_493_);
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_491_, v___x_492_, v_borrows_494_, v_fvarId_483_);
lean_dec_ref(v_borrows_494_);
v___x_496_ = lean_box(v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_483_ = stack[0].m_obj;
lean_object* v_a_484_ = stack[1].m_obj;
lean_object* v_a_485_ = stack[2].m_obj;
lean_object* v_a_486_ = stack[3].m_obj;
lean_object* v_a_487_ = stack[4].m_obj;
lean_object* v_a_488_ = stack[5].m_obj;
lean_object* v_a_489_ = stack[6].m_obj;
lean_object* v_res_498_;
v_res_498_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(v_fvarId_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
stack->m_obj
 = v_res_498_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___boxed(lean_object* v_fvarId_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(v_fvarId_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
return v_res_507_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(lean_object* v_f_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_511_ = lean_st_ref_take(v_a_509_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_apply_1(v_f_508_, v___x_511_);
v___x_514_ = lean_st_ref_put(v_a_509_, v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_512_);
return v___x_515_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_508_ = stack[0].m_obj;
lean_object* v_a_509_ = stack[1].m_obj;
lean_object* v_res_516_;
v_res_516_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(v_f_508_, v_a_509_);
stack->m_obj
 = v_res_516_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg___boxed(lean_object* v_f_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(v_f_517_, v_a_518_);
lean_dec(v_a_518_);
return v_res_520_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(lean_object* v_f_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_529_ = lean_st_ref_take(v_a_523_);
v___x_530_ = lean_box(0);
v___x_531_ = lean_apply_1(v_f_521_, v___x_529_);
v___x_532_ = lean_st_ref_put(v_a_523_, v___x_531_);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_530_);
return v___x_533_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_521_ = stack[0].m_obj;
lean_object* v_a_522_ = stack[1].m_obj;
lean_object* v_a_523_ = stack[2].m_obj;
lean_object* v_a_524_ = stack[3].m_obj;
lean_object* v_a_525_ = stack[4].m_obj;
lean_object* v_a_526_ = stack[5].m_obj;
lean_object* v_a_527_ = stack[6].m_obj;
lean_object* v_res_534_;
v_res_534_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(v_f_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
stack->m_obj
 = v_res_534_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___boxed(lean_object* v_f_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(v_f_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(lean_object* v_child_544_, lean_object* v_k_545_, lean_object* v_t_546_){
_start:
{
if (lean_obj_tag(v_t_546_) == 0)
{
lean_object* v_size_547_; lean_object* v_k_548_; lean_object* v_v_549_; lean_object* v_l_550_; lean_object* v_r_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_577_; 
v_size_547_ = lean_ctor_get(v_t_546_, 0);
v_k_548_ = lean_ctor_get(v_t_546_, 1);
v_v_549_ = lean_ctor_get(v_t_546_, 2);
v_l_550_ = lean_ctor_get(v_t_546_, 3);
v_r_551_ = lean_ctor_get(v_t_546_, 4);
v_isSharedCheck_577_ = !lean_is_exclusive(v_t_546_);
if (v_isSharedCheck_577_ == 0)
{
v___x_553_ = v_t_546_;
v_isShared_554_ = v_isSharedCheck_577_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_r_551_);
lean_inc(v_l_550_);
lean_inc(v_v_549_);
lean_inc(v_k_548_);
lean_inc(v_size_547_);
lean_dec(v_t_546_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_577_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
uint8_t v___x_555_; 
v___x_555_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_545_, v_k_548_);
switch(v___x_555_)
{
case 0:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(v_child_544_, v_k_545_, v_l_550_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 3, v___x_556_);
v___x_558_ = v___x_553_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_size_547_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_k_548_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_v_549_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v_r_551_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
case 1:
{
lean_object* v_parents_560_; lean_object* v_children_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_572_; 
lean_dec(v_k_548_);
v_parents_560_ = lean_ctor_get(v_v_549_, 0);
v_children_561_ = lean_ctor_get(v_v_549_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_v_549_);
if (v_isSharedCheck_572_ == 0)
{
v___x_563_ = v_v_549_;
v_isShared_564_ = v_isSharedCheck_572_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_children_561_);
lean_inc(v_parents_560_);
lean_dec(v_v_549_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_572_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_565_, 0, v_child_544_);
lean_ctor_set(v___x_565_, 1, v_children_561_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_565_);
v___x_567_ = v___x_563_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_parents_560_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_565_);
v___x_567_ = v_reuseFailAlloc_571_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_569_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 2, v___x_567_);
lean_ctor_set(v___x_553_, 1, v_k_545_);
v___x_569_ = v___x_553_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_size_547_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_k_545_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v_l_550_);
lean_ctor_set(v_reuseFailAlloc_570_, 4, v_r_551_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
default: 
{
lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_573_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(v_child_544_, v_k_545_, v_r_551_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 4, v___x_573_);
v___x_575_ = v___x_553_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_size_547_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_k_548_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_v_549_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_l_550_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
else
{
lean_dec(v_k_545_);
lean_dec(v_child_544_);
return v_t_546_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(lean_object* v_child_578_, lean_object* v_as_579_, size_t v_i_580_, size_t v_stop_581_, lean_object* v_b_582_){
_start:
{
uint8_t v___x_583_; 
v___x_583_ = lean_usize_dec_eq(v_i_580_, v_stop_581_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; size_t v___x_586_; size_t v___x_587_; 
v___x_584_ = lean_array_uget_borrowed(v_as_579_, v_i_580_);
lean_inc(v___x_584_);
lean_inc(v_child_578_);
v___x_585_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(v_child_578_, v___x_584_, v_b_582_);
v___x_586_ = ((size_t)1ULL);
v___x_587_ = lean_usize_add(v_i_580_, v___x_586_);
v_i_580_ = v___x_587_;
v_b_582_ = v___x_585_;
goto _start;
}
else
{
lean_dec(v_child_578_);
return v_b_582_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_child_578_ = stack[0].m_obj;
lean_object* v_as_579_ = stack[1].m_obj;
size_t v_i_580_ = stack[2].m_num;
size_t v_stop_581_ = stack[3].m_num;
lean_object* v_b_582_ = stack[4].m_obj;
lean_object* v_res_589_;
v_res_589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(v_child_578_, v_as_579_, v_i_580_, v_stop_581_, v_b_582_);
stack->m_obj
 = v_res_589_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3___boxed(lean_object* v_child_590_, lean_object* v_as_591_, lean_object* v_i_592_, lean_object* v_stop_593_, lean_object* v_b_594_){
_start:
{
size_t v_i_boxed_595_; size_t v_stop_boxed_596_; lean_object* v_res_597_; 
v_i_boxed_595_ = lean_unbox_usize(v_i_592_);
lean_dec(v_i_592_);
v_stop_boxed_596_ = lean_unbox_usize(v_stop_593_);
lean_dec(v_stop_593_);
v_res_597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(v_child_590_, v_as_591_, v_i_boxed_595_, v_stop_boxed_596_, v_b_594_);
lean_dec_ref(v_as_591_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(lean_object* v_k_598_, lean_object* v_v_599_, lean_object* v_t_600_){
_start:
{
if (lean_obj_tag(v_t_600_) == 0)
{
lean_object* v_size_601_; lean_object* v_k_602_; lean_object* v_v_603_; lean_object* v_l_604_; lean_object* v_r_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_885_; 
v_size_601_ = lean_ctor_get(v_t_600_, 0);
v_k_602_ = lean_ctor_get(v_t_600_, 1);
v_v_603_ = lean_ctor_get(v_t_600_, 2);
v_l_604_ = lean_ctor_get(v_t_600_, 3);
v_r_605_ = lean_ctor_get(v_t_600_, 4);
v_isSharedCheck_885_ = !lean_is_exclusive(v_t_600_);
if (v_isSharedCheck_885_ == 0)
{
v___x_607_ = v_t_600_;
v_isShared_608_ = v_isSharedCheck_885_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_r_605_);
lean_inc(v_l_604_);
lean_inc(v_v_603_);
lean_inc(v_k_602_);
lean_inc(v_size_601_);
lean_dec(v_t_600_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_885_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint8_t v___x_609_; 
v___x_609_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_598_, v_k_602_);
switch(v___x_609_)
{
case 0:
{
lean_object* v_impl_610_; lean_object* v___x_611_; 
lean_dec(v_size_601_);
v_impl_610_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_k_598_, v_v_599_, v_l_604_);
v___x_611_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_605_) == 0)
{
lean_object* v_size_612_; lean_object* v_size_613_; lean_object* v_k_614_; lean_object* v_v_615_; lean_object* v_l_616_; lean_object* v_r_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_size_612_ = lean_ctor_get(v_r_605_, 0);
v_size_613_ = lean_ctor_get(v_impl_610_, 0);
v_k_614_ = lean_ctor_get(v_impl_610_, 1);
v_v_615_ = lean_ctor_get(v_impl_610_, 2);
v_l_616_ = lean_ctor_get(v_impl_610_, 3);
v_r_617_ = lean_ctor_get(v_impl_610_, 4);
lean_inc(v_r_617_);
v___x_618_ = lean_unsigned_to_nat(3u);
v___x_619_ = lean_nat_mul(v___x_618_, v_size_612_);
v___x_620_ = lean_nat_dec_lt(v___x_619_, v_size_613_);
lean_dec(v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
lean_dec(v_r_617_);
v___x_621_ = lean_nat_add(v___x_611_, v_size_613_);
v___x_622_ = lean_nat_add(v___x_621_, v_size_612_);
lean_dec(v___x_621_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 3, v_impl_610_);
lean_ctor_set(v___x_607_, 0, v___x_622_);
v___x_624_ = v___x_607_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_impl_610_);
lean_ctor_set(v_reuseFailAlloc_625_, 4, v_r_605_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
else
{
lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_691_; 
lean_inc(v_l_616_);
lean_inc(v_v_615_);
lean_inc(v_k_614_);
lean_inc(v_size_613_);
v_isSharedCheck_691_ = !lean_is_exclusive(v_impl_610_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; lean_object* v_unused_693_; lean_object* v_unused_694_; lean_object* v_unused_695_; lean_object* v_unused_696_; 
v_unused_692_ = lean_ctor_get(v_impl_610_, 4);
lean_dec(v_unused_692_);
v_unused_693_ = lean_ctor_get(v_impl_610_, 3);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v_impl_610_, 2);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_impl_610_, 1);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_impl_610_, 0);
lean_dec(v_unused_696_);
v___x_627_ = v_impl_610_;
v_isShared_628_ = v_isSharedCheck_691_;
goto v_resetjp_626_;
}
else
{
lean_dec(v_impl_610_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_691_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_size_629_; lean_object* v_size_630_; lean_object* v_k_631_; lean_object* v_v_632_; lean_object* v_l_633_; lean_object* v_r_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_size_629_ = lean_ctor_get(v_l_616_, 0);
v_size_630_ = lean_ctor_get(v_r_617_, 0);
v_k_631_ = lean_ctor_get(v_r_617_, 1);
v_v_632_ = lean_ctor_get(v_r_617_, 2);
v_l_633_ = lean_ctor_get(v_r_617_, 3);
v_r_634_ = lean_ctor_get(v_r_617_, 4);
v___x_635_ = lean_unsigned_to_nat(2u);
v___x_636_ = lean_nat_mul(v___x_635_, v_size_629_);
v___x_637_ = lean_nat_dec_lt(v_size_630_, v___x_636_);
lean_dec(v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_666_; 
lean_inc(v_r_634_);
lean_inc(v_l_633_);
lean_inc(v_v_632_);
lean_inc(v_k_631_);
v_isSharedCheck_666_ = !lean_is_exclusive(v_r_617_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; lean_object* v_unused_668_; lean_object* v_unused_669_; lean_object* v_unused_670_; lean_object* v_unused_671_; 
v_unused_667_ = lean_ctor_get(v_r_617_, 4);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_r_617_, 3);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v_r_617_, 2);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v_r_617_, 1);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_r_617_, 0);
lean_dec(v_unused_671_);
v___x_639_ = v_r_617_;
v_isShared_640_ = v_isSharedCheck_666_;
goto v_resetjp_638_;
}
else
{
lean_dec(v_r_617_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_666_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___x_654_; lean_object* v___y_656_; 
v___x_641_ = lean_nat_add(v___x_611_, v_size_613_);
lean_dec(v_size_613_);
v___x_642_ = lean_nat_add(v___x_641_, v_size_612_);
lean_dec(v___x_641_);
v___x_654_ = lean_nat_add(v___x_611_, v_size_629_);
if (lean_obj_tag(v_l_633_) == 0)
{
lean_object* v_size_664_; 
v_size_664_ = lean_ctor_get(v_l_633_, 0);
lean_inc(v_size_664_);
v___y_656_ = v_size_664_;
goto v___jp_655_;
}
else
{
lean_object* v___x_665_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___y_656_ = v___x_665_;
goto v___jp_655_;
}
v___jp_643_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = lean_nat_add(v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec(v___y_645_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 4, v_r_605_);
lean_ctor_set(v___x_639_, 3, v_r_634_);
lean_ctor_set(v___x_639_, 2, v_v_603_);
lean_ctor_set(v___x_639_, 1, v_k_602_);
lean_ctor_set(v___x_639_, 0, v___x_647_);
v___x_649_ = v___x_639_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_r_634_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v_r_605_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 4, v___x_649_);
lean_ctor_set(v___x_627_, 3, v___y_644_);
lean_ctor_set(v___x_627_, 2, v_v_632_);
lean_ctor_set(v___x_627_, 1, v_k_631_);
lean_ctor_set(v___x_627_, 0, v___x_642_);
v___x_651_ = v___x_627_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v___y_644_);
lean_ctor_set(v_reuseFailAlloc_652_, 4, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
v___jp_655_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = lean_nat_add(v___x_654_, v___y_656_);
lean_dec(v___y_656_);
lean_dec(v___x_654_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 4, v_l_633_);
lean_ctor_set(v___x_607_, 3, v_l_616_);
lean_ctor_set(v___x_607_, 2, v_v_615_);
lean_ctor_set(v___x_607_, 1, v_k_614_);
lean_ctor_set(v___x_607_, 0, v___x_657_);
v___x_659_ = v___x_607_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_663_, 3, v_l_616_);
lean_ctor_set(v_reuseFailAlloc_663_, 4, v_l_633_);
v___x_659_ = v_reuseFailAlloc_663_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; 
v___x_660_ = lean_nat_add(v___x_611_, v_size_612_);
if (lean_obj_tag(v_r_634_) == 0)
{
lean_object* v_size_661_; 
v_size_661_ = lean_ctor_get(v_r_634_, 0);
lean_inc(v_size_661_);
v___y_644_ = v___x_659_;
v___y_645_ = v___x_660_;
v___y_646_ = v_size_661_;
goto v___jp_643_;
}
else
{
lean_object* v___x_662_; 
v___x_662_ = lean_unsigned_to_nat(0u);
v___y_644_ = v___x_659_;
v___y_645_ = v___x_660_;
v___y_646_ = v___x_662_;
goto v___jp_643_;
}
}
}
}
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
lean_del_object(v___x_607_);
v___x_672_ = lean_nat_add(v___x_611_, v_size_613_);
lean_dec(v_size_613_);
v___x_673_ = lean_nat_add(v___x_672_, v_size_612_);
lean_dec(v___x_672_);
v___x_674_ = lean_nat_add(v___x_611_, v_size_612_);
v___x_675_ = lean_nat_add(v___x_674_, v_size_630_);
lean_dec(v___x_674_);
lean_inc_ref(v_r_605_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 4, v_r_605_);
lean_ctor_set(v___x_627_, 3, v_r_617_);
lean_ctor_set(v___x_627_, 2, v_v_603_);
lean_ctor_set(v___x_627_, 1, v_k_602_);
lean_ctor_set(v___x_627_, 0, v___x_675_);
v___x_677_ = v___x_627_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v_r_617_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v_r_605_);
v___x_677_ = v_reuseFailAlloc_690_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
v_isSharedCheck_684_ = !lean_is_exclusive(v_r_605_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; lean_object* v_unused_686_; lean_object* v_unused_687_; lean_object* v_unused_688_; lean_object* v_unused_689_; 
v_unused_685_ = lean_ctor_get(v_r_605_, 4);
lean_dec(v_unused_685_);
v_unused_686_ = lean_ctor_get(v_r_605_, 3);
lean_dec(v_unused_686_);
v_unused_687_ = lean_ctor_get(v_r_605_, 2);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_r_605_, 1);
lean_dec(v_unused_688_);
v_unused_689_ = lean_ctor_get(v_r_605_, 0);
lean_dec(v_unused_689_);
v___x_679_ = v_r_605_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_dec(v_r_605_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 4, v___x_677_);
lean_ctor_set(v___x_679_, 3, v_l_616_);
lean_ctor_set(v___x_679_, 2, v_v_615_);
lean_ctor_set(v___x_679_, 1, v_k_614_);
lean_ctor_set(v___x_679_, 0, v___x_673_);
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_l_616_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v___x_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_697_; 
v_l_697_ = lean_ctor_get(v_impl_610_, 3);
if (lean_obj_tag(v_l_697_) == 0)
{
lean_object* v_r_698_; lean_object* v_k_699_; lean_object* v_v_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_711_; 
lean_inc_ref(v_l_697_);
v_r_698_ = lean_ctor_get(v_impl_610_, 4);
v_k_699_ = lean_ctor_get(v_impl_610_, 1);
v_v_700_ = lean_ctor_get(v_impl_610_, 2);
v_isSharedCheck_711_ = !lean_is_exclusive(v_impl_610_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; lean_object* v_unused_713_; 
v_unused_712_ = lean_ctor_get(v_impl_610_, 3);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_impl_610_, 0);
lean_dec(v_unused_713_);
v___x_702_ = v_impl_610_;
v_isShared_703_ = v_isSharedCheck_711_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_r_698_);
lean_inc(v_v_700_);
lean_inc(v_k_699_);
lean_dec(v_impl_610_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_711_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_698_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 3, v_r_698_);
lean_ctor_set(v___x_702_, 2, v_v_603_);
lean_ctor_set(v___x_702_, 1, v_k_602_);
lean_ctor_set(v___x_702_, 0, v___x_611_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_r_698_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v_r_698_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 4, v___x_706_);
lean_ctor_set(v___x_607_, 3, v_l_697_);
lean_ctor_set(v___x_607_, 2, v_v_700_);
lean_ctor_set(v___x_607_, 1, v_k_699_);
lean_ctor_set(v___x_607_, 0, v___x_704_);
v___x_708_ = v___x_607_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_k_699_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_v_700_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_l_697_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_r_714_; 
v_r_714_ = lean_ctor_get(v_impl_610_, 4);
lean_inc(v_r_714_);
if (lean_obj_tag(v_r_714_) == 0)
{
lean_object* v_k_715_; lean_object* v_v_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_739_; 
lean_inc(v_l_697_);
v_k_715_ = lean_ctor_get(v_impl_610_, 1);
v_v_716_ = lean_ctor_get(v_impl_610_, 2);
v_isSharedCheck_739_ = !lean_is_exclusive(v_impl_610_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; lean_object* v_unused_741_; lean_object* v_unused_742_; 
v_unused_740_ = lean_ctor_get(v_impl_610_, 4);
lean_dec(v_unused_740_);
v_unused_741_ = lean_ctor_get(v_impl_610_, 3);
lean_dec(v_unused_741_);
v_unused_742_ = lean_ctor_get(v_impl_610_, 0);
lean_dec(v_unused_742_);
v___x_718_ = v_impl_610_;
v_isShared_719_ = v_isSharedCheck_739_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_v_716_);
lean_inc(v_k_715_);
lean_dec(v_impl_610_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_739_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_k_720_; lean_object* v_v_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_735_; 
v_k_720_ = lean_ctor_get(v_r_714_, 1);
v_v_721_ = lean_ctor_get(v_r_714_, 2);
v_isSharedCheck_735_ = !lean_is_exclusive(v_r_714_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; lean_object* v_unused_737_; lean_object* v_unused_738_; 
v_unused_736_ = lean_ctor_get(v_r_714_, 4);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_r_714_, 3);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_r_714_, 0);
lean_dec(v_unused_738_);
v___x_723_ = v_r_714_;
v_isShared_724_ = v_isSharedCheck_735_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_v_721_);
lean_inc(v_k_720_);
lean_dec(v_r_714_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_735_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = lean_unsigned_to_nat(3u);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 4, v_l_697_);
lean_ctor_set(v___x_723_, 3, v_l_697_);
lean_ctor_set(v___x_723_, 2, v_v_716_);
lean_ctor_set(v___x_723_, 1, v_k_715_);
lean_ctor_set(v___x_723_, 0, v___x_611_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_k_715_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_v_716_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v_l_697_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v_l_697_);
v___x_727_ = v_reuseFailAlloc_734_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_729_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 4, v_l_697_);
lean_ctor_set(v___x_718_, 2, v_v_603_);
lean_ctor_set(v___x_718_, 1, v_k_602_);
lean_ctor_set(v___x_718_, 0, v___x_611_);
v___x_729_ = v___x_718_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_l_697_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_l_697_);
v___x_729_ = v_reuseFailAlloc_733_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_731_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 4, v___x_729_);
lean_ctor_set(v___x_607_, 3, v___x_727_);
lean_ctor_set(v___x_607_, 2, v_v_721_);
lean_ctor_set(v___x_607_, 1, v_k_720_);
lean_ctor_set(v___x_607_, 0, v___x_725_);
v___x_731_ = v___x_607_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_k_720_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_v_721_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v___x_729_);
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
}
else
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_unsigned_to_nat(2u);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 4, v_r_714_);
lean_ctor_set(v___x_607_, 3, v_impl_610_);
lean_ctor_set(v___x_607_, 0, v___x_743_);
v___x_745_ = v___x_607_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_impl_610_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v_r_714_);
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
case 1:
{
lean_object* v___x_748_; 
lean_dec(v_v_603_);
lean_dec(v_k_602_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 2, v_v_599_);
lean_ctor_set(v___x_607_, 1, v_k_598_);
v___x_748_ = v___x_607_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_size_601_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_k_598_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_v_599_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_l_604_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v_r_605_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
default: 
{
lean_object* v_impl_750_; lean_object* v___x_751_; 
lean_dec(v_size_601_);
v_impl_750_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_k_598_, v_v_599_, v_r_605_);
v___x_751_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_604_) == 0)
{
lean_object* v_size_752_; lean_object* v_size_753_; lean_object* v_k_754_; lean_object* v_v_755_; lean_object* v_l_756_; lean_object* v_r_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_size_752_ = lean_ctor_get(v_l_604_, 0);
v_size_753_ = lean_ctor_get(v_impl_750_, 0);
v_k_754_ = lean_ctor_get(v_impl_750_, 1);
v_v_755_ = lean_ctor_get(v_impl_750_, 2);
v_l_756_ = lean_ctor_get(v_impl_750_, 3);
lean_inc(v_l_756_);
v_r_757_ = lean_ctor_get(v_impl_750_, 4);
v___x_758_ = lean_unsigned_to_nat(3u);
v___x_759_ = lean_nat_mul(v___x_758_, v_size_752_);
v___x_760_ = lean_nat_dec_lt(v___x_759_, v_size_753_);
lean_dec(v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
lean_dec(v_l_756_);
v___x_761_ = lean_nat_add(v___x_751_, v_size_752_);
v___x_762_ = lean_nat_add(v___x_761_, v_size_753_);
lean_dec(v___x_761_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 4, v_impl_750_);
lean_ctor_set(v___x_607_, 0, v___x_762_);
v___x_764_ = v___x_607_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_765_, 3, v_l_604_);
lean_ctor_set(v_reuseFailAlloc_765_, 4, v_impl_750_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
else
{
lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_829_; 
lean_inc(v_r_757_);
lean_inc(v_v_755_);
lean_inc(v_k_754_);
lean_inc(v_size_753_);
v_isSharedCheck_829_ = !lean_is_exclusive(v_impl_750_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; lean_object* v_unused_831_; lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; 
v_unused_830_ = lean_ctor_get(v_impl_750_, 4);
lean_dec(v_unused_830_);
v_unused_831_ = lean_ctor_get(v_impl_750_, 3);
lean_dec(v_unused_831_);
v_unused_832_ = lean_ctor_get(v_impl_750_, 2);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_impl_750_, 1);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_impl_750_, 0);
lean_dec(v_unused_834_);
v___x_767_ = v_impl_750_;
v_isShared_768_ = v_isSharedCheck_829_;
goto v_resetjp_766_;
}
else
{
lean_dec(v_impl_750_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_829_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_size_769_; lean_object* v_k_770_; lean_object* v_v_771_; lean_object* v_l_772_; lean_object* v_r_773_; lean_object* v_size_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_size_769_ = lean_ctor_get(v_l_756_, 0);
v_k_770_ = lean_ctor_get(v_l_756_, 1);
v_v_771_ = lean_ctor_get(v_l_756_, 2);
v_l_772_ = lean_ctor_get(v_l_756_, 3);
v_r_773_ = lean_ctor_get(v_l_756_, 4);
v_size_774_ = lean_ctor_get(v_r_757_, 0);
v___x_775_ = lean_unsigned_to_nat(2u);
v___x_776_ = lean_nat_mul(v___x_775_, v_size_774_);
v___x_777_ = lean_nat_dec_lt(v_size_769_, v___x_776_);
lean_dec(v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_805_; 
lean_inc(v_r_773_);
lean_inc(v_l_772_);
lean_inc(v_v_771_);
lean_inc(v_k_770_);
v_isSharedCheck_805_ = !lean_is_exclusive(v_l_756_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; lean_object* v_unused_807_; lean_object* v_unused_808_; lean_object* v_unused_809_; lean_object* v_unused_810_; 
v_unused_806_ = lean_ctor_get(v_l_756_, 4);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_l_756_, 3);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_l_756_, 2);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_l_756_, 1);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_l_756_, 0);
lean_dec(v_unused_810_);
v___x_779_ = v_l_756_;
v_isShared_780_ = v_isSharedCheck_805_;
goto v_resetjp_778_;
}
else
{
lean_dec(v_l_756_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_805_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_795_; 
v___x_781_ = lean_nat_add(v___x_751_, v_size_752_);
v___x_782_ = lean_nat_add(v___x_781_, v_size_753_);
lean_dec(v_size_753_);
if (lean_obj_tag(v_l_772_) == 0)
{
lean_object* v_size_803_; 
v_size_803_ = lean_ctor_get(v_l_772_, 0);
lean_inc(v_size_803_);
v___y_795_ = v_size_803_;
goto v___jp_794_;
}
else
{
lean_object* v___x_804_; 
v___x_804_ = lean_unsigned_to_nat(0u);
v___y_795_ = v___x_804_;
goto v___jp_794_;
}
v___jp_783_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_nat_add(v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec(v___y_785_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_r_757_);
lean_ctor_set(v___x_779_, 3, v_r_773_);
lean_ctor_set(v___x_779_, 2, v_v_755_);
lean_ctor_set(v___x_779_, 1, v_k_754_);
lean_ctor_set(v___x_779_, 0, v___x_787_);
v___x_789_ = v___x_779_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_k_754_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_v_755_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v_r_773_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v_r_757_);
v___x_789_ = v_reuseFailAlloc_793_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_791_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 4, v___x_789_);
lean_ctor_set(v___x_767_, 3, v___y_784_);
lean_ctor_set(v___x_767_, 2, v_v_771_);
lean_ctor_set(v___x_767_, 1, v_k_770_);
lean_ctor_set(v___x_767_, 0, v___x_782_);
v___x_791_ = v___x_767_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_k_770_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_v_771_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v___y_784_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
v___jp_794_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_nat_add(v___x_781_, v___y_795_);
lean_dec(v___y_795_);
lean_dec(v___x_781_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 4, v_l_772_);
lean_ctor_set(v___x_607_, 0, v___x_796_);
v___x_798_ = v___x_607_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v_l_604_);
lean_ctor_set(v_reuseFailAlloc_802_, 4, v_l_772_);
v___x_798_ = v_reuseFailAlloc_802_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; 
v___x_799_ = lean_nat_add(v___x_751_, v_size_774_);
if (lean_obj_tag(v_r_773_) == 0)
{
lean_object* v_size_800_; 
v_size_800_ = lean_ctor_get(v_r_773_, 0);
lean_inc(v_size_800_);
v___y_784_ = v___x_798_;
v___y_785_ = v___x_799_;
v___y_786_ = v_size_800_;
goto v___jp_783_;
}
else
{
lean_object* v___x_801_; 
v___x_801_ = lean_unsigned_to_nat(0u);
v___y_784_ = v___x_798_;
v___y_785_ = v___x_799_;
v___y_786_ = v___x_801_;
goto v___jp_783_;
}
}
}
}
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
lean_del_object(v___x_607_);
v___x_811_ = lean_nat_add(v___x_751_, v_size_752_);
v___x_812_ = lean_nat_add(v___x_811_, v_size_753_);
lean_dec(v_size_753_);
v___x_813_ = lean_nat_add(v___x_811_, v_size_769_);
lean_dec(v___x_811_);
lean_inc_ref(v_l_604_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 4, v_l_756_);
lean_ctor_set(v___x_767_, 3, v_l_604_);
lean_ctor_set(v___x_767_, 2, v_v_603_);
lean_ctor_set(v___x_767_, 1, v_k_602_);
lean_ctor_set(v___x_767_, 0, v___x_813_);
v___x_815_ = v___x_767_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_l_604_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_l_756_);
v___x_815_ = v_reuseFailAlloc_828_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
v_isSharedCheck_822_ = !lean_is_exclusive(v_l_604_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; lean_object* v_unused_824_; lean_object* v_unused_825_; lean_object* v_unused_826_; lean_object* v_unused_827_; 
v_unused_823_ = lean_ctor_get(v_l_604_, 4);
lean_dec(v_unused_823_);
v_unused_824_ = lean_ctor_get(v_l_604_, 3);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_l_604_, 2);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_l_604_, 1);
lean_dec(v_unused_826_);
v_unused_827_ = lean_ctor_get(v_l_604_, 0);
lean_dec(v_unused_827_);
v___x_817_ = v_l_604_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_dec(v_l_604_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 4, v_r_757_);
lean_ctor_set(v___x_817_, 3, v___x_815_);
lean_ctor_set(v___x_817_, 2, v_v_755_);
lean_ctor_set(v___x_817_, 1, v_k_754_);
lean_ctor_set(v___x_817_, 0, v___x_812_);
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_k_754_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_v_755_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_r_757_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_835_; 
v_l_835_ = lean_ctor_get(v_impl_750_, 3);
lean_inc(v_l_835_);
if (lean_obj_tag(v_l_835_) == 0)
{
lean_object* v_r_836_; lean_object* v_k_837_; lean_object* v_v_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_861_; 
v_r_836_ = lean_ctor_get(v_impl_750_, 4);
v_k_837_ = lean_ctor_get(v_impl_750_, 1);
v_v_838_ = lean_ctor_get(v_impl_750_, 2);
v_isSharedCheck_861_ = !lean_is_exclusive(v_impl_750_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; lean_object* v_unused_863_; 
v_unused_862_ = lean_ctor_get(v_impl_750_, 3);
lean_dec(v_unused_862_);
v_unused_863_ = lean_ctor_get(v_impl_750_, 0);
lean_dec(v_unused_863_);
v___x_840_ = v_impl_750_;
v_isShared_841_ = v_isSharedCheck_861_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_r_836_);
lean_inc(v_v_838_);
lean_inc(v_k_837_);
lean_dec(v_impl_750_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_861_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v_k_842_; lean_object* v_v_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_857_; 
v_k_842_ = lean_ctor_get(v_l_835_, 1);
v_v_843_ = lean_ctor_get(v_l_835_, 2);
v_isSharedCheck_857_ = !lean_is_exclusive(v_l_835_);
if (v_isSharedCheck_857_ == 0)
{
lean_object* v_unused_858_; lean_object* v_unused_859_; lean_object* v_unused_860_; 
v_unused_858_ = lean_ctor_get(v_l_835_, 4);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_l_835_, 3);
lean_dec(v_unused_859_);
v_unused_860_ = lean_ctor_get(v_l_835_, 0);
lean_dec(v_unused_860_);
v___x_845_ = v_l_835_;
v_isShared_846_ = v_isSharedCheck_857_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_v_843_);
lean_inc(v_k_842_);
lean_dec(v_l_835_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_857_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_847_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_836_, 2);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 4, v_r_836_);
lean_ctor_set(v___x_845_, 3, v_r_836_);
lean_ctor_set(v___x_845_, 2, v_v_603_);
lean_ctor_set(v___x_845_, 1, v_k_602_);
lean_ctor_set(v___x_845_, 0, v___x_751_);
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_856_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_856_, 3, v_r_836_);
lean_ctor_set(v_reuseFailAlloc_856_, 4, v_r_836_);
v___x_849_ = v_reuseFailAlloc_856_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_851_; 
lean_inc(v_r_836_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 3, v_r_836_);
lean_ctor_set(v___x_840_, 0, v___x_751_);
v___x_851_ = v___x_840_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_k_837_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_v_838_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v_r_836_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v_r_836_);
v___x_851_ = v_reuseFailAlloc_855_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_853_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 4, v___x_851_);
lean_ctor_set(v___x_607_, 3, v___x_849_);
lean_ctor_set(v___x_607_, 2, v_v_843_);
lean_ctor_set(v___x_607_, 1, v_k_842_);
lean_ctor_set(v___x_607_, 0, v___x_847_);
v___x_853_ = v___x_607_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_k_842_);
lean_ctor_set(v_reuseFailAlloc_854_, 2, v_v_843_);
lean_ctor_set(v_reuseFailAlloc_854_, 3, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_854_, 4, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
else
{
lean_object* v_r_864_; 
v_r_864_ = lean_ctor_get(v_impl_750_, 4);
lean_inc(v_r_864_);
if (lean_obj_tag(v_r_864_) == 0)
{
lean_object* v_k_865_; lean_object* v_v_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_877_; 
v_k_865_ = lean_ctor_get(v_impl_750_, 1);
v_v_866_ = lean_ctor_get(v_impl_750_, 2);
v_isSharedCheck_877_ = !lean_is_exclusive(v_impl_750_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; lean_object* v_unused_879_; lean_object* v_unused_880_; 
v_unused_878_ = lean_ctor_get(v_impl_750_, 4);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v_impl_750_, 3);
lean_dec(v_unused_879_);
v_unused_880_ = lean_ctor_get(v_impl_750_, 0);
lean_dec(v_unused_880_);
v___x_868_ = v_impl_750_;
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_v_866_);
lean_inc(v_k_865_);
lean_dec(v_impl_750_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = lean_unsigned_to_nat(3u);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 4, v_l_835_);
lean_ctor_set(v___x_868_, 2, v_v_603_);
lean_ctor_set(v___x_868_, 1, v_k_602_);
lean_ctor_set(v___x_868_, 0, v___x_751_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_876_, 3, v_l_835_);
lean_ctor_set(v_reuseFailAlloc_876_, 4, v_l_835_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 4, v_r_864_);
lean_ctor_set(v___x_607_, 3, v___x_872_);
lean_ctor_set(v___x_607_, 2, v_v_866_);
lean_ctor_set(v___x_607_, 1, v_k_865_);
lean_ctor_set(v___x_607_, 0, v___x_870_);
v___x_874_ = v___x_607_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_k_865_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_v_866_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v_r_864_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = lean_unsigned_to_nat(2u);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 4, v_impl_750_);
lean_ctor_set(v___x_607_, 3, v_r_864_);
lean_ctor_set(v___x_607_, 0, v___x_881_);
v___x_883_ = v___x_607_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_884_, 3, v_r_864_);
lean_ctor_set(v_reuseFailAlloc_884_, 4, v_impl_750_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
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
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v_k_598_);
lean_ctor_set(v___x_887_, 2, v_v_599_);
lean_ctor_set(v___x_887_, 3, v_t_600_);
lean_ctor_set(v___x_887_, 4, v_t_600_);
return v___x_887_;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(lean_object* v_m_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_buckets_890_; lean_object* v___x_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v_fold_895_; uint64_t v___x_896_; uint64_t v___x_897_; uint64_t v___x_898_; size_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_buckets_890_ = lean_ctor_get(v_m_888_, 1);
v___x_891_ = lean_array_get_size(v_buckets_890_);
v___x_892_ = l_Lean_instHashableFVarId_hash(v_a_889_);
v___x_893_ = 32ULL;
v___x_894_ = lean_uint64_shift_right(v___x_892_, v___x_893_);
v_fold_895_ = lean_uint64_xor(v___x_892_, v___x_894_);
v___x_896_ = 16ULL;
v___x_897_ = lean_uint64_shift_right(v_fold_895_, v___x_896_);
v___x_898_ = lean_uint64_xor(v_fold_895_, v___x_897_);
v___x_899_ = lean_uint64_to_usize(v___x_898_);
v___x_900_ = lean_usize_of_nat(v___x_891_);
v___x_901_ = ((size_t)1ULL);
v___x_902_ = lean_usize_sub(v___x_900_, v___x_901_);
v___x_903_ = lean_usize_land(v___x_899_, v___x_902_);
v___x_904_ = lean_array_uget_borrowed(v_buckets_890_, v___x_903_);
v___x_905_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_889_, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_888_ = stack[0].m_obj;
lean_object* v_a_889_ = stack[1].m_obj;
uint8_t v_res_906_;
v_res_906_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_m_888_, v_a_889_);
stack->m_num = v_res_906_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg___boxed(lean_object* v_m_907_, lean_object* v_a_908_){
_start:
{
uint8_t v_res_909_; lean_object* v_r_910_; 
v_res_909_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_m_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_m_907_);
v_r_910_ = lean_box(v_res_909_);
return v_r_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(lean_object* v_ctx_911_, lean_object* v_parents_912_, lean_object* v_child_913_){
_start:
{
lean_object* v_resetTargets_914_; lean_object* v_unconditionalBorrows_915_; lean_object* v_derivedValMap_916_; lean_object* v_varMap_917_; lean_object* v_jpLiveVarMap_918_; lean_object* v_idx_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_952_; 
v_resetTargets_914_ = lean_ctor_get(v_ctx_911_, 0);
v_unconditionalBorrows_915_ = lean_ctor_get(v_ctx_911_, 1);
v_derivedValMap_916_ = lean_ctor_get(v_ctx_911_, 2);
v_varMap_917_ = lean_ctor_get(v_ctx_911_, 3);
v_jpLiveVarMap_918_ = lean_ctor_get(v_ctx_911_, 4);
v_idx_919_ = lean_ctor_get(v_ctx_911_, 5);
v_isSharedCheck_952_ = !lean_is_exclusive(v_ctx_911_);
if (v_isSharedCheck_952_ == 0)
{
v___x_921_ = v_ctx_911_;
v_isShared_922_ = v_isSharedCheck_952_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_idx_919_);
lean_inc(v_jpLiveVarMap_918_);
lean_inc(v_varMap_917_);
lean_inc(v_derivedValMap_916_);
lean_inc(v_unconditionalBorrows_915_);
lean_inc(v_resetTargets_914_);
lean_dec(v_ctx_911_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_952_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v_derivedValMap_925_; uint8_t v___x_926_; 
v___x_923_ = lean_box(0);
lean_inc_ref(v_parents_912_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v_parents_912_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
lean_inc(v_child_913_);
v_derivedValMap_925_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_child_913_, v___x_924_, v_derivedValMap_916_);
v___x_926_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_resetTargets_914_, v_child_913_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_array_get_size(v_parents_912_);
v___x_929_ = lean_nat_dec_lt(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_931_; 
lean_dec(v_child_913_);
lean_dec_ref(v_parents_912_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 2, v_derivedValMap_925_);
v___x_931_ = v___x_921_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_resetTargets_914_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_unconditionalBorrows_915_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_derivedValMap_925_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_varMap_917_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v_jpLiveVarMap_918_);
lean_ctor_set(v_reuseFailAlloc_932_, 5, v_idx_919_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
else
{
uint8_t v___x_933_; 
v___x_933_ = lean_nat_dec_le(v___x_928_, v___x_928_);
if (v___x_933_ == 0)
{
if (v___x_929_ == 0)
{
lean_object* v___x_935_; 
lean_dec(v_child_913_);
lean_dec_ref(v_parents_912_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 2, v_derivedValMap_925_);
v___x_935_ = v___x_921_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_resetTargets_914_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_unconditionalBorrows_915_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_derivedValMap_925_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v_varMap_917_);
lean_ctor_set(v_reuseFailAlloc_936_, 4, v_jpLiveVarMap_918_);
lean_ctor_set(v_reuseFailAlloc_936_, 5, v_idx_919_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
else
{
size_t v___x_937_; size_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_937_ = ((size_t)0ULL);
v___x_938_ = lean_usize_of_nat(v___x_928_);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(v_child_913_, v_parents_912_, v___x_937_, v___x_938_, v_derivedValMap_925_);
lean_dec_ref(v_parents_912_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 2, v___x_939_);
v___x_941_ = v___x_921_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_resetTargets_914_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_unconditionalBorrows_915_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_varMap_917_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_jpLiveVarMap_918_);
lean_ctor_set(v_reuseFailAlloc_942_, 5, v_idx_919_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
else
{
size_t v___x_943_; size_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_943_ = ((size_t)0ULL);
v___x_944_ = lean_usize_of_nat(v___x_928_);
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(v_child_913_, v_parents_912_, v___x_943_, v___x_944_, v_derivedValMap_925_);
lean_dec_ref(v_parents_912_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 2, v___x_945_);
v___x_947_ = v___x_921_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_resetTargets_914_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_unconditionalBorrows_915_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_varMap_917_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_jpLiveVarMap_918_);
lean_ctor_set(v_reuseFailAlloc_948_, 5, v_idx_919_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
lean_object* v___x_950_; 
lean_dec(v_child_913_);
lean_dec_ref(v_parents_912_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 2, v_derivedValMap_925_);
v___x_950_ = v___x_921_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_resetTargets_914_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_unconditionalBorrows_915_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_derivedValMap_925_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_varMap_917_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_jpLiveVarMap_918_);
lean_ctor_set(v_reuseFailAlloc_951_, 5, v_idx_919_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1(lean_object* v_00_u03b2_953_, lean_object* v_k_954_, lean_object* v_v_955_, lean_object* v_t_956_, lean_object* v_hl_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_k_954_, v_v_955_, v_t_956_);
return v___x_958_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2(lean_object* v_00_u03b2_959_, lean_object* v_m_960_, lean_object* v_a_961_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_m_960_, v_a_961_);
return v___x_962_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_960_ = stack[1].m_obj;
lean_object* v_a_961_ = stack[2].m_obj;
uint8_t v_res_963_;
v_res_963_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2(lean_box(0), v_m_960_, v_a_961_);
stack->m_num = v_res_963_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___boxed(lean_object* v_00_u03b2_964_, lean_object* v_m_965_, lean_object* v_a_966_){
_start:
{
uint8_t v_res_967_; lean_object* v_r_968_; 
v_res_967_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2(v_00_u03b2_964_, v_m_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_m_965_);
v_r_968_ = lean_box(v_res_967_);
return v_r_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(lean_object* v_ctx_969_, lean_object* v_fvarId_970_){
_start:
{
lean_object* v_resetTargets_971_; lean_object* v_unconditionalBorrows_972_; lean_object* v_derivedValMap_973_; lean_object* v_varMap_974_; lean_object* v_jpLiveVarMap_975_; lean_object* v_idx_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_984_; 
v_resetTargets_971_ = lean_ctor_get(v_ctx_969_, 0);
v_unconditionalBorrows_972_ = lean_ctor_get(v_ctx_969_, 1);
v_derivedValMap_973_ = lean_ctor_get(v_ctx_969_, 2);
v_varMap_974_ = lean_ctor_get(v_ctx_969_, 3);
v_jpLiveVarMap_975_ = lean_ctor_get(v_ctx_969_, 4);
v_idx_976_ = lean_ctor_get(v_ctx_969_, 5);
v_isSharedCheck_984_ = !lean_is_exclusive(v_ctx_969_);
if (v_isSharedCheck_984_ == 0)
{
v___x_978_ = v_ctx_969_;
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_idx_976_);
lean_inc(v_jpLiveVarMap_975_);
lean_inc(v_varMap_974_);
lean_inc(v_derivedValMap_973_);
lean_inc(v_unconditionalBorrows_972_);
lean_inc(v_resetTargets_971_);
lean_dec(v_ctx_969_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_980_, 0, v_fvarId_970_);
lean_ctor_set(v___x_980_, 1, v_unconditionalBorrows_972_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___x_980_);
v___x_982_ = v___x_978_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_resetTargets_971_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_derivedValMap_973_);
lean_ctor_set(v_reuseFailAlloc_983_, 3, v_varMap_974_);
lean_ctor_set(v_reuseFailAlloc_983_, 4, v_jpLiveVarMap_975_);
lean_ctor_set(v_reuseFailAlloc_983_, 5, v_idx_976_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(lean_object* v_t_985_, lean_object* v_k_986_){
_start:
{
if (lean_obj_tag(v_t_985_) == 0)
{
lean_object* v_k_987_; lean_object* v_v_988_; lean_object* v_l_989_; lean_object* v_r_990_; uint8_t v___x_991_; 
v_k_987_ = lean_ctor_get(v_t_985_, 1);
v_v_988_ = lean_ctor_get(v_t_985_, 2);
v_l_989_ = lean_ctor_get(v_t_985_, 3);
v_r_990_ = lean_ctor_get(v_t_985_, 4);
v___x_991_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_986_, v_k_987_);
switch(v___x_991_)
{
case 0:
{
v_t_985_ = v_l_989_;
goto _start;
}
case 1:
{
lean_object* v___x_993_; 
lean_inc(v_v_988_);
v___x_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_993_, 0, v_v_988_);
return v___x_993_;
}
default: 
{
v_t_985_ = v_r_990_;
goto _start;
}
}
}
else
{
lean_object* v___x_995_; 
v___x_995_ = lean_box(0);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg___boxed(lean_object* v_t_996_, lean_object* v_k_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_t_996_, v_k_997_);
lean_dec(v_k_997_);
lean_dec(v_t_996_);
return v_res_998_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(lean_object* v_ctx_999_, lean_object* v_as_1000_, size_t v_i_1001_, size_t v_stop_1002_, lean_object* v_b_1003_){
_start:
{
lean_object* v___y_1005_; uint8_t v___x_1009_; 
v___x_1009_ = lean_usize_dec_eq(v_i_1001_, v_stop_1002_);
if (v___x_1009_ == 0)
{
lean_object* v_varMap_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_varMap_1010_ = lean_ctor_get(v_ctx_999_, 3);
v___x_1011_ = lean_array_uget_borrowed(v_as_1000_, v_i_1001_);
v___x_1012_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_varMap_1010_, v___x_1011_);
if (lean_obj_tag(v___x_1012_) == 0)
{
v___y_1005_ = v_b_1003_;
goto v___jp_1004_;
}
else
{
lean_object* v_val_1013_; uint8_t v_isPossibleRef_1014_; 
v_val_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v_isPossibleRef_1014_ = lean_ctor_get_uint8(v_val_1013_, sizeof(void*)*2);
lean_dec(v_val_1013_);
if (v_isPossibleRef_1014_ == 0)
{
v___y_1005_ = v_b_1003_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1015_; 
lean_inc(v___x_1011_);
v___x_1015_ = lean_array_push(v_b_1003_, v___x_1011_);
v___y_1005_ = v___x_1015_;
goto v___jp_1004_;
}
}
}
else
{
return v_b_1003_;
}
v___jp_1004_:
{
size_t v___x_1006_; size_t v___x_1007_; 
v___x_1006_ = ((size_t)1ULL);
v___x_1007_ = lean_usize_add(v_i_1001_, v___x_1006_);
v_i_1001_ = v___x_1007_;
v_b_1003_ = v___y_1005_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_999_ = stack[0].m_obj;
lean_object* v_as_1000_ = stack[1].m_obj;
size_t v_i_1001_ = stack[2].m_num;
size_t v_stop_1002_ = stack[3].m_num;
lean_object* v_b_1003_ = stack[4].m_obj;
lean_object* v_res_1016_;
v_res_1016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(v_ctx_999_, v_as_1000_, v_i_1001_, v_stop_1002_, v_b_1003_);
stack->m_obj
 = v_res_1016_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1___boxed(lean_object* v_ctx_1017_, lean_object* v_as_1018_, lean_object* v_i_1019_, lean_object* v_stop_1020_, lean_object* v_b_1021_){
_start:
{
size_t v_i_boxed_1022_; size_t v_stop_boxed_1023_; lean_object* v_res_1024_; 
v_i_boxed_1022_ = lean_unbox_usize(v_i_1019_);
lean_dec(v_i_1019_);
v_stop_boxed_1023_ = lean_unbox_usize(v_stop_1020_);
lean_dec(v_stop_1020_);
v_res_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(v_ctx_1017_, v_as_1018_, v_i_boxed_1022_, v_stop_boxed_1023_, v_b_1021_);
lean_dec_ref(v_as_1018_);
lean_dec_ref(v_ctx_1017_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(lean_object* v_ctx_1027_, lean_object* v_parents_1028_, lean_object* v_decl_1029_){
_start:
{
lean_object* v_fvarId_1030_; lean_object* v_type_1031_; uint8_t v___x_1032_; 
v_fvarId_1030_ = lean_ctor_get(v_decl_1029_, 0);
lean_inc(v_fvarId_1030_);
v_type_1031_ = lean_ctor_get(v_decl_1029_, 2);
lean_inc_ref(v_type_1031_);
lean_dec_ref(v_decl_1029_);
v___x_1032_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1031_);
lean_dec_ref(v_type_1031_);
if (v___x_1032_ == 0)
{
lean_dec(v_fvarId_1030_);
return v_ctx_1027_;
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_array_get_size(v_parents_1028_);
v___x_1035_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1036_ = lean_nat_dec_lt(v___x_1033_, v___x_1034_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1027_, v___x_1035_, v_fvarId_1030_);
return v___x_1037_;
}
else
{
uint8_t v___x_1038_; 
v___x_1038_ = lean_nat_dec_le(v___x_1034_, v___x_1034_);
if (v___x_1038_ == 0)
{
if (v___x_1036_ == 0)
{
lean_object* v___x_1039_; 
v___x_1039_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1027_, v___x_1035_, v_fvarId_1030_);
return v___x_1039_;
}
else
{
size_t v___x_1040_; size_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1040_ = ((size_t)0ULL);
v___x_1041_ = lean_usize_of_nat(v___x_1034_);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(v_ctx_1027_, v_parents_1028_, v___x_1040_, v___x_1041_, v___x_1035_);
v___x_1043_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1027_, v___x_1042_, v_fvarId_1030_);
return v___x_1043_;
}
}
else
{
size_t v___x_1044_; size_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1044_ = ((size_t)0ULL);
v___x_1045_ = lean_usize_of_nat(v___x_1034_);
v___x_1046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(v_ctx_1027_, v_parents_1028_, v___x_1044_, v___x_1045_, v___x_1035_);
v___x_1047_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1027_, v___x_1046_, v_fvarId_1030_);
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___boxed(lean_object* v_ctx_1048_, lean_object* v_parents_1049_, lean_object* v_decl_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1048_, v_parents_1049_, v_decl_1050_);
lean_dec_ref(v_parents_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0(lean_object* v_00_u03b4_1052_, lean_object* v_t_1053_, lean_object* v_k_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_t_1053_, v_k_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___boxed(lean_object* v_00_u03b4_1056_, lean_object* v_t_1057_, lean_object* v_k_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0(v_00_u03b4_1056_, v_t_1057_, v_k_1058_);
lean_dec(v_k_1058_);
lean_dec(v_t_1057_);
return v_res_1059_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(lean_object* v_as_1060_, size_t v_i_1061_, size_t v_stop_1062_, lean_object* v_b_1063_){
_start:
{
lean_object* v___y_1065_; uint8_t v___x_1069_; 
v___x_1069_ = lean_usize_dec_eq(v_i_1061_, v_stop_1062_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_array_uget_borrowed(v_as_1060_, v_i_1061_);
if (lean_obj_tag(v___x_1070_) == 0)
{
v___y_1065_ = v_b_1063_;
goto v___jp_1064_;
}
else
{
lean_object* v_fvarId_1071_; lean_object* v___x_1072_; 
v_fvarId_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_fvarId_1071_);
v___x_1072_ = lean_array_push(v_b_1063_, v_fvarId_1071_);
v___y_1065_ = v___x_1072_;
goto v___jp_1064_;
}
}
else
{
return v_b_1063_;
}
v___jp_1064_:
{
size_t v___x_1066_; size_t v___x_1067_; 
v___x_1066_ = ((size_t)1ULL);
v___x_1067_ = lean_usize_add(v_i_1061_, v___x_1066_);
v_i_1061_ = v___x_1067_;
v_b_1063_ = v___y_1065_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1060_ = stack[0].m_obj;
size_t v_i_1061_ = stack[1].m_num;
size_t v_stop_1062_ = stack[2].m_num;
lean_object* v_b_1063_ = stack[3].m_obj;
lean_object* v_res_1073_;
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1060_, v_i_1061_, v_stop_1062_, v_b_1063_);
stack->m_obj
 = v_res_1073_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0___boxed(lean_object* v_as_1074_, lean_object* v_i_1075_, lean_object* v_stop_1076_, lean_object* v_b_1077_){
_start:
{
size_t v_i_boxed_1078_; size_t v_stop_boxed_1079_; lean_object* v_res_1080_; 
v_i_boxed_1078_ = lean_unbox_usize(v_i_1075_);
lean_dec(v_i_1075_);
v_stop_boxed_1079_ = lean_unbox_usize(v_stop_1076_);
lean_dec(v_stop_1076_);
v_res_1080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1074_, v_i_boxed_1078_, v_stop_boxed_1079_, v_b_1077_);
lean_dec_ref(v_as_1074_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(lean_object* v_as_1081_, lean_object* v_start_1082_, lean_object* v_stop_1083_){
_start:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1085_ = lean_nat_dec_lt(v_start_1082_, v_stop_1083_);
if (v___x_1085_ == 0)
{
return v___x_1084_;
}
else
{
lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = lean_array_get_size(v_as_1081_);
v___x_1087_ = lean_nat_dec_le(v_stop_1083_, v___x_1086_);
if (v___x_1087_ == 0)
{
uint8_t v___x_1088_; 
v___x_1088_ = lean_nat_dec_lt(v_start_1082_, v___x_1086_);
if (v___x_1088_ == 0)
{
return v___x_1084_;
}
else
{
size_t v___x_1089_; size_t v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_usize_of_nat(v_start_1082_);
v___x_1090_ = lean_usize_of_nat(v___x_1086_);
v___x_1091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1081_, v___x_1089_, v___x_1090_, v___x_1084_);
return v___x_1091_;
}
}
else
{
size_t v___x_1092_; size_t v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = lean_usize_of_nat(v_start_1082_);
v___x_1093_ = lean_usize_of_nat(v_stop_1083_);
v___x_1094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1081_, v___x_1092_, v___x_1093_, v___x_1084_);
return v___x_1094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0___boxed(lean_object* v_as_1095_, lean_object* v_start_1096_, lean_object* v_stop_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(v_as_1095_, v_start_1096_, v_stop_1097_);
lean_dec(v_stop_1097_);
lean_dec(v_start_1096_);
lean_dec_ref(v_as_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(lean_object* v_ctx_1103_, lean_object* v_decl_1104_){
_start:
{
lean_object* v_args_1106_; lean_object* v_fvarId_1117_; lean_object* v_value_1118_; 
v_fvarId_1117_ = lean_ctor_get(v_decl_1104_, 0);
v_value_1118_ = lean_ctor_get(v_decl_1104_, 3);
switch(lean_obj_tag(v_value_1118_))
{
case 6:
{
lean_object* v_var_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v_var_1123_ = lean_ctor_get(v_value_1118_, 1);
v___x_1124_ = lean_unsigned_to_nat(1u);
v___x_1125_ = lean_mk_empty_array_with_capacity(v___x_1124_);
lean_inc(v_var_1123_);
v___x_1126_ = lean_array_push(v___x_1125_, v_var_1123_);
v___x_1127_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1103_, v___x_1126_, v_decl_1104_);
lean_dec_ref(v___x_1126_);
return v___x_1127_;
}
case 9:
{
lean_object* v_fn_1128_; 
v_fn_1128_ = lean_ctor_get(v_value_1118_, 0);
if (lean_obj_tag(v_fn_1128_) == 1)
{
lean_object* v_pre_1129_; 
v_pre_1129_ = lean_ctor_get(v_fn_1128_, 0);
if (lean_obj_tag(v_pre_1129_) == 1)
{
lean_object* v_pre_1130_; 
v_pre_1130_ = lean_ctor_get(v_pre_1129_, 0);
if (lean_obj_tag(v_pre_1130_) == 0)
{
lean_object* v_args_1131_; lean_object* v_str_1132_; lean_object* v_str_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_args_1131_ = lean_ctor_get(v_value_1118_, 1);
v_str_1132_ = lean_ctor_get(v_fn_1128_, 1);
v_str_1133_ = lean_ctor_get(v_pre_1129_, 1);
v___x_1134_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0));
v___x_1135_ = lean_string_dec_eq(v_str_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1136_ = lean_array_get_size(v_args_1131_);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = lean_nat_dec_eq(v___x_1136_, v___x_1137_);
if (v___x_1138_ == 0)
{
goto v___jp_1114_;
}
else
{
lean_inc(v_fvarId_1117_);
goto v___jp_1119_;
}
}
else
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__1));
v___x_1140_ = lean_string_dec_eq(v_str_1132_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__2));
v___x_1142_ = lean_string_dec_eq(v_str_1132_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__3));
v___x_1144_ = lean_string_dec_eq(v_str_1132_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_array_get_size(v_args_1131_);
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = lean_nat_dec_eq(v___x_1145_, v___x_1146_);
if (v___x_1147_ == 0)
{
goto v___jp_1114_;
}
else
{
lean_inc(v_fvarId_1117_);
goto v___jp_1119_;
}
}
else
{
lean_inc_ref(v_args_1131_);
v_args_1106_ = v_args_1131_;
goto v___jp_1105_;
}
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v_parents_1158_; lean_object* v___x_1159_; 
v___x_1148_ = lean_box(0);
v___x_1149_ = lean_unsigned_to_nat(1u);
v___x_1150_ = lean_array_get_borrowed(v___x_1148_, v_args_1131_, v___x_1149_);
v___x_1151_ = lean_unsigned_to_nat(2u);
v___x_1152_ = lean_array_get_borrowed(v___x_1148_, v_args_1131_, v___x_1151_);
v___x_1153_ = lean_mk_empty_array_with_capacity(v___x_1151_);
lean_inc(v___x_1150_);
v___x_1154_ = lean_array_push(v___x_1153_, v___x_1150_);
lean_inc(v___x_1152_);
v___x_1155_ = lean_array_push(v___x_1154_, v___x_1152_);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_array_get_size(v___x_1155_);
v_parents_1158_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(v___x_1155_, v___x_1156_, v___x_1157_);
lean_dec_ref(v___x_1155_);
v___x_1159_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1103_, v_parents_1158_, v_decl_1104_);
lean_dec_ref(v_parents_1158_);
return v___x_1159_;
}
}
else
{
lean_inc_ref(v_args_1131_);
v_args_1106_ = v_args_1131_;
goto v___jp_1105_;
}
}
}
else
{
lean_object* v_args_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v_args_1160_ = lean_ctor_get(v_value_1118_, 1);
v___x_1161_ = lean_array_get_size(v_args_1160_);
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = lean_nat_dec_eq(v___x_1161_, v___x_1162_);
if (v___x_1163_ == 0)
{
goto v___jp_1114_;
}
else
{
lean_inc(v_fvarId_1117_);
goto v___jp_1119_;
}
}
}
else
{
lean_object* v_args_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_args_1164_ = lean_ctor_get(v_value_1118_, 1);
v___x_1165_ = lean_array_get_size(v_args_1164_);
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = lean_nat_dec_eq(v___x_1165_, v___x_1166_);
if (v___x_1167_ == 0)
{
goto v___jp_1114_;
}
else
{
lean_inc(v_fvarId_1117_);
goto v___jp_1119_;
}
}
}
else
{
lean_object* v_args_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v_args_1168_ = lean_ctor_get(v_value_1118_, 1);
v___x_1169_ = lean_array_get_size(v_args_1168_);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_nat_dec_eq(v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
goto v___jp_1114_;
}
else
{
lean_inc(v_fvarId_1117_);
goto v___jp_1119_;
}
}
}
case 5:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1173_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1103_, v___x_1172_, v_decl_1104_);
return v___x_1173_;
}
case 12:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1175_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1103_, v___x_1174_, v_decl_1104_);
return v___x_1175_;
}
default: 
{
lean_dec_ref(v_decl_1104_);
return v_ctx_1103_;
}
}
v___jp_1105_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_unsigned_to_nat(1u);
v___x_1109_ = lean_array_get(v___x_1107_, v_args_1106_, v___x_1108_);
lean_dec_ref(v_args_1106_);
if (lean_obj_tag(v___x_1109_) == 1)
{
lean_object* v_fvarId_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_fvarId_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_fvarId_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = lean_mk_empty_array_with_capacity(v___x_1108_);
v___x_1112_ = lean_array_push(v___x_1111_, v_fvarId_1110_);
v___x_1113_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1103_, v___x_1112_, v_decl_1104_);
lean_dec_ref(v___x_1112_);
return v___x_1113_;
}
else
{
lean_dec(v___x_1109_);
lean_dec_ref(v_decl_1104_);
return v_ctx_1103_;
}
}
v___jp_1114_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1116_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1103_, v___x_1115_, v_decl_1104_);
return v___x_1116_;
}
v___jp_1119_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1121_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1103_, v___x_1120_, v_decl_1104_);
v___x_1122_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(v___x_1121_, v_fvarId_1117_);
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___lam__0(lean_object* v_x1_1176_, lean_object* v_x2_1177_){
_start:
{
lean_object* v_resetTargets_1178_; lean_object* v_unconditionalBorrows_1179_; lean_object* v_derivedValMap_1180_; lean_object* v_varMap_1181_; lean_object* v_jpLiveVarMap_1182_; lean_object* v_idx_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1204_; 
v_resetTargets_1178_ = lean_ctor_get(v_x1_1176_, 0);
v_unconditionalBorrows_1179_ = lean_ctor_get(v_x1_1176_, 1);
v_derivedValMap_1180_ = lean_ctor_get(v_x1_1176_, 2);
v_varMap_1181_ = lean_ctor_get(v_x1_1176_, 3);
v_jpLiveVarMap_1182_ = lean_ctor_get(v_x1_1176_, 4);
v_idx_1183_ = lean_ctor_get(v_x1_1176_, 5);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_x1_1176_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1185_ = v_x1_1176_;
v_isShared_1186_ = v_isSharedCheck_1204_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_idx_1183_);
lean_inc(v_jpLiveVarMap_1182_);
lean_inc(v_varMap_1181_);
lean_inc(v_derivedValMap_1180_);
lean_inc(v_unconditionalBorrows_1179_);
lean_inc(v_resetTargets_1178_);
lean_dec(v_x1_1176_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1204_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_fvarId_1187_; lean_object* v_type_1188_; uint8_t v_borrow_1189_; uint8_t v___x_1190_; uint8_t v___x_1191_; uint8_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v_varMap_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v_ctx_1199_; 
v_fvarId_1187_ = lean_ctor_get(v_x2_1177_, 0);
lean_inc_n(v_fvarId_1187_, 2);
v_type_1188_ = lean_ctor_get(v_x2_1177_, 2);
lean_inc_ref(v_type_1188_);
v_borrow_1189_ = lean_ctor_get_uint8(v_x2_1177_, sizeof(void*)*3);
lean_dec_ref(v_x2_1177_);
v___x_1190_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1188_);
v___x_1191_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1188_);
lean_dec_ref(v_type_1188_);
v___x_1192_ = 0;
v___x_1193_ = lean_box(0);
lean_inc(v_idx_1183_);
v___x_1194_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1194_, 0, v_idx_1183_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*2, v___x_1190_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*2 + 1, v___x_1191_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*2 + 2, v___x_1192_);
v_varMap_1195_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1187_, v___x_1194_, v_varMap_1181_);
v___x_1196_ = lean_unsigned_to_nat(1u);
v___x_1197_ = lean_nat_add(v_idx_1183_, v___x_1196_);
lean_dec(v_idx_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 5, v___x_1197_);
lean_ctor_set(v___x_1185_, 3, v_varMap_1195_);
v_ctx_1199_ = v___x_1185_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_resetTargets_1178_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_unconditionalBorrows_1179_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_derivedValMap_1180_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_varMap_1195_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_jpLiveVarMap_1182_);
lean_ctor_set(v_reuseFailAlloc_1203_, 5, v___x_1197_);
v_ctx_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v_ctx_1201_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
lean_inc(v_fvarId_1187_);
v_ctx_1201_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1199_, v___x_1200_, v_fvarId_1187_);
if (v_borrow_1189_ == 0)
{
lean_dec(v_fvarId_1187_);
return v_ctx_1201_;
}
else
{
if (v___x_1190_ == 0)
{
lean_dec(v_fvarId_1187_);
return v_ctx_1201_;
}
else
{
lean_object* v___x_1202_; 
v___x_1202_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(v_ctx_1201_, v_fvarId_1187_);
return v___x_1202_;
}
}
}
}
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(lean_object* v_ps_1206_, lean_object* v_x_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_array_get_size(v_ps_1206_);
v___x_1217_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v___x_1218_ = lean_nat_dec_lt(v___x_1215_, v___x_1216_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; 
lean_dec_ref(v_ps_1206_);
lean_inc(v_a_1213_);
lean_inc_ref(v_a_1212_);
lean_inc(v_a_1211_);
lean_inc_ref(v_a_1210_);
lean_inc(v_a_1209_);
lean_inc_ref(v_a_1208_);
v___x_1219_ = lean_apply_7(v_x_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, lean_box(0));
return v___x_1219_;
}
else
{
lean_object* v___f_1220_; uint8_t v___x_1221_; 
v___f_1220_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___x_1221_ = lean_nat_dec_le(v___x_1216_, v___x_1216_);
if (v___x_1221_ == 0)
{
if (v___x_1218_ == 0)
{
lean_object* v___x_1222_; 
lean_dec_ref(v_ps_1206_);
lean_inc(v_a_1213_);
lean_inc_ref(v_a_1212_);
lean_inc(v_a_1211_);
lean_inc_ref(v_a_1210_);
lean_inc(v_a_1209_);
lean_inc_ref(v_a_1208_);
v___x_1222_ = lean_apply_7(v_x_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, lean_box(0));
return v___x_1222_;
}
else
{
size_t v___x_1223_; size_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1223_ = ((size_t)0ULL);
v___x_1224_ = lean_usize_of_nat(v___x_1216_);
lean_inc_ref(v_a_1208_);
v___x_1225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1217_, v___f_1220_, v_ps_1206_, v___x_1223_, v___x_1224_, v_a_1208_);
lean_inc(v_a_1213_);
lean_inc_ref(v_a_1212_);
lean_inc(v_a_1211_);
lean_inc_ref(v_a_1210_);
lean_inc(v_a_1209_);
v___x_1226_ = lean_apply_7(v_x_1207_, v___x_1225_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, lean_box(0));
return v___x_1226_;
}
}
else
{
size_t v___x_1227_; size_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1227_ = ((size_t)0ULL);
v___x_1228_ = lean_usize_of_nat(v___x_1216_);
lean_inc_ref(v_a_1208_);
v___x_1229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1217_, v___f_1220_, v_ps_1206_, v___x_1227_, v___x_1228_, v_a_1208_);
lean_inc(v_a_1213_);
lean_inc_ref(v_a_1212_);
lean_inc(v_a_1211_);
lean_inc_ref(v_a_1210_);
lean_inc(v_a_1209_);
v___x_1230_ = lean_apply_7(v_x_1207_, v___x_1229_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, lean_box(0));
return v___x_1230_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ps_1206_ = stack[0].m_obj;
lean_object* v_x_1207_ = stack[1].m_obj;
lean_object* v_a_1208_ = stack[2].m_obj;
lean_object* v_a_1209_ = stack[3].m_obj;
lean_object* v_a_1210_ = stack[4].m_obj;
lean_object* v_a_1211_ = stack[5].m_obj;
lean_object* v_a_1212_ = stack[6].m_obj;
lean_object* v_a_1213_ = stack[7].m_obj;
lean_object* v_res_1231_;
v_res_1231_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(v_ps_1206_, v_x_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
stack->m_obj
 = v_res_1231_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___boxed(lean_object* v_ps_1232_, lean_object* v_x_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(v_ps_1232_, v_x_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
return v_res_1241_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(lean_object* v_00_u03b1_1242_, lean_object* v_ps_1243_, lean_object* v_x_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = lean_array_get_size(v_ps_1243_);
v___x_1254_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v___x_1255_ = lean_nat_dec_lt(v___x_1252_, v___x_1253_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_dec_ref(v_ps_1243_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc(v_a_1246_);
lean_inc_ref(v_a_1245_);
v___x_1256_ = lean_apply_7(v_x_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, lean_box(0));
return v___x_1256_;
}
else
{
lean_object* v___f_1257_; uint8_t v___x_1258_; 
v___f_1257_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___x_1258_ = lean_nat_dec_le(v___x_1253_, v___x_1253_);
if (v___x_1258_ == 0)
{
if (v___x_1255_ == 0)
{
lean_object* v___x_1259_; 
lean_dec_ref(v_ps_1243_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc(v_a_1246_);
lean_inc_ref(v_a_1245_);
v___x_1259_ = lean_apply_7(v_x_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, lean_box(0));
return v___x_1259_;
}
else
{
size_t v___x_1260_; size_t v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = ((size_t)0ULL);
v___x_1261_ = lean_usize_of_nat(v___x_1253_);
lean_inc_ref(v_a_1245_);
v___x_1262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1254_, v___f_1257_, v_ps_1243_, v___x_1260_, v___x_1261_, v_a_1245_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc(v_a_1246_);
v___x_1263_ = lean_apply_7(v_x_1244_, v___x_1262_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, lean_box(0));
return v___x_1263_;
}
}
else
{
size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1264_ = ((size_t)0ULL);
v___x_1265_ = lean_usize_of_nat(v___x_1253_);
lean_inc_ref(v_a_1245_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1254_, v___f_1257_, v_ps_1243_, v___x_1264_, v___x_1265_, v_a_1245_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc(v_a_1246_);
v___x_1267_ = lean_apply_7(v_x_1244_, v___x_1266_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, lean_box(0));
return v___x_1267_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_ps_1243_ = stack[1].m_obj;
lean_object* v_x_1244_ = stack[2].m_obj;
lean_object* v_a_1245_ = stack[3].m_obj;
lean_object* v_a_1246_ = stack[4].m_obj;
lean_object* v_a_1247_ = stack[5].m_obj;
lean_object* v_a_1248_ = stack[6].m_obj;
lean_object* v_a_1249_ = stack[7].m_obj;
lean_object* v_a_1250_ = stack[8].m_obj;
lean_object* v_res_1268_;
v_res_1268_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(lean_box(0), v_ps_1243_, v_x_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
stack->m_obj
 = v_res_1268_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___boxed(lean_object* v_00_u03b1_1269_, lean_object* v_ps_1270_, lean_object* v_x_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(v_00_u03b1_1269_, v_ps_1270_, v_x_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
return v_res_1279_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(lean_object* v_decl_1280_, lean_object* v_x_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_fvarId_1289_; lean_object* v_type_1290_; lean_object* v_value_1291_; lean_object* v___y_1293_; 
v_fvarId_1289_ = lean_ctor_get(v_decl_1280_, 0);
v_type_1290_ = lean_ctor_get(v_decl_1280_, 2);
v_value_1291_ = lean_ctor_get(v_decl_1280_, 3);
if (lean_obj_tag(v_value_1291_) == 5)
{
lean_object* v_i_1310_; lean_object* v___x_1311_; 
v_i_1310_ = lean_ctor_get(v_value_1291_, 0);
lean_inc_ref(v_i_1310_);
v___x_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1311_, 0, v_i_1310_);
v___y_1293_ = v___x_1311_;
goto v___jp_1292_;
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_box(0);
v___y_1293_ = v___x_1312_;
goto v___jp_1292_;
}
v___jp_1292_:
{
lean_object* v_resetTargets_1294_; lean_object* v_unconditionalBorrows_1295_; lean_object* v_derivedValMap_1296_; lean_object* v_varMap_1297_; lean_object* v_jpLiveVarMap_1298_; lean_object* v_idx_1299_; uint8_t v___x_1300_; uint8_t v___x_1301_; uint8_t v___x_1302_; lean_object* v_varInfo_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v_ctx_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_resetTargets_1294_ = lean_ctor_get(v_a_1282_, 0);
v_unconditionalBorrows_1295_ = lean_ctor_get(v_a_1282_, 1);
v_derivedValMap_1296_ = lean_ctor_get(v_a_1282_, 2);
v_varMap_1297_ = lean_ctor_get(v_a_1282_, 3);
v_jpLiveVarMap_1298_ = lean_ctor_get(v_a_1282_, 4);
v_idx_1299_ = lean_ctor_get(v_a_1282_, 5);
v___x_1300_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1290_);
v___x_1301_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1290_);
v___x_1302_ = l_Lean_Compiler_LCNF_LetValue_isPersistent(v_value_1291_);
lean_inc(v_idx_1299_);
v_varInfo_1303_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_varInfo_1303_, 0, v_idx_1299_);
lean_ctor_set(v_varInfo_1303_, 1, v___y_1293_);
lean_ctor_set_uint8(v_varInfo_1303_, sizeof(void*)*2, v___x_1300_);
lean_ctor_set_uint8(v_varInfo_1303_, sizeof(void*)*2 + 1, v___x_1301_);
lean_ctor_set_uint8(v_varInfo_1303_, sizeof(void*)*2 + 2, v___x_1302_);
lean_inc(v_varMap_1297_);
lean_inc(v_fvarId_1289_);
v___x_1304_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1289_, v_varInfo_1303_, v_varMap_1297_);
v___x_1305_ = lean_unsigned_to_nat(1u);
v___x_1306_ = lean_nat_add(v_idx_1299_, v___x_1305_);
lean_inc(v_jpLiveVarMap_1298_);
lean_inc(v_derivedValMap_1296_);
lean_inc(v_unconditionalBorrows_1295_);
lean_inc_ref(v_resetTargets_1294_);
v_ctx_1307_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_ctx_1307_, 0, v_resetTargets_1294_);
lean_ctor_set(v_ctx_1307_, 1, v_unconditionalBorrows_1295_);
lean_ctor_set(v_ctx_1307_, 2, v_derivedValMap_1296_);
lean_ctor_set(v_ctx_1307_, 3, v___x_1304_);
lean_ctor_set(v_ctx_1307_, 4, v_jpLiveVarMap_1298_);
lean_ctor_set(v_ctx_1307_, 5, v___x_1306_);
v___x_1308_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(v_ctx_1307_, v_decl_1280_);
lean_inc(v_a_1287_);
lean_inc_ref(v_a_1286_);
lean_inc(v_a_1285_);
lean_inc_ref(v_a_1284_);
lean_inc(v_a_1283_);
v___x_1309_ = lean_apply_7(v_x_1281_, v___x_1308_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, lean_box(0));
return v___x_1309_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1280_ = stack[0].m_obj;
lean_object* v_x_1281_ = stack[1].m_obj;
lean_object* v_a_1282_ = stack[2].m_obj;
lean_object* v_a_1283_ = stack[3].m_obj;
lean_object* v_a_1284_ = stack[4].m_obj;
lean_object* v_a_1285_ = stack[5].m_obj;
lean_object* v_a_1286_ = stack[6].m_obj;
lean_object* v_a_1287_ = stack[7].m_obj;
lean_object* v_res_1313_;
v_res_1313_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(v_decl_1280_, v_x_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
stack->m_obj
 = v_res_1313_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg___boxed(lean_object* v_decl_1314_, lean_object* v_x_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(v_decl_1314_, v_x_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1323_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(lean_object* v_00_u03b1_1324_, lean_object* v_decl_1325_, lean_object* v_x_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_fvarId_1334_; lean_object* v_type_1335_; lean_object* v_value_1336_; lean_object* v___y_1338_; 
v_fvarId_1334_ = lean_ctor_get(v_decl_1325_, 0);
v_type_1335_ = lean_ctor_get(v_decl_1325_, 2);
v_value_1336_ = lean_ctor_get(v_decl_1325_, 3);
if (lean_obj_tag(v_value_1336_) == 5)
{
lean_object* v_i_1355_; lean_object* v___x_1356_; 
v_i_1355_ = lean_ctor_get(v_value_1336_, 0);
lean_inc_ref(v_i_1355_);
v___x_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_i_1355_);
v___y_1338_ = v___x_1356_;
goto v___jp_1337_;
}
else
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_box(0);
v___y_1338_ = v___x_1357_;
goto v___jp_1337_;
}
v___jp_1337_:
{
lean_object* v_resetTargets_1339_; lean_object* v_unconditionalBorrows_1340_; lean_object* v_derivedValMap_1341_; lean_object* v_varMap_1342_; lean_object* v_jpLiveVarMap_1343_; lean_object* v_idx_1344_; uint8_t v___x_1345_; uint8_t v___x_1346_; uint8_t v___x_1347_; lean_object* v_varInfo_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v_ctx_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_resetTargets_1339_ = lean_ctor_get(v_a_1327_, 0);
v_unconditionalBorrows_1340_ = lean_ctor_get(v_a_1327_, 1);
v_derivedValMap_1341_ = lean_ctor_get(v_a_1327_, 2);
v_varMap_1342_ = lean_ctor_get(v_a_1327_, 3);
v_jpLiveVarMap_1343_ = lean_ctor_get(v_a_1327_, 4);
v_idx_1344_ = lean_ctor_get(v_a_1327_, 5);
v___x_1345_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1335_);
v___x_1346_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1335_);
v___x_1347_ = l_Lean_Compiler_LCNF_LetValue_isPersistent(v_value_1336_);
lean_inc(v_idx_1344_);
v_varInfo_1348_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_varInfo_1348_, 0, v_idx_1344_);
lean_ctor_set(v_varInfo_1348_, 1, v___y_1338_);
lean_ctor_set_uint8(v_varInfo_1348_, sizeof(void*)*2, v___x_1345_);
lean_ctor_set_uint8(v_varInfo_1348_, sizeof(void*)*2 + 1, v___x_1346_);
lean_ctor_set_uint8(v_varInfo_1348_, sizeof(void*)*2 + 2, v___x_1347_);
lean_inc(v_varMap_1342_);
lean_inc(v_fvarId_1334_);
v___x_1349_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1334_, v_varInfo_1348_, v_varMap_1342_);
v___x_1350_ = lean_unsigned_to_nat(1u);
v___x_1351_ = lean_nat_add(v_idx_1344_, v___x_1350_);
lean_inc(v_jpLiveVarMap_1343_);
lean_inc(v_derivedValMap_1341_);
lean_inc(v_unconditionalBorrows_1340_);
lean_inc_ref(v_resetTargets_1339_);
v_ctx_1352_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_ctx_1352_, 0, v_resetTargets_1339_);
lean_ctor_set(v_ctx_1352_, 1, v_unconditionalBorrows_1340_);
lean_ctor_set(v_ctx_1352_, 2, v_derivedValMap_1341_);
lean_ctor_set(v_ctx_1352_, 3, v___x_1349_);
lean_ctor_set(v_ctx_1352_, 4, v_jpLiveVarMap_1343_);
lean_ctor_set(v_ctx_1352_, 5, v___x_1351_);
v___x_1353_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(v_ctx_1352_, v_decl_1325_);
lean_inc(v_a_1332_);
lean_inc_ref(v_a_1331_);
lean_inc(v_a_1330_);
lean_inc_ref(v_a_1329_);
lean_inc(v_a_1328_);
v___x_1354_ = lean_apply_7(v_x_1326_, v___x_1353_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, lean_box(0));
return v___x_1354_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1325_ = stack[1].m_obj;
lean_object* v_x_1326_ = stack[2].m_obj;
lean_object* v_a_1327_ = stack[3].m_obj;
lean_object* v_a_1328_ = stack[4].m_obj;
lean_object* v_a_1329_ = stack[5].m_obj;
lean_object* v_a_1330_ = stack[6].m_obj;
lean_object* v_a_1331_ = stack[7].m_obj;
lean_object* v_a_1332_ = stack[8].m_obj;
lean_object* v_res_1358_;
v_res_1358_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(lean_box(0), v_decl_1325_, v_x_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
stack->m_obj
 = v_res_1358_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___boxed(lean_object* v_00_u03b1_1359_, lean_object* v_decl_1360_, lean_object* v_x_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(v_00_u03b1_1359_, v_decl_1360_, v_x_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
return v_res_1369_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(lean_object* v_discr_1370_, lean_object* v_c_1371_, lean_object* v_x_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_resetTargets_1380_; lean_object* v_unconditionalBorrows_1381_; lean_object* v_derivedValMap_1382_; lean_object* v_varMap_1383_; lean_object* v_jpLiveVarMap_1384_; lean_object* v_idx_1385_; lean_object* v___y_1387_; lean_object* v___f_1392_; lean_object* v___x_1393_; 
v_resetTargets_1380_ = lean_ctor_get(v_a_1373_, 0);
v_unconditionalBorrows_1381_ = lean_ctor_get(v_a_1373_, 1);
v_derivedValMap_1382_ = lean_ctor_get(v_a_1373_, 2);
v_varMap_1383_ = lean_ctor_get(v_a_1373_, 3);
v_jpLiveVarMap_1384_ = lean_ctor_get(v_a_1373_, 4);
v_idx_1385_ = lean_ctor_get(v_a_1373_, 5);
v___f_1392_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_discr_1370_);
lean_inc(v_varMap_1383_);
v___x_1393_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1392_, v_varMap_1383_, v_discr_1370_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_dec_ref(v_c_1371_);
lean_dec(v_discr_1370_);
lean_inc(v_varMap_1383_);
v___y_1387_ = v_varMap_1383_;
goto v___jp_1386_;
}
else
{
lean_object* v_val_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1415_; 
v_val_1394_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1396_ = v___x_1393_;
v_isShared_1397_ = v_isSharedCheck_1415_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_val_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1415_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
uint8_t v_persistent_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1412_; 
v_persistent_1398_ = lean_ctor_get_uint8(v_val_1394_, sizeof(void*)*2 + 2);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_val_1394_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; lean_object* v_unused_1414_; 
v_unused_1413_ = lean_ctor_get(v_val_1394_, 1);
lean_dec(v_unused_1413_);
v_unused_1414_ = lean_ctor_get(v_val_1394_, 0);
lean_dec(v_unused_1414_);
v___x_1400_ = v_val_1394_;
v_isShared_1401_ = v_isSharedCheck_1412_;
goto v_resetjp_1399_;
}
else
{
lean_dec(v_val_1394_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1412_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
uint8_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1402_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_c_1371_);
v___x_1403_ = lean_unsigned_to_nat(1u);
v___x_1404_ = lean_nat_add(v_idx_1385_, v___x_1403_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v_c_1371_);
v___x_1406_ = v___x_1396_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_c_1371_);
v___x_1406_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1408_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v___x_1406_);
lean_ctor_set(v___x_1400_, 0, v___x_1404_);
v___x_1408_ = v___x_1400_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___x_1406_);
lean_ctor_set_uint8(v_reuseFailAlloc_1410_, sizeof(void*)*2 + 2, v_persistent_1398_);
v___x_1408_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; 
lean_ctor_set_uint8(v___x_1408_, sizeof(void*)*2, v___x_1402_);
lean_ctor_set_uint8(v___x_1408_, sizeof(void*)*2 + 1, v___x_1402_);
lean_inc(v_varMap_1383_);
v___x_1409_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_1370_, v___x_1408_, v_varMap_1383_);
v___y_1387_ = v___x_1409_;
goto v___jp_1386_;
}
}
}
}
}
v___jp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1388_ = lean_unsigned_to_nat(1u);
v___x_1389_ = lean_nat_add(v_idx_1385_, v___x_1388_);
lean_inc(v_jpLiveVarMap_1384_);
lean_inc(v_derivedValMap_1382_);
lean_inc(v_unconditionalBorrows_1381_);
lean_inc_ref(v_resetTargets_1380_);
v___x_1390_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1390_, 0, v_resetTargets_1380_);
lean_ctor_set(v___x_1390_, 1, v_unconditionalBorrows_1381_);
lean_ctor_set(v___x_1390_, 2, v_derivedValMap_1382_);
lean_ctor_set(v___x_1390_, 3, v___y_1387_);
lean_ctor_set(v___x_1390_, 4, v_jpLiveVarMap_1384_);
lean_ctor_set(v___x_1390_, 5, v___x_1389_);
lean_inc(v_a_1378_);
lean_inc_ref(v_a_1377_);
lean_inc(v_a_1376_);
lean_inc_ref(v_a_1375_);
lean_inc(v_a_1374_);
v___x_1391_ = lean_apply_7(v_x_1372_, v___x_1390_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, lean_box(0));
return v___x_1391_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_1370_ = stack[0].m_obj;
lean_object* v_c_1371_ = stack[1].m_obj;
lean_object* v_x_1372_ = stack[2].m_obj;
lean_object* v_a_1373_ = stack[3].m_obj;
lean_object* v_a_1374_ = stack[4].m_obj;
lean_object* v_a_1375_ = stack[5].m_obj;
lean_object* v_a_1376_ = stack[6].m_obj;
lean_object* v_a_1377_ = stack[7].m_obj;
lean_object* v_a_1378_ = stack[8].m_obj;
lean_object* v_res_1416_;
v_res_1416_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(v_discr_1370_, v_c_1371_, v_x_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
stack->m_obj
 = v_res_1416_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg___boxed(lean_object* v_discr_1417_, lean_object* v_c_1418_, lean_object* v_x_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(v_discr_1417_, v_c_1418_, v_x_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
return v_res_1427_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(lean_object* v_00_u03b1_1428_, lean_object* v_discr_1429_, lean_object* v_c_1430_, lean_object* v_x_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_resetTargets_1439_; lean_object* v_unconditionalBorrows_1440_; lean_object* v_derivedValMap_1441_; lean_object* v_varMap_1442_; lean_object* v_jpLiveVarMap_1443_; lean_object* v_idx_1444_; lean_object* v___y_1446_; lean_object* v___f_1451_; lean_object* v___x_1452_; 
v_resetTargets_1439_ = lean_ctor_get(v_a_1432_, 0);
v_unconditionalBorrows_1440_ = lean_ctor_get(v_a_1432_, 1);
v_derivedValMap_1441_ = lean_ctor_get(v_a_1432_, 2);
v_varMap_1442_ = lean_ctor_get(v_a_1432_, 3);
v_jpLiveVarMap_1443_ = lean_ctor_get(v_a_1432_, 4);
v_idx_1444_ = lean_ctor_get(v_a_1432_, 5);
v___f_1451_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_discr_1429_);
lean_inc(v_varMap_1442_);
v___x_1452_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1451_, v_varMap_1442_, v_discr_1429_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_dec_ref(v_c_1430_);
lean_dec(v_discr_1429_);
lean_inc(v_varMap_1442_);
v___y_1446_ = v_varMap_1442_;
goto v___jp_1445_;
}
else
{
lean_object* v_val_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1474_; 
v_val_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1474_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_val_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1474_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
uint8_t v_persistent_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1471_; 
v_persistent_1457_ = lean_ctor_get_uint8(v_val_1453_, sizeof(void*)*2 + 2);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_val_1453_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; lean_object* v_unused_1473_; 
v_unused_1472_ = lean_ctor_get(v_val_1453_, 1);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_val_1453_, 0);
lean_dec(v_unused_1473_);
v___x_1459_ = v_val_1453_;
v_isShared_1460_ = v_isSharedCheck_1471_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v_val_1453_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1471_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
uint8_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1461_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_c_1430_);
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_add(v_idx_1444_, v___x_1462_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v_c_1430_);
v___x_1465_ = v___x_1455_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_c_1430_);
v___x_1465_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1467_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 1, v___x_1465_);
lean_ctor_set(v___x_1459_, 0, v___x_1463_);
v___x_1467_ = v___x_1459_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v___x_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*2 + 2, v_persistent_1457_);
v___x_1467_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1468_; 
lean_ctor_set_uint8(v___x_1467_, sizeof(void*)*2, v___x_1461_);
lean_ctor_set_uint8(v___x_1467_, sizeof(void*)*2 + 1, v___x_1461_);
lean_inc(v_varMap_1442_);
v___x_1468_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_1429_, v___x_1467_, v_varMap_1442_);
v___y_1446_ = v___x_1468_;
goto v___jp_1445_;
}
}
}
}
}
v___jp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_nat_add(v_idx_1444_, v___x_1447_);
lean_inc(v_jpLiveVarMap_1443_);
lean_inc(v_derivedValMap_1441_);
lean_inc(v_unconditionalBorrows_1440_);
lean_inc_ref(v_resetTargets_1439_);
v___x_1449_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1449_, 0, v_resetTargets_1439_);
lean_ctor_set(v___x_1449_, 1, v_unconditionalBorrows_1440_);
lean_ctor_set(v___x_1449_, 2, v_derivedValMap_1441_);
lean_ctor_set(v___x_1449_, 3, v___y_1446_);
lean_ctor_set(v___x_1449_, 4, v_jpLiveVarMap_1443_);
lean_ctor_set(v___x_1449_, 5, v___x_1448_);
lean_inc(v_a_1437_);
lean_inc_ref(v_a_1436_);
lean_inc(v_a_1435_);
lean_inc_ref(v_a_1434_);
lean_inc(v_a_1433_);
v___x_1450_ = lean_apply_7(v_x_1431_, v___x_1449_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, lean_box(0));
return v___x_1450_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_1429_ = stack[1].m_obj;
lean_object* v_c_1430_ = stack[2].m_obj;
lean_object* v_x_1431_ = stack[3].m_obj;
lean_object* v_a_1432_ = stack[4].m_obj;
lean_object* v_a_1433_ = stack[5].m_obj;
lean_object* v_a_1434_ = stack[6].m_obj;
lean_object* v_a_1435_ = stack[7].m_obj;
lean_object* v_a_1436_ = stack[8].m_obj;
lean_object* v_a_1437_ = stack[9].m_obj;
lean_object* v_res_1475_;
v_res_1475_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(lean_box(0), v_discr_1429_, v_c_1430_, v_x_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
stack->m_obj
 = v_res_1475_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___boxed(lean_object* v_00_u03b1_1476_, lean_object* v_discr_1477_, lean_object* v_c_1478_, lean_object* v_x_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(v_00_u03b1_1476_, v_discr_1477_, v_c_1478_, v_x_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
return v_res_1487_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(lean_object* v_x_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1496_ = lean_st_ref_get(v_a_1490_);
v___x_1497_ = lean_st_ref_take(v_a_1490_);
lean_dec(v___x_1497_);
v___x_1498_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_1499_ = lean_st_ref_put(v_a_1490_, v___x_1498_);
lean_inc(v_a_1494_);
lean_inc_ref(v_a_1493_);
lean_inc(v_a_1492_);
lean_inc_ref(v_a_1491_);
lean_inc(v_a_1490_);
lean_inc_ref(v_a_1489_);
v___x_1500_ = lean_apply_7(v_x_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, lean_box(0));
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1512_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1512_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1512_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1505_ = lean_st_ref_get(v_a_1490_);
v___x_1506_ = lean_st_ref_take(v_a_1490_);
lean_dec(v___x_1506_);
v___x_1507_ = lean_st_ref_put(v_a_1490_, v___x_1496_);
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v_a_1501_);
lean_ctor_set(v___x_1508_, 1, v___x_1505_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v___x_1508_);
v___x_1510_ = v___x_1503_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v___x_1496_);
v_a_1513_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1500_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1500_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1488_ = stack[0].m_obj;
lean_object* v_a_1489_ = stack[1].m_obj;
lean_object* v_a_1490_ = stack[2].m_obj;
lean_object* v_a_1491_ = stack[3].m_obj;
lean_object* v_a_1492_ = stack[4].m_obj;
lean_object* v_a_1493_ = stack[5].m_obj;
lean_object* v_a_1494_ = stack[6].m_obj;
lean_object* v_res_1521_;
v_res_1521_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(v_x_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
stack->m_obj
 = v_res_1521_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg___boxed(lean_object* v_x_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(v_x_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
return v_res_1530_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(lean_object* v_00_u03b1_1531_, lean_object* v_x_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1540_ = lean_st_ref_get(v_a_1534_);
v___x_1541_ = lean_st_ref_take(v_a_1534_);
lean_dec(v___x_1541_);
v___x_1542_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_1543_ = lean_st_ref_put(v_a_1534_, v___x_1542_);
lean_inc(v_a_1538_);
lean_inc_ref(v_a_1537_);
lean_inc(v_a_1536_);
lean_inc_ref(v_a_1535_);
lean_inc(v_a_1534_);
lean_inc_ref(v_a_1533_);
v___x_1544_ = lean_apply_7(v_x_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, lean_box(0));
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1556_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1556_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1556_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1549_ = lean_st_ref_get(v_a_1534_);
v___x_1550_ = lean_st_ref_take(v_a_1534_);
lean_dec(v___x_1550_);
v___x_1551_ = lean_st_ref_put(v_a_1534_, v___x_1540_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_a_1545_);
lean_ctor_set(v___x_1552_, 1, v___x_1549_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1552_);
v___x_1554_ = v___x_1547_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v___x_1540_);
v_a_1557_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1544_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1544_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1532_ = stack[1].m_obj;
lean_object* v_a_1533_ = stack[2].m_obj;
lean_object* v_a_1534_ = stack[3].m_obj;
lean_object* v_a_1535_ = stack[4].m_obj;
lean_object* v_a_1536_ = stack[5].m_obj;
lean_object* v_a_1537_ = stack[6].m_obj;
lean_object* v_a_1538_ = stack[7].m_obj;
lean_object* v_res_1565_;
v_res_1565_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(lean_box(0), v_x_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
stack->m_obj
 = v_res_1565_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___boxed(lean_object* v_00_u03b1_1566_, lean_object* v_x_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(v_00_u03b1_1566_, v_x_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
return v_res_1575_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0(lean_object* v_liveVars_1576_, uint8_t v___x_1577_, lean_object* v___x_1578_, lean_object* v___x_1579_, lean_object* v_v_1580_){
_start:
{
uint8_t v___y_1582_; lean_object* v_vars_1584_; lean_object* v_borrows_1585_; uint8_t v___x_1586_; 
v_vars_1584_ = lean_ctor_get(v_liveVars_1576_, 0);
v_borrows_1585_ = lean_ctor_get(v_liveVars_1576_, 1);
lean_inc(v_v_1580_);
lean_inc_ref(v___x_1579_);
lean_inc_ref(v___x_1578_);
v___x_1586_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1578_, v___x_1579_, v_vars_1584_, v_v_1580_);
if (v___x_1586_ == 0)
{
uint8_t v___x_1587_; 
v___x_1587_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1578_, v___x_1579_, v_borrows_1585_, v_v_1580_);
v___y_1582_ = v___x_1587_;
goto v___jp_1581_;
}
else
{
lean_dec(v_v_1580_);
lean_dec_ref(v___x_1579_);
lean_dec_ref(v___x_1578_);
v___y_1582_ = v___x_1586_;
goto v___jp_1581_;
}
v___jp_1581_:
{
if (v___y_1582_ == 0)
{
return v___x_1577_;
}
else
{
uint8_t v___x_1583_; 
v___x_1583_ = 0;
return v___x_1583_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_liveVars_1576_ = stack[0].m_obj;
uint8_t v___x_1577_ = stack[1].m_num;
lean_object* v___x_1578_ = stack[2].m_obj;
lean_object* v___x_1579_ = stack[3].m_obj;
lean_object* v_v_1580_ = stack[4].m_obj;
uint8_t v_res_1588_;
v_res_1588_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0(v_liveVars_1576_, v___x_1577_, v___x_1578_, v___x_1579_, v_v_1580_);
stack->m_num = v_res_1588_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0___boxed(lean_object* v_liveVars_1589_, lean_object* v___x_1590_, lean_object* v___x_1591_, lean_object* v___x_1592_, lean_object* v_v_1593_){
_start:
{
uint8_t v___x_362__boxed_1594_; uint8_t v_res_1595_; lean_object* v_r_1596_; 
v___x_362__boxed_1594_ = lean_unbox(v___x_1590_);
v_res_1595_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0(v_liveVars_1589_, v___x_362__boxed_1594_, v___x_1591_, v___x_1592_, v_v_1593_);
lean_dec_ref(v_liveVars_1589_);
v_r_1596_ = lean_box(v_res_1595_);
return v_r_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1(lean_object* v___f_1597_, lean_object* v___x_1598_, lean_object* v_derivedValMap_1599_, lean_object* v_shouldAdd_1600_, lean_object* v___x_1601_, lean_object* v___x_1602_, lean_object* v_liveVars_1603_, lean_object* v_child_1604_){
_start:
{
lean_object* v_cinfo_1621_; lean_object* v_parents_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
lean_inc(v_child_1604_);
lean_inc(v_derivedValMap_1599_);
v_cinfo_1621_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_1597_, v___x_1598_, v_derivedValMap_1599_, v_child_1604_);
v_parents_1622_ = lean_ctor_get(v_cinfo_1621_, 0);
lean_inc_ref(v_parents_1622_);
lean_dec(v_cinfo_1621_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_array_get_size(v_parents_1622_);
v___x_1625_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v___x_1626_ = lean_nat_dec_lt(v___x_1623_, v___x_1624_);
if (v___x_1626_ == 0)
{
lean_dec_ref(v_parents_1622_);
goto v___jp_1605_;
}
else
{
if (v___x_1626_ == 0)
{
lean_dec_ref(v_parents_1622_);
goto v___jp_1605_;
}
else
{
lean_object* v___x_1627_; lean_object* v___f_1628_; size_t v___x_1629_; size_t v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1627_ = lean_box(v___x_1626_);
lean_inc_ref(v___x_1602_);
lean_inc_ref(v___x_1601_);
lean_inc_ref(v_liveVars_1603_);
v___f_1628_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1628_, 0, v_liveVars_1603_);
lean_closure_set(v___f_1628_, 1, v___x_1627_);
lean_closure_set(v___f_1628_, 2, v___x_1601_);
lean_closure_set(v___f_1628_, 3, v___x_1602_);
v___x_1629_ = ((size_t)0ULL);
v___x_1630_ = lean_usize_of_nat(v___x_1624_);
v___x_1631_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1625_, v___f_1628_, v_parents_1622_, v___x_1629_, v___x_1630_);
v___x_1632_ = lean_unbox(v___x_1631_);
lean_dec(v___x_1631_);
if (v___x_1632_ == 0)
{
goto v___jp_1605_;
}
else
{
lean_object* v___x_1633_; 
lean_dec_ref(v___x_1602_);
lean_dec_ref(v___x_1601_);
v___x_1633_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_child_1604_, v_derivedValMap_1599_, v_liveVars_1603_, v_shouldAdd_1600_);
return v___x_1633_;
}
}
}
v___jp_1605_:
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
lean_inc_ref(v_shouldAdd_1600_);
lean_inc(v_child_1604_);
v___x_1606_ = lean_apply_1(v_shouldAdd_1600_, v_child_1604_);
v___x_1607_ = lean_unbox(v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_dec_ref(v___x_1602_);
lean_dec_ref(v___x_1601_);
v___x_1608_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_child_1604_, v_derivedValMap_1599_, v_liveVars_1603_, v_shouldAdd_1600_);
return v___x_1608_;
}
else
{
lean_object* v_vars_1609_; lean_object* v_borrows_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1620_; 
v_vars_1609_ = lean_ctor_get(v_liveVars_1603_, 0);
v_borrows_1610_ = lean_ctor_get(v_liveVars_1603_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_liveVars_1603_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1612_ = v_liveVars_1603_;
v_isShared_1613_ = v_isSharedCheck_1620_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_borrows_1610_);
lean_inc(v_vars_1609_);
lean_dec(v_liveVars_1603_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1620_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1614_ = lean_box(0);
lean_inc(v_child_1604_);
v___x_1615_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1601_, v___x_1602_, v_borrows_1610_, v_child_1604_, v___x_1614_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 1, v___x_1615_);
v___x_1617_ = v___x_1612_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_vars_1609_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; 
v___x_1618_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_child_1604_, v_derivedValMap_1599_, v___x_1617_, v_shouldAdd_1600_);
return v___x_1618_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1___boxed(lean_object* v___f_1634_, lean_object* v___x_1635_, lean_object* v_derivedValMap_1636_, lean_object* v_shouldAdd_1637_, lean_object* v___x_1638_, lean_object* v___x_1639_, lean_object* v_liveVars_1640_, lean_object* v_child_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1(v___f_1634_, v___x_1635_, v_derivedValMap_1636_, v_shouldAdd_1637_, v___x_1638_, v___x_1639_, v_liveVars_1640_, v_child_1641_);
lean_dec_ref(v___x_1635_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(lean_object* v_fvarId_1643_, lean_object* v_derivedValMap_1644_, lean_object* v_liveVars_1645_, lean_object* v_shouldAdd_1646_){
_start:
{
lean_object* v___f_1647_; lean_object* v___x_1648_; 
v___f_1647_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_derivedValMap_1644_);
v___x_1648_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1647_, v_derivedValMap_1644_, v_fvarId_1643_);
if (lean_obj_tag(v___x_1648_) == 1)
{
lean_object* v_val_1649_; lean_object* v_children_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___f_1654_; lean_object* v___x_1655_; 
v_val_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_val_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v_children_1650_ = lean_ctor_get(v_val_1649_, 1);
lean_inc(v_children_1650_);
lean_dec(v_val_1649_);
v___x_1651_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default));
v___x_1652_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_1653_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___f_1654_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1___boxed), 8, 6);
lean_closure_set(v___f_1654_, 0, v___f_1647_);
lean_closure_set(v___f_1654_, 1, v___x_1651_);
lean_closure_set(v___f_1654_, 2, v_derivedValMap_1644_);
lean_closure_set(v___f_1654_, 3, v_shouldAdd_1646_);
lean_closure_set(v___f_1654_, 4, v___x_1652_);
lean_closure_set(v___f_1654_, 5, v___x_1653_);
v___x_1655_ = l_List_foldl___redArg(v___f_1654_, v_liveVars_1645_, v_children_1650_);
return v___x_1655_;
}
else
{
lean_dec(v___x_1648_);
lean_dec_ref(v_shouldAdd_1646_);
lean_dec(v_derivedValMap_1644_);
return v_liveVars_1645_;
}
}
}
uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0(lean_object* v_val_1656_, lean_object* v___x_1657_, lean_object* v___x_1658_, lean_object* v_shouldBorrow_1659_, uint8_t v___x_1660_, lean_object* v_y_1661_){
_start:
{
lean_object* v_vars_1662_; uint8_t v___x_1663_; 
v_vars_1662_ = lean_ctor_get(v_val_1656_, 0);
lean_inc(v_y_1661_);
v___x_1663_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1657_, v___x_1658_, v_vars_1662_, v_y_1661_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = lean_apply_1(v_shouldBorrow_1659_, v_y_1661_);
v___x_1665_ = lean_unbox(v___x_1664_);
return v___x_1665_;
}
else
{
lean_dec(v_y_1661_);
lean_dec_ref(v_shouldBorrow_1659_);
return v___x_1660_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1656_ = stack[0].m_obj;
lean_object* v___x_1657_ = stack[1].m_obj;
lean_object* v___x_1658_ = stack[2].m_obj;
lean_object* v_shouldBorrow_1659_ = stack[3].m_obj;
uint8_t v___x_1660_ = stack[4].m_num;
lean_object* v_y_1661_ = stack[5].m_obj;
uint8_t v_res_1666_;
v_res_1666_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0(v_val_1656_, v___x_1657_, v___x_1658_, v_shouldBorrow_1659_, v___x_1660_, v_y_1661_);
stack->m_num = v_res_1666_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0___boxed(lean_object* v_val_1667_, lean_object* v___x_1668_, lean_object* v___x_1669_, lean_object* v_shouldBorrow_1670_, lean_object* v___x_1671_, lean_object* v_y_1672_){
_start:
{
uint8_t v___x_1972__boxed_1673_; uint8_t v_res_1674_; lean_object* v_r_1675_; 
v___x_1972__boxed_1673_ = lean_unbox(v___x_1671_);
v_res_1674_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0(v_val_1667_, v___x_1668_, v___x_1669_, v_shouldBorrow_1670_, v___x_1972__boxed_1673_, v_y_1672_);
lean_dec_ref(v_val_1667_);
v_r_1675_ = lean_box(v_res_1674_);
return v_r_1675_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(lean_object* v_fvarId_1676_, lean_object* v_shouldBorrow_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v_vars_1684_; uint8_t v___x_1685_; 
v___x_1681_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_1682_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_1683_ = lean_st_ref_get(v_a_1679_);
v_vars_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc_ref(v_vars_1684_);
lean_dec(v___x_1683_);
lean_inc(v_fvarId_1676_);
v___x_1685_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1681_, v___x_1682_, v_vars_1684_, v_fvarId_1676_);
lean_dec_ref(v_vars_1684_);
if (v___x_1685_ == 0)
{
lean_object* v_derivedValMap_1686_; lean_object* v___x_1687_; lean_object* v_vars_1688_; lean_object* v_borrows_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1705_; 
v_derivedValMap_1686_ = lean_ctor_get(v_a_1678_, 2);
v___x_1687_ = lean_st_ref_take(v_a_1679_);
v_vars_1688_ = lean_ctor_get(v___x_1687_, 0);
v_borrows_1689_ = lean_ctor_get(v___x_1687_, 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1691_ = v___x_1687_;
v_isShared_1692_ = v_isSharedCheck_1705_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_borrows_1689_);
lean_inc(v_vars_1688_);
lean_dec(v___x_1687_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1705_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1693_ = lean_box(0);
lean_inc(v_fvarId_1676_);
v___x_1694_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1681_, v___x_1682_, v_vars_1688_, v_fvarId_1676_, v___x_1693_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1694_);
v___x_1696_ = v___x_1691_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_borrows_1689_);
v___x_1696_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___f_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1697_ = lean_st_ref_put(v_a_1679_, v___x_1696_);
v___x_1698_ = lean_st_ref_take(v_a_1679_);
v___x_1699_ = lean_box(v___x_1685_);
lean_inc(v___x_1698_);
v___f_1700_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1700_, 0, v___x_1698_);
lean_closure_set(v___f_1700_, 1, v___x_1681_);
lean_closure_set(v___f_1700_, 2, v___x_1682_);
lean_closure_set(v___f_1700_, 3, v_shouldBorrow_1677_);
lean_closure_set(v___f_1700_, 4, v___x_1699_);
lean_inc(v_derivedValMap_1686_);
v___x_1701_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_fvarId_1676_, v_derivedValMap_1686_, v___x_1698_, v___f_1700_);
v___x_1702_ = lean_st_ref_put(v_a_1679_, v___x_1701_);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1693_);
return v___x_1703_;
}
}
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec_ref(v_shouldBorrow_1677_);
lean_dec(v_fvarId_1676_);
v___x_1706_ = lean_box(0);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
return v___x_1707_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1676_ = stack[0].m_obj;
lean_object* v_shouldBorrow_1677_ = stack[1].m_obj;
lean_object* v_a_1678_ = stack[2].m_obj;
lean_object* v_a_1679_ = stack[3].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_1676_, v_shouldBorrow_1677_, v_a_1678_, v_a_1679_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___boxed(lean_object* v_fvarId_1709_, lean_object* v_shouldBorrow_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_1709_, v_shouldBorrow_1710_, v_a_1711_, v_a_1712_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
return v_res_1714_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(lean_object* v_fvarId_1715_, lean_object* v_shouldBorrow_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_1715_, v_shouldBorrow_1716_, v_a_1717_, v_a_1718_);
return v___x_1724_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1715_ = stack[0].m_obj;
lean_object* v_shouldBorrow_1716_ = stack[1].m_obj;
lean_object* v_a_1717_ = stack[2].m_obj;
lean_object* v_a_1718_ = stack[3].m_obj;
lean_object* v_a_1719_ = stack[4].m_obj;
lean_object* v_a_1720_ = stack[5].m_obj;
lean_object* v_a_1721_ = stack[6].m_obj;
lean_object* v_a_1722_ = stack[7].m_obj;
lean_object* v_res_1725_;
v_res_1725_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(v_fvarId_1715_, v_shouldBorrow_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_);
stack->m_obj
 = v_res_1725_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___boxed(lean_object* v_fvarId_1726_, lean_object* v_shouldBorrow_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(v_fvarId_1726_, v_shouldBorrow_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
return v_res_1735_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(lean_object* v_liveVars_1736_, lean_object* v_as_1737_, size_t v_i_1738_, size_t v_stop_1739_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_usize_dec_eq(v_i_1738_, v_stop_1739_);
if (v___x_1740_ == 0)
{
lean_object* v_vars_1741_; lean_object* v_borrows_1742_; uint8_t v___x_1743_; uint8_t v___y_1745_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_vars_1741_ = lean_ctor_get(v_liveVars_1736_, 0);
v_borrows_1742_ = lean_ctor_get(v_liveVars_1736_, 1);
v___x_1743_ = 1;
v___x_1749_ = lean_array_uget_borrowed(v_as_1737_, v_i_1738_);
v___x_1750_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1741_, v___x_1749_);
if (v___x_1750_ == 0)
{
uint8_t v___x_1751_; 
v___x_1751_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_1742_, v___x_1749_);
v___y_1745_ = v___x_1751_;
goto v___jp_1744_;
}
else
{
v___y_1745_ = v___x_1750_;
goto v___jp_1744_;
}
v___jp_1744_:
{
if (v___y_1745_ == 0)
{
return v___x_1743_;
}
else
{
size_t v___x_1746_; size_t v___x_1747_; 
v___x_1746_ = ((size_t)1ULL);
v___x_1747_ = lean_usize_add(v_i_1738_, v___x_1746_);
v_i_1738_ = v___x_1747_;
goto _start;
}
}
}
else
{
uint8_t v___x_1752_; 
v___x_1752_ = 0;
return v___x_1752_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_liveVars_1736_ = stack[0].m_obj;
lean_object* v_as_1737_ = stack[1].m_obj;
size_t v_i_1738_ = stack[2].m_num;
size_t v_stop_1739_ = stack[3].m_num;
uint8_t v_res_1753_;
v_res_1753_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_liveVars_1736_, v_as_1737_, v_i_1738_, v_stop_1739_);
stack->m_num = v_res_1753_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3___boxed(lean_object* v_liveVars_1754_, lean_object* v_as_1755_, lean_object* v_i_1756_, lean_object* v_stop_1757_){
_start:
{
size_t v_i_boxed_1758_; size_t v_stop_boxed_1759_; uint8_t v_res_1760_; lean_object* v_r_1761_; 
v_i_boxed_1758_ = lean_unbox_usize(v_i_1756_);
lean_dec(v_i_1756_);
v_stop_boxed_1759_ = lean_unbox_usize(v_stop_1757_);
lean_dec(v_stop_1757_);
v_res_1760_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_liveVars_1754_, v_as_1755_, v_i_boxed_1758_, v_stop_boxed_1759_);
lean_dec_ref(v_as_1755_);
lean_dec_ref(v_liveVars_1754_);
v_r_1761_ = lean_box(v_res_1760_);
return v_r_1761_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(lean_object* v_y_1762_, lean_object* v_as_1763_, size_t v_i_1764_, size_t v_stop_1765_){
_start:
{
uint8_t v___x_1770_; 
v___x_1770_ = lean_usize_dec_eq(v_i_1764_, v_stop_1765_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_array_uget_borrowed(v_as_1763_, v_i_1764_);
if (lean_obj_tag(v___x_1771_) == 0)
{
goto v___jp_1766_;
}
else
{
lean_object* v_fvarId_1772_; uint8_t v___x_1773_; 
v_fvarId_1772_ = lean_ctor_get(v___x_1771_, 0);
v___x_1773_ = l_Lean_instBEqFVarId_beq(v_y_1762_, v_fvarId_1772_);
if (v___x_1773_ == 0)
{
goto v___jp_1766_;
}
else
{
return v___x_1773_;
}
}
}
else
{
uint8_t v___x_1774_; 
v___x_1774_ = 0;
return v___x_1774_;
}
v___jp_1766_:
{
size_t v___x_1767_; size_t v___x_1768_; 
v___x_1767_ = ((size_t)1ULL);
v___x_1768_ = lean_usize_add(v_i_1764_, v___x_1767_);
v_i_1764_ = v___x_1768_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_1762_ = stack[0].m_obj;
lean_object* v_as_1763_ = stack[1].m_obj;
size_t v_i_1764_ = stack[2].m_num;
size_t v_stop_1765_ = stack[3].m_num;
uint8_t v_res_1775_;
v_res_1775_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_y_1762_, v_as_1763_, v_i_1764_, v_stop_1765_);
stack->m_num = v_res_1775_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0___boxed(lean_object* v_y_1776_, lean_object* v_as_1777_, lean_object* v_i_1778_, lean_object* v_stop_1779_){
_start:
{
size_t v_i_boxed_1780_; size_t v_stop_boxed_1781_; uint8_t v_res_1782_; lean_object* v_r_1783_; 
v_i_boxed_1780_ = lean_unbox_usize(v_i_1778_);
lean_dec(v_i_1778_);
v_stop_boxed_1781_ = lean_unbox_usize(v_stop_1779_);
lean_dec(v_stop_1779_);
v_res_1782_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_y_1776_, v_as_1777_, v_i_boxed_1780_, v_stop_boxed_1781_);
lean_dec_ref(v_as_1777_);
lean_dec(v_y_1776_);
v_r_1783_ = lean_box(v_res_1782_);
return v_r_1783_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2_spec__4(lean_object* v_msg_1784_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default));
v___x_1786_ = lean_panic_fn_borrowed(v___x_1785_, v_msg_1784_);
return v___x_1786_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1790_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__2));
v___x_1791_ = lean_unsigned_to_nat(13u);
v___x_1792_ = lean_unsigned_to_nat(227u);
v___x_1793_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__1));
v___x_1794_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__0));
v___x_1795_ = l_mkPanicMessageWithDecl(v___x_1794_, v___x_1793_, v___x_1792_, v___x_1791_, v___x_1790_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(lean_object* v_t_1796_, lean_object* v_k_1797_){
_start:
{
if (lean_obj_tag(v_t_1796_) == 0)
{
lean_object* v_k_1798_; lean_object* v_v_1799_; lean_object* v_l_1800_; lean_object* v_r_1801_; uint8_t v___x_1802_; 
v_k_1798_ = lean_ctor_get(v_t_1796_, 1);
v_v_1799_ = lean_ctor_get(v_t_1796_, 2);
v_l_1800_ = lean_ctor_get(v_t_1796_, 3);
v_r_1801_ = lean_ctor_get(v_t_1796_, 4);
v___x_1802_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1797_, v_k_1798_);
switch(v___x_1802_)
{
case 0:
{
v_t_1796_ = v_l_1800_;
goto _start;
}
case 1:
{
lean_inc(v_v_1799_);
return v_v_1799_;
}
default: 
{
v_t_1796_ = v_r_1801_;
goto _start;
}
}
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3);
v___x_1806_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2_spec__4(v___x_1805_);
return v___x_1806_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___boxed(lean_object* v_t_1807_, lean_object* v_k_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_t_1807_, v_k_1808_);
lean_dec(v_k_1808_);
lean_dec(v_t_1807_);
return v_res_1809_;
}
}
lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(lean_object* v___x_1810_, lean_object* v_args_1811_, uint8_t v___x_1812_, lean_object* v_derivedValMap_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
if (lean_obj_tag(v_x_1815_) == 0)
{
return v_x_1814_;
}
else
{
lean_object* v_head_1816_; lean_object* v_tail_1817_; uint8_t v___y_1833_; lean_object* v_cinfo_1845_; lean_object* v_parents_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v_head_1816_ = lean_ctor_get(v_x_1815_, 0);
lean_inc(v_head_1816_);
v_tail_1817_ = lean_ctor_get(v_x_1815_, 1);
lean_inc(v_tail_1817_);
lean_dec_ref_known(v_x_1815_, 2);
v_cinfo_1845_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_1813_, v_head_1816_);
v_parents_1846_ = lean_ctor_get(v_cinfo_1845_, 0);
lean_inc_ref(v_parents_1846_);
lean_dec_ref(v_cinfo_1845_);
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = lean_array_get_size(v_parents_1846_);
v___x_1849_ = lean_nat_dec_lt(v___x_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_dec_ref(v_parents_1846_);
goto v___jp_1836_;
}
else
{
if (v___x_1849_ == 0)
{
lean_dec_ref(v_parents_1846_);
goto v___jp_1836_;
}
else
{
size_t v___x_1850_; size_t v___x_1851_; uint8_t v___x_1852_; 
v___x_1850_ = ((size_t)0ULL);
v___x_1851_ = lean_usize_of_nat(v___x_1848_);
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_1814_, v_parents_1846_, v___x_1850_, v___x_1851_);
lean_dec_ref(v_parents_1846_);
if (v___x_1852_ == 0)
{
goto v___jp_1836_;
}
else
{
lean_object* v___x_1853_; 
v___x_1853_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1810_, v_args_1811_, v___x_1812_, v_head_1816_, v_derivedValMap_1813_, v_x_1814_);
lean_dec(v_head_1816_);
v_x_1814_ = v___x_1853_;
v_x_1815_ = v_tail_1817_;
goto _start;
}
}
}
v___jp_1818_:
{
lean_object* v_vars_1819_; lean_object* v_borrows_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1831_; 
v_vars_1819_ = lean_ctor_get(v_x_1814_, 0);
v_borrows_1820_ = lean_ctor_get(v_x_1814_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_x_1814_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1822_ = v_x_1814_;
v_isShared_1823_ = v_isSharedCheck_1831_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_borrows_1820_);
lean_inc(v_vars_1819_);
lean_dec(v_x_1814_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1831_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1824_ = lean_box(0);
lean_inc(v_head_1816_);
v___x_1825_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_1820_, v_head_1816_, v___x_1824_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v___x_1825_);
v___x_1827_ = v___x_1822_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_vars_1819_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; 
v___x_1828_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1810_, v_args_1811_, v___x_1812_, v_head_1816_, v_derivedValMap_1813_, v___x_1827_);
lean_dec(v_head_1816_);
v_x_1814_ = v___x_1828_;
v_x_1815_ = v_tail_1817_;
goto _start;
}
}
}
v___jp_1832_:
{
if (v___y_1833_ == 0)
{
lean_object* v___x_1834_; 
v___x_1834_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1810_, v_args_1811_, v___x_1812_, v_head_1816_, v_derivedValMap_1813_, v_x_1814_);
lean_dec(v_head_1816_);
v_x_1814_ = v___x_1834_;
v_x_1815_ = v_tail_1817_;
goto _start;
}
else
{
goto v___jp_1818_;
}
}
v___jp_1836_:
{
lean_object* v_vars_1837_; uint8_t v___x_1838_; 
v_vars_1837_ = lean_ctor_get(v___x_1810_, 0);
v___x_1838_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1837_, v_head_1816_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_array_get_size(v_args_1811_);
v___x_1841_ = lean_nat_dec_lt(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
goto v___jp_1818_;
}
else
{
if (v___x_1841_ == 0)
{
goto v___jp_1818_;
}
else
{
size_t v___x_1842_; size_t v___x_1843_; uint8_t v___x_1844_; 
v___x_1842_ = ((size_t)0ULL);
v___x_1843_ = lean_usize_of_nat(v___x_1840_);
v___x_1844_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_head_1816_, v_args_1811_, v___x_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
goto v___jp_1818_;
}
else
{
v___y_1833_ = v___x_1838_;
goto v___jp_1832_;
}
}
}
}
else
{
v___y_1833_ = v___x_1812_;
goto v___jp_1832_;
}
}
}
}
}
LEAN_EXPORT void l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1810_ = stack[0].m_obj;
lean_object* v_args_1811_ = stack[1].m_obj;
uint8_t v___x_1812_ = stack[2].m_num;
lean_object* v_derivedValMap_1813_ = stack[3].m_obj;
lean_object* v_x_1814_ = stack[4].m_obj;
lean_object* v_x_1815_ = stack[5].m_obj;
lean_object* v_res_1855_;
v_res_1855_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1810_, v_args_1811_, v___x_1812_, v_derivedValMap_1813_, v_x_1814_, v_x_1815_);
stack->m_obj
 = v_res_1855_;
}
lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(lean_object* v___x_1856_, lean_object* v_args_1857_, uint8_t v___x_1858_, lean_object* v_derivedValMap_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_){
_start:
{
if (lean_obj_tag(v_x_1861_) == 0)
{
return v_x_1860_;
}
else
{
lean_object* v_head_1862_; lean_object* v_tail_1863_; uint8_t v___y_1879_; lean_object* v_cinfo_1891_; lean_object* v_parents_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v_head_1862_ = lean_ctor_get(v_x_1861_, 0);
lean_inc(v_head_1862_);
v_tail_1863_ = lean_ctor_get(v_x_1861_, 1);
lean_inc(v_tail_1863_);
lean_dec_ref_known(v_x_1861_, 2);
v_cinfo_1891_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_1859_, v_head_1862_);
v_parents_1892_ = lean_ctor_get(v_cinfo_1891_, 0);
lean_inc_ref(v_parents_1892_);
lean_dec_ref(v_cinfo_1891_);
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = lean_array_get_size(v_parents_1892_);
v___x_1895_ = lean_nat_dec_lt(v___x_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_dec_ref(v_parents_1892_);
goto v___jp_1882_;
}
else
{
if (v___x_1895_ == 0)
{
lean_dec_ref(v_parents_1892_);
goto v___jp_1882_;
}
else
{
size_t v___x_1896_; size_t v___x_1897_; uint8_t v___x_1898_; 
v___x_1896_ = ((size_t)0ULL);
v___x_1897_ = lean_usize_of_nat(v___x_1894_);
v___x_1898_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_1860_, v_parents_1892_, v___x_1896_, v___x_1897_);
lean_dec_ref(v_parents_1892_);
if (v___x_1898_ == 0)
{
goto v___jp_1882_;
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1856_, v_args_1857_, v___x_1858_, v_head_1862_, v_derivedValMap_1859_, v_x_1860_);
lean_dec(v_head_1862_);
v___x_1900_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1856_, v_args_1857_, v___x_1858_, v_derivedValMap_1859_, v___x_1899_, v_tail_1863_);
return v___x_1900_;
}
}
}
v___jp_1864_:
{
lean_object* v_vars_1865_; lean_object* v_borrows_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1877_; 
v_vars_1865_ = lean_ctor_get(v_x_1860_, 0);
v_borrows_1866_ = lean_ctor_get(v_x_1860_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_x_1860_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1868_ = v_x_1860_;
v_isShared_1869_ = v_isSharedCheck_1877_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_borrows_1866_);
lean_inc(v_vars_1865_);
lean_dec(v_x_1860_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1877_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1870_ = lean_box(0);
lean_inc(v_head_1862_);
v___x_1871_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_1866_, v_head_1862_, v___x_1870_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___x_1871_);
v___x_1873_ = v___x_1868_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_vars_1865_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1856_, v_args_1857_, v___x_1858_, v_head_1862_, v_derivedValMap_1859_, v___x_1873_);
lean_dec(v_head_1862_);
v___x_1875_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1856_, v_args_1857_, v___x_1858_, v_derivedValMap_1859_, v___x_1874_, v_tail_1863_);
return v___x_1875_;
}
}
}
v___jp_1878_:
{
if (v___y_1879_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1856_, v_args_1857_, v___x_1858_, v_head_1862_, v_derivedValMap_1859_, v_x_1860_);
lean_dec(v_head_1862_);
v___x_1881_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1856_, v_args_1857_, v___x_1858_, v_derivedValMap_1859_, v___x_1880_, v_tail_1863_);
return v___x_1881_;
}
else
{
goto v___jp_1864_;
}
}
v___jp_1882_:
{
lean_object* v_vars_1883_; uint8_t v___x_1884_; 
v_vars_1883_ = lean_ctor_get(v___x_1856_, 0);
v___x_1884_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1883_, v_head_1862_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_array_get_size(v_args_1857_);
v___x_1887_ = lean_nat_dec_lt(v___x_1885_, v___x_1886_);
if (v___x_1887_ == 0)
{
goto v___jp_1864_;
}
else
{
if (v___x_1887_ == 0)
{
goto v___jp_1864_;
}
else
{
size_t v___x_1888_; size_t v___x_1889_; uint8_t v___x_1890_; 
v___x_1888_ = ((size_t)0ULL);
v___x_1889_ = lean_usize_of_nat(v___x_1886_);
v___x_1890_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_head_1862_, v_args_1857_, v___x_1888_, v___x_1889_);
if (v___x_1890_ == 0)
{
goto v___jp_1864_;
}
else
{
v___y_1879_ = v___x_1884_;
goto v___jp_1878_;
}
}
}
}
else
{
v___y_1879_ = v___x_1858_;
goto v___jp_1878_;
}
}
}
}
}
LEAN_EXPORT void l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1856_ = stack[0].m_obj;
lean_object* v_args_1857_ = stack[1].m_obj;
uint8_t v___x_1858_ = stack[2].m_num;
lean_object* v_derivedValMap_1859_ = stack[3].m_obj;
lean_object* v_x_1860_ = stack[4].m_obj;
lean_object* v_x_1861_ = stack[5].m_obj;
lean_object* v_res_1901_;
v_res_1901_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(v___x_1856_, v_args_1857_, v___x_1858_, v_derivedValMap_1859_, v_x_1860_, v_x_1861_);
stack->m_obj
 = v_res_1901_;
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(lean_object* v___x_1902_, lean_object* v_args_1903_, uint8_t v___x_1904_, lean_object* v_fvarId_1905_, lean_object* v_derivedValMap_1906_, lean_object* v_liveVars_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_derivedValMap_1906_, v_fvarId_1905_);
if (lean_obj_tag(v___x_1908_) == 1)
{
lean_object* v_val_1909_; lean_object* v_children_1910_; lean_object* v___x_1911_; 
v_val_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_val_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v_children_1910_ = lean_ctor_get(v_val_1909_, 1);
lean_inc(v_children_1910_);
lean_dec(v_val_1909_);
v___x_1911_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(v___x_1902_, v_args_1903_, v___x_1904_, v_derivedValMap_1906_, v_liveVars_1907_, v_children_1910_);
return v___x_1911_;
}
else
{
lean_dec(v___x_1908_);
return v_liveVars_1907_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1902_ = stack[0].m_obj;
lean_object* v_args_1903_ = stack[1].m_obj;
uint8_t v___x_1904_ = stack[2].m_num;
lean_object* v_fvarId_1905_ = stack[3].m_obj;
lean_object* v_derivedValMap_1906_ = stack[4].m_obj;
lean_object* v_liveVars_1907_ = stack[5].m_obj;
lean_object* v_res_1912_;
v_res_1912_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1902_, v_args_1903_, v___x_1904_, v_fvarId_1905_, v_derivedValMap_1906_, v_liveVars_1907_);
stack->m_obj
 = v_res_1912_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1___boxed(lean_object* v___x_1913_, lean_object* v_args_1914_, lean_object* v___x_1915_, lean_object* v_fvarId_1916_, lean_object* v_derivedValMap_1917_, lean_object* v_liveVars_1918_){
_start:
{
uint8_t v___x_2310__boxed_1919_; lean_object* v_res_1920_; 
v___x_2310__boxed_1919_ = lean_unbox(v___x_1915_);
v_res_1920_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1913_, v_args_1914_, v___x_2310__boxed_1919_, v_fvarId_1916_, v_derivedValMap_1917_, v_liveVars_1918_);
lean_dec(v_derivedValMap_1917_);
lean_dec(v_fvarId_1916_);
lean_dec_ref(v_args_1914_);
lean_dec_ref(v___x_1913_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v___x_1921_, lean_object* v_args_1922_, lean_object* v___x_1923_, lean_object* v_derivedValMap_1924_, lean_object* v_x_1925_, lean_object* v_x_1926_){
_start:
{
uint8_t v___x_2315__boxed_1927_; lean_object* v_res_1928_; 
v___x_2315__boxed_1927_ = lean_unbox(v___x_1923_);
v_res_1928_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1921_, v_args_1922_, v___x_2315__boxed_1927_, v_derivedValMap_1924_, v_x_1925_, v_x_1926_);
lean_dec(v_derivedValMap_1924_);
lean_dec_ref(v_args_1922_);
lean_dec_ref(v___x_1921_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4___boxed(lean_object* v___x_1929_, lean_object* v_args_1930_, lean_object* v___x_1931_, lean_object* v_derivedValMap_1932_, lean_object* v_x_1933_, lean_object* v_x_1934_){
_start:
{
uint8_t v___x_2347__boxed_1935_; lean_object* v_res_1936_; 
v___x_2347__boxed_1935_ = lean_unbox(v___x_1931_);
v_res_1936_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(v___x_1929_, v_args_1930_, v___x_2347__boxed_1935_, v_derivedValMap_1932_, v_x_1933_, v_x_1934_);
lean_dec(v_derivedValMap_1932_);
lean_dec_ref(v_args_1930_);
lean_dec_ref(v___x_1929_);
return v_res_1936_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(lean_object* v_args_1937_, lean_object* v_fvarId_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v___x_1942_; lean_object* v_vars_1943_; uint8_t v___x_1944_; 
v___x_1942_ = lean_st_ref_get(v_a_1940_);
v_vars_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc_ref(v_vars_1943_);
lean_dec(v___x_1942_);
v___x_1944_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1943_, v_fvarId_1938_);
lean_dec_ref(v_vars_1943_);
if (v___x_1944_ == 0)
{
lean_object* v_derivedValMap_1945_; lean_object* v___x_1946_; lean_object* v_vars_1947_; lean_object* v_borrows_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1962_; 
v_derivedValMap_1945_ = lean_ctor_get(v_a_1939_, 2);
v___x_1946_ = lean_st_ref_take(v_a_1940_);
v_vars_1947_ = lean_ctor_get(v___x_1946_, 0);
v_borrows_1948_ = lean_ctor_get(v___x_1946_, 1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1950_ = v___x_1946_;
v_isShared_1951_ = v_isSharedCheck_1962_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_borrows_1948_);
lean_inc(v_vars_1947_);
lean_dec(v___x_1946_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1962_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1952_ = lean_box(0);
lean_inc(v_fvarId_1938_);
v___x_1953_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_vars_1947_, v_fvarId_1938_, v___x_1952_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1953_);
v___x_1955_ = v___x_1950_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_borrows_1948_);
v___x_1955_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1956_ = lean_st_ref_put(v_a_1940_, v___x_1955_);
v___x_1957_ = lean_st_ref_take(v_a_1940_);
lean_inc(v___x_1957_);
v___x_1958_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1957_, v_args_1937_, v___x_1944_, v_fvarId_1938_, v_derivedValMap_1945_, v___x_1957_);
lean_dec(v_fvarId_1938_);
lean_dec(v___x_1957_);
v___x_1959_ = lean_st_ref_put(v_a_1940_, v___x_1958_);
v___x_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1952_);
return v___x_1960_;
}
}
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec(v_fvarId_1938_);
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1937_ = stack[0].m_obj;
lean_object* v_fvarId_1938_ = stack[1].m_obj;
lean_object* v_a_1939_ = stack[2].m_obj;
lean_object* v_a_1940_ = stack[3].m_obj;
lean_object* v_res_1965_;
v_res_1965_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_1937_, v_fvarId_1938_, v_a_1939_, v_a_1940_);
stack->m_obj
 = v_res_1965_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg___boxed(lean_object* v_args_1966_, lean_object* v_fvarId_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_1966_, v_fvarId_1967_, v_a_1968_, v_a_1969_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_args_1966_);
return v_res_1971_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(lean_object* v_args_1972_, lean_object* v_as_1973_, size_t v_i_1974_, size_t v_stop_1975_, lean_object* v_b_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_a_1985_; uint8_t v___x_1989_; 
v___x_1989_ = lean_usize_dec_eq(v_i_1974_, v_stop_1975_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_array_uget_borrowed(v_as_1973_, v_i_1974_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v___x_1991_; 
v___x_1991_ = lean_box(0);
v_a_1985_ = v___x_1991_;
goto v___jp_1984_;
}
else
{
lean_object* v_fvarId_1992_; lean_object* v___x_1993_; 
v_fvarId_1992_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_fvarId_1992_);
v___x_1993_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_1972_, v_fvarId_1992_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v_a_1985_ = v_a_1994_;
goto v___jp_1984_;
}
else
{
return v___x_1993_;
}
}
}
else
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1995_, 0, v_b_1976_);
return v___x_1995_;
}
v___jp_1984_:
{
size_t v___x_1986_; size_t v___x_1987_; 
v___x_1986_ = ((size_t)1ULL);
v___x_1987_ = lean_usize_add(v_i_1974_, v___x_1986_);
v_i_1974_ = v___x_1987_;
v_b_1976_ = v_a_1985_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1972_ = stack[0].m_obj;
lean_object* v_as_1973_ = stack[1].m_obj;
size_t v_i_1974_ = stack[2].m_num;
size_t v_stop_1975_ = stack[3].m_num;
lean_object* v_b_1976_ = stack[4].m_obj;
lean_object* v___y_1977_ = stack[5].m_obj;
lean_object* v___y_1978_ = stack[6].m_obj;
lean_object* v___y_1979_ = stack[7].m_obj;
lean_object* v___y_1980_ = stack[8].m_obj;
lean_object* v___y_1981_ = stack[9].m_obj;
lean_object* v___y_1982_ = stack[10].m_obj;
lean_object* v_res_1996_;
v_res_1996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(v_args_1972_, v_as_1973_, v_i_1974_, v_stop_1975_, v_b_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
stack->m_obj
 = v_res_1996_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2___boxed(lean_object* v_args_1997_, lean_object* v_as_1998_, lean_object* v_i_1999_, lean_object* v_stop_2000_, lean_object* v_b_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
size_t v_i_boxed_2009_; size_t v_stop_boxed_2010_; lean_object* v_res_2011_; 
v_i_boxed_2009_ = lean_unbox_usize(v_i_1999_);
lean_dec(v_i_1999_);
v_stop_boxed_2010_ = lean_unbox_usize(v_stop_2000_);
lean_dec(v_stop_2000_);
v_res_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(v_args_1997_, v_as_1998_, v_i_boxed_2009_, v_stop_boxed_2010_, v_b_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec_ref(v_as_1998_);
lean_dec_ref(v_args_1997_);
return v_res_2011_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(lean_object* v_args_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2020_ = lean_unsigned_to_nat(0u);
v___x_2021_ = lean_array_get_size(v_args_2012_);
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_nat_dec_lt(v___x_2020_, v___x_2021_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2022_);
return v___x_2024_;
}
else
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_nat_dec_le(v___x_2021_, v___x_2021_);
if (v___x_2025_ == 0)
{
if (v___x_2023_ == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2022_);
return v___x_2026_;
}
else
{
size_t v___x_2027_; size_t v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = ((size_t)0ULL);
v___x_2028_ = lean_usize_of_nat(v___x_2021_);
v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(v_args_2012_, v_args_2012_, v___x_2027_, v___x_2028_, v___x_2022_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
return v___x_2029_;
}
}
else
{
size_t v___x_2030_; size_t v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = ((size_t)0ULL);
v___x_2031_ = lean_usize_of_nat(v___x_2021_);
v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(v_args_2012_, v_args_2012_, v___x_2030_, v___x_2031_, v___x_2022_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
return v___x_2032_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_2012_ = stack[0].m_obj;
lean_object* v_a_2013_ = stack[1].m_obj;
lean_object* v_a_2014_ = stack[2].m_obj;
lean_object* v_a_2015_ = stack[3].m_obj;
lean_object* v_a_2016_ = stack[4].m_obj;
lean_object* v_a_2017_ = stack[5].m_obj;
lean_object* v_a_2018_ = stack[6].m_obj;
lean_object* v_res_2033_;
v_res_2033_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
stack->m_obj
 = v_res_2033_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs___boxed(lean_object* v_args_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
lean_dec(v_a_2036_);
lean_dec_ref(v_a_2035_);
lean_dec_ref(v_args_2034_);
return v_res_2042_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(lean_object* v_args_2043_, lean_object* v_fvarId_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_2043_, v_fvarId_2044_, v_a_2045_, v_a_2046_);
return v___x_2052_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_2043_ = stack[0].m_obj;
lean_object* v_fvarId_2044_ = stack[1].m_obj;
lean_object* v_a_2045_ = stack[2].m_obj;
lean_object* v_a_2046_ = stack[3].m_obj;
lean_object* v_a_2047_ = stack[4].m_obj;
lean_object* v_a_2048_ = stack[5].m_obj;
lean_object* v_a_2049_ = stack[6].m_obj;
lean_object* v_a_2050_ = stack[7].m_obj;
lean_object* v_res_2053_;
v_res_2053_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(v_args_2043_, v_fvarId_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
stack->m_obj
 = v_res_2053_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___boxed(lean_object* v_args_2054_, lean_object* v_fvarId_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(v_args_2054_, v_fvarId_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
lean_dec_ref(v_args_2054_);
return v_res_2063_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_instMonadEIO___redArg();
return v___x_2064_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(lean_object* v_msg_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_toApplicative_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2142_; 
v___x_2077_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0);
v___x_2078_ = l_StateRefT_x27_instMonad___redArg(v___x_2077_);
v_toApplicative_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; 
v_unused_2143_ = lean_ctor_get(v___x_2078_, 1);
lean_dec(v_unused_2143_);
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2142_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_toApplicative_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2142_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_toFunctor_2083_; lean_object* v_toSeq_2084_; lean_object* v_toSeqLeft_2085_; lean_object* v_toSeqRight_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2140_; 
v_toFunctor_2083_ = lean_ctor_get(v_toApplicative_2079_, 0);
v_toSeq_2084_ = lean_ctor_get(v_toApplicative_2079_, 2);
v_toSeqLeft_2085_ = lean_ctor_get(v_toApplicative_2079_, 3);
v_toSeqRight_2086_ = lean_ctor_get(v_toApplicative_2079_, 4);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_toApplicative_2079_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; 
v_unused_2141_ = lean_ctor_get(v_toApplicative_2079_, 1);
lean_dec(v_unused_2141_);
v___x_2088_ = v_toApplicative_2079_;
v_isShared_2089_ = v_isSharedCheck_2140_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_toSeqRight_2086_);
lean_inc(v_toSeqLeft_2085_);
lean_inc(v_toSeq_2084_);
lean_inc(v_toFunctor_2083_);
lean_dec(v_toApplicative_2079_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2140_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___f_2090_; lean_object* v___f_2091_; lean_object* v___f_2092_; lean_object* v___f_2093_; lean_object* v___x_2094_; lean_object* v___f_2095_; lean_object* v___f_2096_; lean_object* v___f_2097_; lean_object* v___x_2099_; 
v___f_2090_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__1));
v___f_2091_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2083_);
v___f_2092_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2092_, 0, v_toFunctor_2083_);
v___f_2093_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2093_, 0, v_toFunctor_2083_);
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___f_2092_);
lean_ctor_set(v___x_2094_, 1, v___f_2093_);
v___f_2095_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2095_, 0, v_toSeqRight_2086_);
v___f_2096_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2096_, 0, v_toSeqLeft_2085_);
v___f_2097_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2097_, 0, v_toSeq_2084_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 4, v___f_2095_);
lean_ctor_set(v___x_2088_, 3, v___f_2096_);
lean_ctor_set(v___x_2088_, 2, v___f_2097_);
lean_ctor_set(v___x_2088_, 1, v___f_2090_);
lean_ctor_set(v___x_2088_, 0, v___x_2094_);
v___x_2099_ = v___x_2088_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___f_2090_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v___f_2097_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v___f_2096_);
lean_ctor_set(v_reuseFailAlloc_2139_, 4, v___f_2095_);
v___x_2099_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2101_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v___f_2091_);
lean_ctor_set(v___x_2081_, 0, v___x_2099_);
v___x_2101_ = v___x_2081_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___f_2091_);
v___x_2101_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v_toApplicative_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2136_; 
v___x_2102_ = l_StateRefT_x27_instMonad___redArg(v___x_2101_);
v_toApplicative_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2136_ == 0)
{
lean_object* v_unused_2137_; 
v_unused_2137_ = lean_ctor_get(v___x_2102_, 1);
lean_dec(v_unused_2137_);
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2136_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_toApplicative_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2136_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_toFunctor_2107_; lean_object* v_toSeq_2108_; lean_object* v_toSeqLeft_2109_; lean_object* v_toSeqRight_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2134_; 
v_toFunctor_2107_ = lean_ctor_get(v_toApplicative_2103_, 0);
v_toSeq_2108_ = lean_ctor_get(v_toApplicative_2103_, 2);
v_toSeqLeft_2109_ = lean_ctor_get(v_toApplicative_2103_, 3);
v_toSeqRight_2110_ = lean_ctor_get(v_toApplicative_2103_, 4);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_toApplicative_2103_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v_toApplicative_2103_, 1);
lean_dec(v_unused_2135_);
v___x_2112_ = v_toApplicative_2103_;
v_isShared_2113_ = v_isSharedCheck_2134_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_toSeqRight_2110_);
lean_inc(v_toSeqLeft_2109_);
lean_inc(v_toSeq_2108_);
lean_inc(v_toFunctor_2107_);
lean_dec(v_toApplicative_2103_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2134_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___f_2114_; lean_object* v___f_2115_; lean_object* v___f_2116_; lean_object* v___f_2117_; lean_object* v___x_2118_; lean_object* v___f_2119_; lean_object* v___f_2120_; lean_object* v___f_2121_; lean_object* v___x_2123_; 
v___f_2114_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__3));
v___f_2115_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2107_);
v___f_2116_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2116_, 0, v_toFunctor_2107_);
v___f_2117_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2117_, 0, v_toFunctor_2107_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___f_2116_);
lean_ctor_set(v___x_2118_, 1, v___f_2117_);
v___f_2119_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2119_, 0, v_toSeqRight_2110_);
v___f_2120_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2120_, 0, v_toSeqLeft_2109_);
v___f_2121_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2121_, 0, v_toSeq_2108_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 4, v___f_2119_);
lean_ctor_set(v___x_2112_, 3, v___f_2120_);
lean_ctor_set(v___x_2112_, 2, v___f_2121_);
lean_ctor_set(v___x_2112_, 1, v___f_2114_);
lean_ctor_set(v___x_2112_, 0, v___x_2118_);
v___x_2123_ = v___x_2112_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___f_2114_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v___f_2121_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v___f_2120_);
lean_ctor_set(v_reuseFailAlloc_2133_, 4, v___f_2119_);
v___x_2123_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 1, v___f_2115_);
lean_ctor_set(v___x_2105_, 0, v___x_2123_);
v___x_2125_ = v___x_2105_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v___f_2115_);
v___x_2125_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___f_2129_; lean_object* v___x_1110__overap_2130_; lean_object* v___x_2131_; 
v___x_2126_ = l_StateRefT_x27_instMonad___redArg(v___x_2125_);
v___x_2127_ = lean_box(0);
v___x_2128_ = l_instInhabitedOfMonad___redArg(v___x_2126_, v___x_2127_);
v___f_2129_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2129_, 0, v___x_2128_);
v___x_1110__overap_2130_ = lean_panic_fn_borrowed(v___f_2129_, v_msg_2069_);
lean_dec_ref(v___f_2129_);
lean_inc(v___y_2075_);
lean_inc_ref(v___y_2074_);
lean_inc(v___y_2073_);
lean_inc_ref(v___y_2072_);
lean_inc(v___y_2071_);
lean_inc_ref(v___y_2070_);
v___x_2131_ = lean_apply_7(v___x_1110__overap_2130_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, lean_box(0));
return v___x_2131_;
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2069_ = stack[0].m_obj;
lean_object* v___y_2070_ = stack[1].m_obj;
lean_object* v___y_2071_ = stack[2].m_obj;
lean_object* v___y_2072_ = stack[3].m_obj;
lean_object* v___y_2073_ = stack[4].m_obj;
lean_object* v___y_2074_ = stack[5].m_obj;
lean_object* v___y_2075_ = stack[6].m_obj;
lean_object* v_res_2144_;
v_res_2144_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(v_msg_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
stack->m_obj
 = v_res_2144_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___boxed(lean_object* v_msg_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(v_msg_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
return v_res_2153_;
}
}
lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_2154_, uint8_t v___x_2155_, lean_object* v_derivedValMap_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_){
_start:
{
if (lean_obj_tag(v_x_2158_) == 0)
{
return v_x_2157_;
}
else
{
lean_object* v_head_2159_; lean_object* v_tail_2160_; lean_object* v_cinfo_2180_; lean_object* v_parents_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v_head_2159_ = lean_ctor_get(v_x_2158_, 0);
lean_inc(v_head_2159_);
v_tail_2160_ = lean_ctor_get(v_x_2158_, 1);
lean_inc(v_tail_2160_);
lean_dec_ref_known(v_x_2158_, 2);
v_cinfo_2180_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2156_, v_head_2159_);
v_parents_2181_ = lean_ctor_get(v_cinfo_2180_, 0);
lean_inc_ref(v_parents_2181_);
lean_dec_ref(v_cinfo_2180_);
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = lean_array_get_size(v_parents_2181_);
v___x_2184_ = lean_nat_dec_lt(v___x_2182_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_dec_ref(v_parents_2181_);
goto v___jp_2175_;
}
else
{
if (v___x_2184_ == 0)
{
lean_dec_ref(v_parents_2181_);
goto v___jp_2175_;
}
else
{
size_t v___x_2185_; size_t v___x_2186_; uint8_t v___x_2187_; 
v___x_2185_ = ((size_t)0ULL);
v___x_2186_ = lean_usize_of_nat(v___x_2183_);
v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2157_, v_parents_2181_, v___x_2185_, v___x_2186_);
lean_dec_ref(v_parents_2181_);
if (v___x_2187_ == 0)
{
goto v___jp_2175_;
}
else
{
lean_object* v___x_2188_; 
v___x_2188_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2154_, v___x_2155_, v_head_2159_, v_derivedValMap_2156_, v_x_2157_);
lean_dec(v_head_2159_);
v_x_2157_ = v___x_2188_;
v_x_2158_ = v_tail_2160_;
goto _start;
}
}
}
v___jp_2161_:
{
lean_object* v_vars_2162_; lean_object* v_borrows_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2174_; 
v_vars_2162_ = lean_ctor_get(v_x_2157_, 0);
v_borrows_2163_ = lean_ctor_get(v_x_2157_, 1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_x_2157_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2165_ = v_x_2157_;
v_isShared_2166_ = v_isSharedCheck_2174_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_borrows_2163_);
lean_inc(v_vars_2162_);
lean_dec(v_x_2157_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2174_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2167_ = lean_box(0);
lean_inc(v_head_2159_);
v___x_2168_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2163_, v_head_2159_, v___x_2167_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 1, v___x_2168_);
v___x_2170_ = v___x_2165_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_vars_2162_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2171_; 
v___x_2171_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2154_, v___x_2155_, v_head_2159_, v_derivedValMap_2156_, v___x_2170_);
lean_dec(v_head_2159_);
v_x_2157_ = v___x_2171_;
v_x_2158_ = v_tail_2160_;
goto _start;
}
}
}
v___jp_2175_:
{
lean_object* v_vars_2176_; uint8_t v___x_2177_; 
v_vars_2176_ = lean_ctor_get(v___x_2154_, 0);
v___x_2177_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2176_, v_head_2159_);
if (v___x_2177_ == 0)
{
goto v___jp_2161_;
}
else
{
if (v___x_2155_ == 0)
{
lean_object* v___x_2178_; 
v___x_2178_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2154_, v___x_2155_, v_head_2159_, v_derivedValMap_2156_, v_x_2157_);
lean_dec(v_head_2159_);
v_x_2157_ = v___x_2178_;
v_x_2158_ = v_tail_2160_;
goto _start;
}
else
{
goto v___jp_2161_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2154_ = stack[0].m_obj;
uint8_t v___x_2155_ = stack[1].m_num;
lean_object* v_derivedValMap_2156_ = stack[2].m_obj;
lean_object* v_x_2157_ = stack[3].m_obj;
lean_object* v_x_2158_ = stack[4].m_obj;
lean_object* v_res_2190_;
v_res_2190_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2154_, v___x_2155_, v_derivedValMap_2156_, v_x_2157_, v_x_2158_);
stack->m_obj
 = v_res_2190_;
}
lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(lean_object* v___x_2191_, uint8_t v___x_2192_, lean_object* v_derivedValMap_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_){
_start:
{
if (lean_obj_tag(v_x_2195_) == 0)
{
return v_x_2194_;
}
else
{
lean_object* v_head_2196_; lean_object* v_tail_2197_; lean_object* v_cinfo_2217_; lean_object* v_parents_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; 
v_head_2196_ = lean_ctor_get(v_x_2195_, 0);
lean_inc(v_head_2196_);
v_tail_2197_ = lean_ctor_get(v_x_2195_, 1);
lean_inc(v_tail_2197_);
lean_dec_ref_known(v_x_2195_, 2);
v_cinfo_2217_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2193_, v_head_2196_);
v_parents_2218_ = lean_ctor_get(v_cinfo_2217_, 0);
lean_inc_ref(v_parents_2218_);
lean_dec_ref(v_cinfo_2217_);
v___x_2219_ = lean_unsigned_to_nat(0u);
v___x_2220_ = lean_array_get_size(v_parents_2218_);
v___x_2221_ = lean_nat_dec_lt(v___x_2219_, v___x_2220_);
if (v___x_2221_ == 0)
{
lean_dec_ref(v_parents_2218_);
goto v___jp_2212_;
}
else
{
if (v___x_2221_ == 0)
{
lean_dec_ref(v_parents_2218_);
goto v___jp_2212_;
}
else
{
size_t v___x_2222_; size_t v___x_2223_; uint8_t v___x_2224_; 
v___x_2222_ = ((size_t)0ULL);
v___x_2223_ = lean_usize_of_nat(v___x_2220_);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2194_, v_parents_2218_, v___x_2222_, v___x_2223_);
lean_dec_ref(v_parents_2218_);
if (v___x_2224_ == 0)
{
goto v___jp_2212_;
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2191_, v___x_2192_, v_head_2196_, v_derivedValMap_2193_, v_x_2194_);
lean_dec(v_head_2196_);
v___x_2226_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2191_, v___x_2192_, v_derivedValMap_2193_, v___x_2225_, v_tail_2197_);
return v___x_2226_;
}
}
}
v___jp_2198_:
{
lean_object* v_vars_2199_; lean_object* v_borrows_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2211_; 
v_vars_2199_ = lean_ctor_get(v_x_2194_, 0);
v_borrows_2200_ = lean_ctor_get(v_x_2194_, 1);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_x_2194_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2202_ = v_x_2194_;
v_isShared_2203_ = v_isSharedCheck_2211_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_borrows_2200_);
lean_inc(v_vars_2199_);
lean_dec(v_x_2194_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2211_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2204_ = lean_box(0);
lean_inc(v_head_2196_);
v___x_2205_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2200_, v_head_2196_, v___x_2204_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 1, v___x_2205_);
v___x_2207_ = v___x_2202_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_vars_2199_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2191_, v___x_2192_, v_head_2196_, v_derivedValMap_2193_, v___x_2207_);
lean_dec(v_head_2196_);
v___x_2209_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2191_, v___x_2192_, v_derivedValMap_2193_, v___x_2208_, v_tail_2197_);
return v___x_2209_;
}
}
}
v___jp_2212_:
{
lean_object* v_vars_2213_; uint8_t v___x_2214_; 
v_vars_2213_ = lean_ctor_get(v___x_2191_, 0);
v___x_2214_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2213_, v_head_2196_);
if (v___x_2214_ == 0)
{
goto v___jp_2198_;
}
else
{
if (v___x_2192_ == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2191_, v___x_2192_, v_head_2196_, v_derivedValMap_2193_, v_x_2194_);
lean_dec(v_head_2196_);
v___x_2216_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2191_, v___x_2192_, v_derivedValMap_2193_, v___x_2215_, v_tail_2197_);
return v___x_2216_;
}
else
{
goto v___jp_2198_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2191_ = stack[0].m_obj;
uint8_t v___x_2192_ = stack[1].m_num;
lean_object* v_derivedValMap_2193_ = stack[2].m_obj;
lean_object* v_x_2194_ = stack[3].m_obj;
lean_object* v_x_2195_ = stack[4].m_obj;
lean_object* v_res_2227_;
v_res_2227_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(v___x_2191_, v___x_2192_, v_derivedValMap_2193_, v_x_2194_, v_x_2195_);
stack->m_obj
 = v_res_2227_;
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(lean_object* v___x_2228_, uint8_t v___x_2229_, lean_object* v_fvarId_2230_, lean_object* v_derivedValMap_2231_, lean_object* v_liveVars_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_derivedValMap_2231_, v_fvarId_2230_);
if (lean_obj_tag(v___x_2233_) == 1)
{
lean_object* v_val_2234_; lean_object* v_children_2235_; lean_object* v___x_2236_; 
v_val_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_val_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v_children_2235_ = lean_ctor_get(v_val_2234_, 1);
lean_inc(v_children_2235_);
lean_dec(v_val_2234_);
v___x_2236_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(v___x_2228_, v___x_2229_, v_derivedValMap_2231_, v_liveVars_2232_, v_children_2235_);
return v___x_2236_;
}
else
{
lean_dec(v___x_2233_);
return v_liveVars_2232_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2228_ = stack[0].m_obj;
uint8_t v___x_2229_ = stack[1].m_num;
lean_object* v_fvarId_2230_ = stack[2].m_obj;
lean_object* v_derivedValMap_2231_ = stack[3].m_obj;
lean_object* v_liveVars_2232_ = stack[4].m_obj;
lean_object* v_res_2237_;
v_res_2237_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2228_, v___x_2229_, v_fvarId_2230_, v_derivedValMap_2231_, v_liveVars_2232_);
stack->m_obj
 = v_res_2237_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0___boxed(lean_object* v___x_2238_, lean_object* v___x_2239_, lean_object* v_fvarId_2240_, lean_object* v_derivedValMap_2241_, lean_object* v_liveVars_2242_){
_start:
{
uint8_t v___x_1802__boxed_2243_; lean_object* v_res_2244_; 
v___x_1802__boxed_2243_ = lean_unbox(v___x_2239_);
v_res_2244_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2238_, v___x_1802__boxed_2243_, v_fvarId_2240_, v_derivedValMap_2241_, v_liveVars_2242_);
lean_dec(v_derivedValMap_2241_);
lean_dec(v_fvarId_2240_);
lean_dec_ref(v___x_2238_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v___x_2245_, lean_object* v___x_2246_, lean_object* v_derivedValMap_2247_, lean_object* v_x_2248_, lean_object* v_x_2249_){
_start:
{
uint8_t v___x_1807__boxed_2250_; lean_object* v_res_2251_; 
v___x_1807__boxed_2250_ = lean_unbox(v___x_2246_);
v_res_2251_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2245_, v___x_1807__boxed_2250_, v_derivedValMap_2247_, v_x_2248_, v_x_2249_);
lean_dec(v_derivedValMap_2247_);
lean_dec_ref(v___x_2245_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2___boxed(lean_object* v___x_2252_, lean_object* v___x_2253_, lean_object* v_derivedValMap_2254_, lean_object* v_x_2255_, lean_object* v_x_2256_){
_start:
{
uint8_t v___x_1831__boxed_2257_; lean_object* v_res_2258_; 
v___x_1831__boxed_2257_ = lean_unbox(v___x_2253_);
v_res_2258_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(v___x_2252_, v___x_1831__boxed_2257_, v_derivedValMap_2254_, v_x_2255_, v_x_2256_);
lean_dec(v_derivedValMap_2254_);
lean_dec_ref(v___x_2252_);
return v_res_2258_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(lean_object* v_fvarId_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v_vars_2264_; uint8_t v___x_2265_; 
v___x_2263_ = lean_st_ref_get(v_a_2261_);
v_vars_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc_ref(v_vars_2264_);
lean_dec(v___x_2263_);
v___x_2265_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2264_, v_fvarId_2259_);
lean_dec_ref(v_vars_2264_);
if (v___x_2265_ == 0)
{
lean_object* v_derivedValMap_2266_; lean_object* v___x_2267_; lean_object* v_vars_2268_; lean_object* v_borrows_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2283_; 
v_derivedValMap_2266_ = lean_ctor_get(v_a_2260_, 2);
v___x_2267_ = lean_st_ref_take(v_a_2261_);
v_vars_2268_ = lean_ctor_get(v___x_2267_, 0);
v_borrows_2269_ = lean_ctor_get(v___x_2267_, 1);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2271_ = v___x_2267_;
v_isShared_2272_ = v_isSharedCheck_2283_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_borrows_2269_);
lean_inc(v_vars_2268_);
lean_dec(v___x_2267_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2283_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2273_ = lean_box(0);
lean_inc(v_fvarId_2259_);
v___x_2274_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_vars_2268_, v_fvarId_2259_, v___x_2273_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2274_);
v___x_2276_ = v___x_2271_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_borrows_2269_);
v___x_2276_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2277_ = lean_st_ref_put(v_a_2261_, v___x_2276_);
v___x_2278_ = lean_st_ref_take(v_a_2261_);
lean_inc(v___x_2278_);
v___x_2279_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2278_, v___x_2265_, v_fvarId_2259_, v_derivedValMap_2266_, v___x_2278_);
lean_dec(v_fvarId_2259_);
lean_dec(v___x_2278_);
v___x_2280_ = lean_st_ref_put(v_a_2261_, v___x_2279_);
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2273_);
return v___x_2281_;
}
}
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec(v_fvarId_2259_);
v___x_2284_ = lean_box(0);
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
return v___x_2285_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2259_ = stack[0].m_obj;
lean_object* v_a_2260_ = stack[1].m_obj;
lean_object* v_a_2261_ = stack[2].m_obj;
lean_object* v_res_2286_;
v_res_2286_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2259_, v_a_2260_, v_a_2261_);
stack->m_obj
 = v_res_2286_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg___boxed(lean_object* v_fvarId_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2287_, v_a_2288_, v_a_2289_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
return v_res_2291_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2293_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_2294_ = lean_unsigned_to_nat(20u);
v___x_2295_ = lean_unsigned_to_nat(343u);
v___x_2296_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__0));
v___x_2297_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_2298_ = l_mkPanicMessageWithDecl(v___x_2297_, v___x_2296_, v___x_2295_, v___x_2294_, v___x_2293_);
return v___x_2298_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(lean_object* v_value_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_){
_start:
{
switch(lean_obj_tag(v_value_2299_))
{
case 4:
{
lean_object* v_fvarId_2307_; lean_object* v_args_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_fvarId_2307_ = lean_ctor_get(v_value_2299_, 0);
lean_inc(v_fvarId_2307_);
v_args_2308_ = lean_ctor_get(v_value_2299_, 1);
lean_inc_ref(v_args_2308_);
lean_dec_ref_known(v_value_2299_, 2);
v___x_2309_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2307_, v_a_2300_, v_a_2301_);
lean_dec_ref(v___x_2309_);
v___x_2310_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2308_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec_ref(v_args_2308_);
return v___x_2310_;
}
case 5:
{
lean_object* v_args_2311_; lean_object* v___x_2312_; 
v_args_2311_ = lean_ctor_get(v_value_2299_, 1);
lean_inc_ref(v_args_2311_);
lean_dec_ref_known(v_value_2299_, 2);
v___x_2312_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2311_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec_ref(v_args_2311_);
return v___x_2312_;
}
case 6:
{
lean_object* v_var_2313_; lean_object* v___x_2314_; 
v_var_2313_ = lean_ctor_get(v_value_2299_, 1);
lean_inc(v_var_2313_);
lean_dec_ref_known(v_value_2299_, 2);
v___x_2314_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2313_, v_a_2300_, v_a_2301_);
return v___x_2314_;
}
case 7:
{
lean_object* v_var_2315_; lean_object* v___x_2316_; 
v_var_2315_ = lean_ctor_get(v_value_2299_, 1);
lean_inc(v_var_2315_);
lean_dec_ref_known(v_value_2299_, 2);
v___x_2316_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2315_, v_a_2300_, v_a_2301_);
return v___x_2316_;
}
case 8:
{
lean_object* v_var_2317_; lean_object* v___x_2318_; 
v_var_2317_ = lean_ctor_get(v_value_2299_, 2);
lean_inc(v_var_2317_);
lean_dec_ref_known(v_value_2299_, 3);
v___x_2318_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2317_, v_a_2300_, v_a_2301_);
return v___x_2318_;
}
case 9:
{
lean_object* v_args_2319_; lean_object* v___x_2320_; 
v_args_2319_ = lean_ctor_get(v_value_2299_, 1);
lean_inc_ref(v_args_2319_);
lean_dec_ref_known(v_value_2299_, 2);
v___x_2320_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2319_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec_ref(v_args_2319_);
return v___x_2320_;
}
case 10:
{
lean_object* v_args_2321_; lean_object* v___x_2322_; 
v_args_2321_ = lean_ctor_get(v_value_2299_, 1);
lean_inc_ref(v_args_2321_);
lean_dec_ref_known(v_value_2299_, 2);
v___x_2322_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2321_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec_ref(v_args_2321_);
return v___x_2322_;
}
case 11:
{
lean_object* v_var_2323_; lean_object* v___x_2324_; 
v_var_2323_ = lean_ctor_get(v_value_2299_, 1);
lean_inc(v_var_2323_);
lean_dec_ref_known(v_value_2299_, 2);
v___x_2324_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2323_, v_a_2300_, v_a_2301_);
return v___x_2324_;
}
case 12:
{
lean_object* v_var_2325_; lean_object* v_args_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v_var_2325_ = lean_ctor_get(v_value_2299_, 0);
lean_inc(v_var_2325_);
v_args_2326_ = lean_ctor_get(v_value_2299_, 2);
lean_inc_ref(v_args_2326_);
lean_dec_ref_known(v_value_2299_, 3);
v___x_2327_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2325_, v_a_2300_, v_a_2301_);
lean_dec_ref(v___x_2327_);
v___x_2328_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2326_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec_ref(v_args_2326_);
return v___x_2328_;
}
case 13:
{
lean_object* v_fvarId_2329_; lean_object* v___x_2330_; 
v_fvarId_2329_ = lean_ctor_get(v_value_2299_, 1);
lean_inc(v_fvarId_2329_);
lean_dec_ref_known(v_value_2299_, 2);
v___x_2330_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2329_, v_a_2300_, v_a_2301_);
return v___x_2330_;
}
case 14:
{
lean_object* v_fvarId_2331_; lean_object* v___x_2332_; 
v_fvarId_2331_ = lean_ctor_get(v_value_2299_, 0);
lean_inc(v_fvarId_2331_);
lean_dec_ref_known(v_value_2299_, 1);
v___x_2332_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2331_, v_a_2300_, v_a_2301_);
return v___x_2332_;
}
case 15:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec_ref_known(v_value_2299_, 1);
v___x_2333_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1);
v___x_2334_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(v___x_2333_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
return v___x_2334_;
}
default: 
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_dec(v_value_2299_);
v___x_2335_ = lean_box(0);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
return v___x_2336_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_2299_ = stack[0].m_obj;
lean_object* v_a_2300_ = stack[1].m_obj;
lean_object* v_a_2301_ = stack[2].m_obj;
lean_object* v_a_2302_ = stack[3].m_obj;
lean_object* v_a_2303_ = stack[4].m_obj;
lean_object* v_a_2304_ = stack[5].m_obj;
lean_object* v_a_2305_ = stack[6].m_obj;
lean_object* v_res_2337_;
v_res_2337_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(v_value_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
stack->m_obj
 = v_res_2337_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___boxed(lean_object* v_value_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(v_value_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
return v_res_2346_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(lean_object* v_fvarId_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2347_, v_a_2348_, v_a_2349_);
return v___x_2355_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2347_ = stack[0].m_obj;
lean_object* v_a_2348_ = stack[1].m_obj;
lean_object* v_a_2349_ = stack[2].m_obj;
lean_object* v_a_2350_ = stack[3].m_obj;
lean_object* v_a_2351_ = stack[4].m_obj;
lean_object* v_a_2352_ = stack[5].m_obj;
lean_object* v_a_2353_ = stack[6].m_obj;
lean_object* v_res_2356_;
v_res_2356_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(v_fvarId_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_);
stack->m_obj
 = v_res_2356_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___boxed(lean_object* v_fvarId_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(v_fvarId_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
return v_res_2365_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(lean_object* v_fvarId_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v___x_2369_; lean_object* v_vars_2370_; lean_object* v_borrows_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2385_; 
v___x_2369_ = lean_st_ref_take(v_a_2367_);
v_vars_2370_ = lean_ctor_get(v___x_2369_, 0);
v_borrows_2371_ = lean_ctor_get(v___x_2369_, 1);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2373_ = v___x_2369_;
v_isShared_2374_ = v_isSharedCheck_2385_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_borrows_2371_);
lean_inc(v_vars_2370_);
lean_dec(v___x_2369_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2385_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v_vars_2378_; lean_object* v_borrows_2379_; lean_object* v___x_2381_; 
v___x_2375_ = lean_box(0);
v___x_2376_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_2377_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
lean_inc(v_fvarId_2366_);
v_vars_2378_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2376_, v___x_2377_, v_vars_2370_, v_fvarId_2366_);
v_borrows_2379_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2376_, v___x_2377_, v_borrows_2371_, v_fvarId_2366_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 1, v_borrows_2379_);
lean_ctor_set(v___x_2373_, 0, v_vars_2378_);
v___x_2381_ = v___x_2373_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_vars_2378_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_borrows_2379_);
v___x_2381_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_st_ref_put(v_a_2367_, v___x_2381_);
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2375_);
return v___x_2383_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2366_ = stack[0].m_obj;
lean_object* v_a_2367_ = stack[1].m_obj;
lean_object* v_res_2386_;
v_res_2386_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(v_fvarId_2366_, v_a_2367_);
stack->m_obj
 = v_res_2386_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg___boxed(lean_object* v_fvarId_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(v_fvarId_2387_, v_a_2388_);
lean_dec(v_a_2388_);
return v_res_2390_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(lean_object* v_fvarId_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v___x_2399_; lean_object* v_vars_2400_; lean_object* v_borrows_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2415_; 
v___x_2399_ = lean_st_ref_take(v_a_2393_);
v_vars_2400_ = lean_ctor_get(v___x_2399_, 0);
v_borrows_2401_ = lean_ctor_get(v___x_2399_, 1);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2403_ = v___x_2399_;
v_isShared_2404_ = v_isSharedCheck_2415_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_borrows_2401_);
lean_inc(v_vars_2400_);
lean_dec(v___x_2399_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2415_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v_vars_2408_; lean_object* v_borrows_2409_; lean_object* v___x_2411_; 
v___x_2405_ = lean_box(0);
v___x_2406_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_2407_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
lean_inc(v_fvarId_2391_);
v_vars_2408_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2406_, v___x_2407_, v_vars_2400_, v_fvarId_2391_);
v_borrows_2409_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2406_, v___x_2407_, v_borrows_2401_, v_fvarId_2391_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 1, v_borrows_2409_);
lean_ctor_set(v___x_2403_, 0, v_vars_2408_);
v___x_2411_ = v___x_2403_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_vars_2408_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_borrows_2409_);
v___x_2411_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_st_ref_put(v_a_2393_, v___x_2411_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2405_);
return v___x_2413_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2391_ = stack[0].m_obj;
lean_object* v_a_2392_ = stack[1].m_obj;
lean_object* v_a_2393_ = stack[2].m_obj;
lean_object* v_a_2394_ = stack[3].m_obj;
lean_object* v_a_2395_ = stack[4].m_obj;
lean_object* v_a_2396_ = stack[5].m_obj;
lean_object* v_a_2397_ = stack[6].m_obj;
lean_object* v_res_2416_;
v_res_2416_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(v_fvarId_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
stack->m_obj
 = v_res_2416_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___boxed(lean_object* v_fvarId_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(v_fvarId_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(lean_object* v_liveVars_2426_, lean_object* v_derivedValMap_2427_, lean_object* v_x_2428_, lean_object* v_x_2429_){
_start:
{
if (lean_obj_tag(v_x_2429_) == 0)
{
return v_x_2428_;
}
else
{
lean_object* v_head_2430_; lean_object* v_tail_2431_; lean_object* v_cinfo_2450_; lean_object* v_parents_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v_head_2430_ = lean_ctor_get(v_x_2429_, 0);
lean_inc(v_head_2430_);
v_tail_2431_ = lean_ctor_get(v_x_2429_, 1);
lean_inc(v_tail_2431_);
lean_dec_ref_known(v_x_2429_, 2);
v_cinfo_2450_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2427_, v_head_2430_);
v_parents_2451_ = lean_ctor_get(v_cinfo_2450_, 0);
lean_inc_ref(v_parents_2451_);
lean_dec_ref(v_cinfo_2450_);
v___x_2452_ = lean_unsigned_to_nat(0u);
v___x_2453_ = lean_array_get_size(v_parents_2451_);
v___x_2454_ = lean_nat_dec_lt(v___x_2452_, v___x_2453_);
if (v___x_2454_ == 0)
{
lean_dec_ref(v_parents_2451_);
goto v___jp_2432_;
}
else
{
if (v___x_2454_ == 0)
{
lean_dec_ref(v_parents_2451_);
goto v___jp_2432_;
}
else
{
size_t v___x_2455_; size_t v___x_2456_; uint8_t v___x_2457_; 
v___x_2455_ = ((size_t)0ULL);
v___x_2456_ = lean_usize_of_nat(v___x_2453_);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2428_, v_parents_2451_, v___x_2455_, v___x_2456_);
lean_dec_ref(v_parents_2451_);
if (v___x_2457_ == 0)
{
goto v___jp_2432_;
}
else
{
lean_object* v___x_2458_; 
v___x_2458_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2426_, v_head_2430_, v_derivedValMap_2427_, v_x_2428_);
lean_dec(v_head_2430_);
v_x_2428_ = v___x_2458_;
v_x_2429_ = v_tail_2431_;
goto _start;
}
}
}
v___jp_2432_:
{
lean_object* v_vars_2433_; uint8_t v___x_2434_; 
v_vars_2433_ = lean_ctor_get(v_liveVars_2426_, 0);
v___x_2434_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2433_, v_head_2430_);
if (v___x_2434_ == 0)
{
lean_object* v_vars_2435_; lean_object* v_borrows_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2447_; 
v_vars_2435_ = lean_ctor_get(v_x_2428_, 0);
v_borrows_2436_ = lean_ctor_get(v_x_2428_, 1);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_x_2428_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2438_ = v_x_2428_;
v_isShared_2439_ = v_isSharedCheck_2447_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_borrows_2436_);
lean_inc(v_vars_2435_);
lean_dec(v_x_2428_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2447_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2440_ = lean_box(0);
lean_inc(v_head_2430_);
v___x_2441_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2436_, v_head_2430_, v___x_2440_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 1, v___x_2441_);
v___x_2443_ = v___x_2438_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_vars_2435_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2444_; 
v___x_2444_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2426_, v_head_2430_, v_derivedValMap_2427_, v___x_2443_);
lean_dec(v_head_2430_);
v_x_2428_ = v___x_2444_;
v_x_2429_ = v_tail_2431_;
goto _start;
}
}
}
else
{
lean_object* v___x_2448_; 
v___x_2448_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2426_, v_head_2430_, v_derivedValMap_2427_, v_x_2428_);
lean_dec(v_head_2430_);
v_x_2428_ = v___x_2448_;
v_x_2429_ = v_tail_2431_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(lean_object* v_liveVars_2460_, lean_object* v_derivedValMap_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_){
_start:
{
if (lean_obj_tag(v_x_2463_) == 0)
{
return v_x_2462_;
}
else
{
lean_object* v_head_2464_; lean_object* v_tail_2465_; lean_object* v_cinfo_2484_; lean_object* v_parents_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
v_head_2464_ = lean_ctor_get(v_x_2463_, 0);
lean_inc(v_head_2464_);
v_tail_2465_ = lean_ctor_get(v_x_2463_, 1);
lean_inc(v_tail_2465_);
lean_dec_ref_known(v_x_2463_, 2);
v_cinfo_2484_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2461_, v_head_2464_);
v_parents_2485_ = lean_ctor_get(v_cinfo_2484_, 0);
lean_inc_ref(v_parents_2485_);
lean_dec_ref(v_cinfo_2484_);
v___x_2486_ = lean_unsigned_to_nat(0u);
v___x_2487_ = lean_array_get_size(v_parents_2485_);
v___x_2488_ = lean_nat_dec_lt(v___x_2486_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_dec_ref(v_parents_2485_);
goto v___jp_2466_;
}
else
{
if (v___x_2488_ == 0)
{
lean_dec_ref(v_parents_2485_);
goto v___jp_2466_;
}
else
{
size_t v___x_2489_; size_t v___x_2490_; uint8_t v___x_2491_; 
v___x_2489_ = ((size_t)0ULL);
v___x_2490_ = lean_usize_of_nat(v___x_2487_);
v___x_2491_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2462_, v_parents_2485_, v___x_2489_, v___x_2490_);
lean_dec_ref(v_parents_2485_);
if (v___x_2491_ == 0)
{
goto v___jp_2466_;
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2460_, v_head_2464_, v_derivedValMap_2461_, v_x_2462_);
lean_dec(v_head_2464_);
v___x_2493_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2460_, v_derivedValMap_2461_, v___x_2492_, v_tail_2465_);
return v___x_2493_;
}
}
}
v___jp_2466_:
{
lean_object* v_vars_2467_; uint8_t v___x_2468_; 
v_vars_2467_ = lean_ctor_get(v_liveVars_2460_, 0);
v___x_2468_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2467_, v_head_2464_);
if (v___x_2468_ == 0)
{
lean_object* v_vars_2469_; lean_object* v_borrows_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2481_; 
v_vars_2469_ = lean_ctor_get(v_x_2462_, 0);
v_borrows_2470_ = lean_ctor_get(v_x_2462_, 1);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_x_2462_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2472_ = v_x_2462_;
v_isShared_2473_ = v_isSharedCheck_2481_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_borrows_2470_);
lean_inc(v_vars_2469_);
lean_dec(v_x_2462_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2481_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2474_ = lean_box(0);
lean_inc(v_head_2464_);
v___x_2475_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2470_, v_head_2464_, v___x_2474_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 1, v___x_2475_);
v___x_2477_ = v___x_2472_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_vars_2469_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2460_, v_head_2464_, v_derivedValMap_2461_, v___x_2477_);
lean_dec(v_head_2464_);
v___x_2479_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2460_, v_derivedValMap_2461_, v___x_2478_, v_tail_2465_);
return v___x_2479_;
}
}
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2460_, v_head_2464_, v_derivedValMap_2461_, v_x_2462_);
lean_dec(v_head_2464_);
v___x_2483_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2460_, v_derivedValMap_2461_, v___x_2482_, v_tail_2465_);
return v___x_2483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(lean_object* v_liveVars_2494_, lean_object* v_fvarId_2495_, lean_object* v_derivedValMap_2496_, lean_object* v_liveVars_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_derivedValMap_2496_, v_fvarId_2495_);
if (lean_obj_tag(v___x_2498_) == 1)
{
lean_object* v_val_2499_; lean_object* v_children_2500_; lean_object* v___x_2501_; 
v_val_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_val_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v_children_2500_ = lean_ctor_get(v_val_2499_, 1);
lean_inc(v_children_2500_);
lean_dec(v_val_2499_);
v___x_2501_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(v_liveVars_2494_, v_derivedValMap_2496_, v_liveVars_2497_, v_children_2500_);
return v___x_2501_;
}
else
{
lean_dec(v___x_2498_);
return v_liveVars_2497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0___boxed(lean_object* v_liveVars_2502_, lean_object* v_fvarId_2503_, lean_object* v_derivedValMap_2504_, lean_object* v_liveVars_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2502_, v_fvarId_2503_, v_derivedValMap_2504_, v_liveVars_2505_);
lean_dec(v_derivedValMap_2504_);
lean_dec(v_fvarId_2503_);
lean_dec_ref(v_liveVars_2502_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1___boxed(lean_object* v_liveVars_2507_, lean_object* v_derivedValMap_2508_, lean_object* v_x_2509_, lean_object* v_x_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2507_, v_derivedValMap_2508_, v_x_2509_, v_x_2510_);
lean_dec(v_derivedValMap_2508_);
lean_dec_ref(v_liveVars_2507_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0___boxed(lean_object* v_liveVars_2512_, lean_object* v_derivedValMap_2513_, lean_object* v_x_2514_, lean_object* v_x_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(v_liveVars_2512_, v_derivedValMap_2513_, v_x_2514_, v_x_2515_);
lean_dec(v_derivedValMap_2513_);
lean_dec_ref(v_liveVars_2512_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(lean_object* v_a_2517_, lean_object* v_liveVars_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_){
_start:
{
if (lean_obj_tag(v_x_2520_) == 0)
{
return v_x_2519_;
}
else
{
lean_object* v_key_2521_; lean_object* v_tail_2522_; lean_object* v_derivedValMap_2523_; lean_object* v___x_2524_; 
v_key_2521_ = lean_ctor_get(v_x_2520_, 0);
v_tail_2522_ = lean_ctor_get(v_x_2520_, 2);
v_derivedValMap_2523_ = lean_ctor_get(v_a_2517_, 2);
v___x_2524_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2518_, v_key_2521_, v_derivedValMap_2523_, v_x_2519_);
v_x_2519_ = v___x_2524_;
v_x_2520_ = v_tail_2522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2___boxed(lean_object* v_a_2526_, lean_object* v_liveVars_2527_, lean_object* v_x_2528_, lean_object* v_x_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(v_a_2526_, v_liveVars_2527_, v_x_2528_, v_x_2529_);
lean_dec(v_x_2529_);
lean_dec_ref(v_liveVars_2527_);
lean_dec_ref(v_a_2526_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(lean_object* v_a_2531_, lean_object* v_liveVars_2532_, lean_object* v_x_2533_, lean_object* v_x_2534_){
_start:
{
if (lean_obj_tag(v_x_2534_) == 0)
{
return v_x_2533_;
}
else
{
lean_object* v_key_2535_; lean_object* v_tail_2536_; lean_object* v_derivedValMap_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_key_2535_ = lean_ctor_get(v_x_2534_, 0);
v_tail_2536_ = lean_ctor_get(v_x_2534_, 2);
v_derivedValMap_2537_ = lean_ctor_get(v_a_2531_, 2);
v___x_2538_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2532_, v_key_2535_, v_derivedValMap_2537_, v_x_2533_);
v___x_2539_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(v_a_2531_, v_liveVars_2532_, v___x_2538_, v_tail_2536_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1___boxed(lean_object* v_a_2540_, lean_object* v_liveVars_2541_, lean_object* v_x_2542_, lean_object* v_x_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(v_a_2540_, v_liveVars_2541_, v_x_2542_, v_x_2543_);
lean_dec(v_x_2543_);
lean_dec_ref(v_liveVars_2541_);
lean_dec_ref(v_a_2540_);
return v_res_2544_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(lean_object* v_a_2545_, lean_object* v_liveVars_2546_, lean_object* v_as_2547_, size_t v_i_2548_, size_t v_stop_2549_, lean_object* v_b_2550_){
_start:
{
uint8_t v___x_2551_; 
v___x_2551_ = lean_usize_dec_eq(v_i_2548_, v_stop_2549_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; size_t v___x_2554_; size_t v___x_2555_; 
v___x_2552_ = lean_array_uget_borrowed(v_as_2547_, v_i_2548_);
v___x_2553_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(v_a_2545_, v_liveVars_2546_, v_b_2550_, v___x_2552_);
v___x_2554_ = ((size_t)1ULL);
v___x_2555_ = lean_usize_add(v_i_2548_, v___x_2554_);
v_i_2548_ = v___x_2555_;
v_b_2550_ = v___x_2553_;
goto _start;
}
else
{
return v_b_2550_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2545_ = stack[0].m_obj;
lean_object* v_liveVars_2546_ = stack[1].m_obj;
lean_object* v_as_2547_ = stack[2].m_obj;
size_t v_i_2548_ = stack[3].m_num;
size_t v_stop_2549_ = stack[4].m_num;
lean_object* v_b_2550_ = stack[5].m_obj;
lean_object* v_res_2557_;
v_res_2557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2545_, v_liveVars_2546_, v_as_2547_, v_i_2548_, v_stop_2549_, v_b_2550_);
stack->m_obj
 = v_res_2557_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2___boxed(lean_object* v_a_2558_, lean_object* v_liveVars_2559_, lean_object* v_as_2560_, lean_object* v_i_2561_, lean_object* v_stop_2562_, lean_object* v_b_2563_){
_start:
{
size_t v_i_boxed_2564_; size_t v_stop_boxed_2565_; lean_object* v_res_2566_; 
v_i_boxed_2564_ = lean_unbox_usize(v_i_2561_);
lean_dec(v_i_2561_);
v_stop_boxed_2565_ = lean_unbox_usize(v_stop_2562_);
lean_dec(v_stop_2562_);
v_res_2566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2558_, v_liveVars_2559_, v_as_2560_, v_i_boxed_2564_, v_stop_boxed_2565_, v_b_2563_);
lean_dec_ref(v_as_2560_);
lean_dec_ref(v_liveVars_2559_);
lean_dec_ref(v_a_2558_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(lean_object* v_a_2567_, lean_object* v_liveVars_2568_, lean_object* v_x_2569_, lean_object* v_x_2570_){
_start:
{
if (lean_obj_tag(v_x_2570_) == 0)
{
return v_x_2569_;
}
else
{
lean_object* v_head_2571_; lean_object* v_tail_2572_; lean_object* v_derivedValMap_2573_; lean_object* v_vars_2574_; lean_object* v_borrows_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2586_; 
v_head_2571_ = lean_ctor_get(v_x_2570_, 0);
lean_inc(v_head_2571_);
v_tail_2572_ = lean_ctor_get(v_x_2570_, 1);
lean_inc(v_tail_2572_);
lean_dec_ref_known(v_x_2570_, 2);
v_derivedValMap_2573_ = lean_ctor_get(v_a_2567_, 2);
v_vars_2574_ = lean_ctor_get(v_x_2569_, 0);
v_borrows_2575_ = lean_ctor_get(v_x_2569_, 1);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_x_2569_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2577_ = v_x_2569_;
v_isShared_2578_ = v_isSharedCheck_2586_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_borrows_2575_);
lean_inc(v_vars_2574_);
lean_dec(v_x_2569_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2586_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2579_ = lean_box(0);
lean_inc(v_head_2571_);
v___x_2580_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2575_, v_head_2571_, v___x_2579_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 1, v___x_2580_);
v___x_2582_ = v___x_2577_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_vars_2574_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2583_; 
v___x_2583_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2568_, v_head_2571_, v_derivedValMap_2573_, v___x_2582_);
lean_dec(v_head_2571_);
v_x_2569_ = v___x_2583_;
v_x_2570_ = v_tail_2572_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3___boxed(lean_object* v_a_2587_, lean_object* v_liveVars_2588_, lean_object* v_x_2589_, lean_object* v_x_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(v_a_2587_, v_liveVars_2588_, v_x_2589_, v_x_2590_);
lean_dec_ref(v_liveVars_2588_);
lean_dec_ref(v_a_2587_);
return v_res_2591_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(lean_object* v_liveVars_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v___y_2596_; lean_object* v_unconditionalBorrows_2607_; lean_object* v___x_2608_; lean_object* v_vars_2609_; lean_object* v_buckets_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; 
v_unconditionalBorrows_2607_ = lean_ctor_get(v_a_2593_, 1);
lean_inc(v_unconditionalBorrows_2607_);
lean_inc_ref(v_liveVars_2592_);
v___x_2608_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(v_a_2593_, v_liveVars_2592_, v_liveVars_2592_, v_unconditionalBorrows_2607_);
v_vars_2609_ = lean_ctor_get(v_liveVars_2592_, 0);
v_buckets_2610_ = lean_ctor_get(v_vars_2609_, 1);
v___x_2611_ = lean_unsigned_to_nat(0u);
v___x_2612_ = lean_array_get_size(v_buckets_2610_);
v___x_2613_ = lean_nat_dec_lt(v___x_2611_, v___x_2612_);
if (v___x_2613_ == 0)
{
v___y_2596_ = v___x_2608_;
goto v___jp_2595_;
}
else
{
size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = lean_usize_of_nat(v___x_2612_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2593_, v_liveVars_2592_, v_buckets_2610_, v___x_2614_, v___x_2615_, v___x_2608_);
v___y_2596_ = v___x_2616_;
goto v___jp_2595_;
}
v___jp_2595_:
{
lean_object* v_borrows_2597_; lean_object* v_buckets_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v_borrows_2597_ = lean_ctor_get(v___y_2596_, 1);
v_buckets_2598_ = lean_ctor_get(v_borrows_2597_, 1);
v___x_2599_ = lean_unsigned_to_nat(0u);
v___x_2600_ = lean_array_get_size(v_buckets_2598_);
v___x_2601_ = lean_nat_dec_lt(v___x_2599_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; 
lean_dec_ref(v_liveVars_2592_);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___y_2596_);
return v___x_2602_;
}
else
{
size_t v___x_2603_; size_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_inc_ref(v_buckets_2598_);
v___x_2603_ = ((size_t)0ULL);
v___x_2604_ = lean_usize_of_nat(v___x_2600_);
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2593_, v_liveVars_2592_, v_buckets_2598_, v___x_2603_, v___x_2604_, v___y_2596_);
lean_dec_ref(v_buckets_2598_);
lean_dec_ref(v_liveVars_2592_);
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
return v___x_2606_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_liveVars_2592_ = stack[0].m_obj;
lean_object* v_a_2593_ = stack[1].m_obj;
lean_object* v_res_2617_;
v_res_2617_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v_liveVars_2592_, v_a_2593_);
stack->m_obj
 = v_res_2617_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg___boxed(lean_object* v_liveVars_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v_liveVars_2618_, v_a_2619_);
lean_dec_ref(v_a_2619_);
return v_res_2621_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows(lean_object* v_liveVars_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v_liveVars_2622_, v_a_2623_);
return v___x_2630_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_0interp(lean_interpreter_value* stack)
{
lean_object* v_liveVars_2622_ = stack[0].m_obj;
lean_object* v_a_2623_ = stack[1].m_obj;
lean_object* v_a_2624_ = stack[2].m_obj;
lean_object* v_a_2625_ = stack[3].m_obj;
lean_object* v_a_2626_ = stack[4].m_obj;
lean_object* v_a_2627_ = stack[5].m_obj;
lean_object* v_a_2628_ = stack[6].m_obj;
lean_object* v_res_2631_;
v_res_2631_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows(v_liveVars_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
stack->m_obj
 = v_res_2631_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___boxed(lean_object* v_liveVars_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows(v_liveVars_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
return v_res_2640_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2656_; 
v___x_2644_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_2645_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_2644_, v_a_2641_);
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2656_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2656_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2650_ = lean_st_ref_take(v_a_2642_);
lean_dec(v___x_2650_);
v___x_2651_ = lean_box(0);
v___x_2652_ = lean_st_ref_put(v_a_2642_, v_a_2646_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2651_);
v___x_2654_ = v___x_2648_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2651_);
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
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2641_ = stack[0].m_obj;
lean_object* v_a_2642_ = stack[1].m_obj;
lean_object* v_res_2657_;
v_res_2657_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(v_a_2641_, v_a_2642_);
stack->m_obj
 = v_res_2657_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg___boxed(lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(v_a_2658_, v_a_2659_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
return v_res_2661_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2681_; 
v___x_2669_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_2670_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_2669_, v_a_2662_);
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2673_ = v___x_2670_;
v_isShared_2674_ = v_isSharedCheck_2681_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2681_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2675_ = lean_st_ref_take(v_a_2663_);
lean_dec(v___x_2675_);
v___x_2676_ = lean_box(0);
v___x_2677_ = lean_st_ref_put(v_a_2663_, v_a_2671_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2676_);
v___x_2679_ = v___x_2673_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2676_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2662_ = stack[0].m_obj;
lean_object* v_a_2663_ = stack[1].m_obj;
lean_object* v_a_2664_ = stack[2].m_obj;
lean_object* v_a_2665_ = stack[3].m_obj;
lean_object* v_a_2666_ = stack[4].m_obj;
lean_object* v_a_2667_ = stack[5].m_obj;
lean_object* v_res_2682_;
v_res_2682_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
stack->m_obj
 = v_res_2682_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___boxed(lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
return v_res_2690_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(lean_object* v_fvarId_2691_, lean_object* v_k_2692_, lean_object* v_n_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2696_ = lean_unsigned_to_nat(0u);
v___x_2697_ = lean_nat_dec_eq(v_n_2693_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v_varMap_2698_; lean_object* v___f_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___y_2703_; uint8_t v_isDefiniteRef_2707_; 
v_varMap_2698_ = lean_ctor_get(v_a_2694_, 3);
v___f_2699_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_2700_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_fvarId_2691_);
lean_inc(v_varMap_2698_);
v___x_2701_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_2699_, v___x_2700_, v_varMap_2698_, v_fvarId_2691_);
v_isDefiniteRef_2707_ = lean_ctor_get_uint8(v___x_2701_, sizeof(void*)*2 + 1);
if (v_isDefiniteRef_2707_ == 0)
{
uint8_t v___x_2708_; 
v___x_2708_ = 1;
v___y_2703_ = v___x_2708_;
goto v___jp_2702_;
}
else
{
v___y_2703_ = v___x_2697_;
goto v___jp_2702_;
}
v___jp_2702_:
{
uint8_t v_persistent_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v_persistent_2704_ = lean_ctor_get_uint8(v___x_2701_, sizeof(void*)*2 + 2);
lean_dec(v___x_2701_);
v___x_2705_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_2705_, 0, v_fvarId_2691_);
lean_ctor_set(v___x_2705_, 1, v_n_2693_);
lean_ctor_set(v___x_2705_, 2, v_k_2692_);
lean_ctor_set_uint8(v___x_2705_, sizeof(void*)*3, v___y_2703_);
lean_ctor_set_uint8(v___x_2705_, sizeof(void*)*3 + 1, v_persistent_2704_);
v___x_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
return v___x_2706_;
}
}
else
{
lean_object* v___x_2709_; 
lean_dec(v_n_2693_);
lean_dec(v_fvarId_2691_);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v_k_2692_);
return v___x_2709_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2691_ = stack[0].m_obj;
lean_object* v_k_2692_ = stack[1].m_obj;
lean_object* v_n_2693_ = stack[2].m_obj;
lean_object* v_a_2694_ = stack[3].m_obj;
lean_object* v_res_2710_;
v_res_2710_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(v_fvarId_2691_, v_k_2692_, v_n_2693_, v_a_2694_);
stack->m_obj
 = v_res_2710_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg___boxed(lean_object* v_fvarId_2711_, lean_object* v_k_2712_, lean_object* v_n_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(v_fvarId_2711_, v_k_2712_, v_n_2713_, v_a_2714_);
lean_dec_ref(v_a_2714_);
return v_res_2716_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(lean_object* v_fvarId_2717_, lean_object* v_k_2718_, lean_object* v_n_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2727_ = lean_unsigned_to_nat(0u);
v___x_2728_ = lean_nat_dec_eq(v_n_2719_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_object* v_varMap_2729_; lean_object* v___f_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___y_2734_; uint8_t v_isDefiniteRef_2738_; 
v_varMap_2729_ = lean_ctor_get(v_a_2720_, 3);
v___f_2730_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_2731_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_fvarId_2717_);
lean_inc(v_varMap_2729_);
v___x_2732_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_2730_, v___x_2731_, v_varMap_2729_, v_fvarId_2717_);
v_isDefiniteRef_2738_ = lean_ctor_get_uint8(v___x_2732_, sizeof(void*)*2 + 1);
if (v_isDefiniteRef_2738_ == 0)
{
uint8_t v___x_2739_; 
v___x_2739_ = 1;
v___y_2734_ = v___x_2739_;
goto v___jp_2733_;
}
else
{
v___y_2734_ = v___x_2728_;
goto v___jp_2733_;
}
v___jp_2733_:
{
uint8_t v_persistent_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v_persistent_2735_ = lean_ctor_get_uint8(v___x_2732_, sizeof(void*)*2 + 2);
lean_dec(v___x_2732_);
v___x_2736_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_2736_, 0, v_fvarId_2717_);
lean_ctor_set(v___x_2736_, 1, v_n_2719_);
lean_ctor_set(v___x_2736_, 2, v_k_2718_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*3, v___y_2734_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*3 + 1, v_persistent_2735_);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
return v___x_2737_;
}
}
else
{
lean_object* v___x_2740_; 
lean_dec(v_n_2719_);
lean_dec(v_fvarId_2717_);
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v_k_2718_);
return v___x_2740_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2717_ = stack[0].m_obj;
lean_object* v_k_2718_ = stack[1].m_obj;
lean_object* v_n_2719_ = stack[2].m_obj;
lean_object* v_a_2720_ = stack[3].m_obj;
lean_object* v_a_2721_ = stack[4].m_obj;
lean_object* v_a_2722_ = stack[5].m_obj;
lean_object* v_a_2723_ = stack[6].m_obj;
lean_object* v_a_2724_ = stack[7].m_obj;
lean_object* v_a_2725_ = stack[8].m_obj;
lean_object* v_res_2741_;
v_res_2741_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(v_fvarId_2717_, v_k_2718_, v_n_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
stack->m_obj
 = v_res_2741_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___boxed(lean_object* v_fvarId_2742_, lean_object* v_k_2743_, lean_object* v_n_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(v_fvarId_2742_, v_k_2743_, v_n_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0_spec__0(lean_object* v_msg_2753_){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_2755_ = lean_panic_fn_borrowed(v___x_2754_, v_msg_2753_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(lean_object* v_t_2756_, lean_object* v_k_2757_){
_start:
{
if (lean_obj_tag(v_t_2756_) == 0)
{
lean_object* v_k_2758_; lean_object* v_v_2759_; lean_object* v_l_2760_; lean_object* v_r_2761_; uint8_t v___x_2762_; 
v_k_2758_ = lean_ctor_get(v_t_2756_, 1);
v_v_2759_ = lean_ctor_get(v_t_2756_, 2);
v_l_2760_ = lean_ctor_get(v_t_2756_, 3);
v_r_2761_ = lean_ctor_get(v_t_2756_, 4);
v___x_2762_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2757_, v_k_2758_);
switch(v___x_2762_)
{
case 0:
{
v_t_2756_ = v_l_2760_;
goto _start;
}
case 1:
{
lean_inc(v_v_2759_);
return v_v_2759_;
}
default: 
{
v_t_2756_ = v_r_2761_;
goto _start;
}
}
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3);
v___x_2766_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0_spec__0(v___x_2765_);
return v___x_2766_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0___boxed(lean_object* v_t_2767_, lean_object* v_k_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_t_2767_, v_k_2768_);
lean_dec(v_k_2768_);
lean_dec(v_t_2767_);
return v_res_2769_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(lean_object* v_fvarId_2770_, lean_object* v_k_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_varMap_2774_; lean_object* v___x_2775_; lean_object* v_ctorInfo_2776_; 
v_varMap_2774_ = lean_ctor_get(v_a_2772_, 3);
v___x_2775_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_2774_, v_fvarId_2770_);
v_ctorInfo_2776_ = lean_ctor_get(v___x_2775_, 1);
lean_inc(v_ctorInfo_2776_);
if (lean_obj_tag(v_ctorInfo_2776_) == 0)
{
uint8_t v_isDefiniteRef_2777_; uint8_t v_persistent_2778_; lean_object* v___x_2779_; uint8_t v___y_2781_; 
v_isDefiniteRef_2777_ = lean_ctor_get_uint8(v___x_2775_, sizeof(void*)*2 + 1);
v_persistent_2778_ = lean_ctor_get_uint8(v___x_2775_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_2775_);
v___x_2779_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_2777_ == 0)
{
uint8_t v___x_2785_; 
v___x_2785_ = 1;
v___y_2781_ = v___x_2785_;
goto v___jp_2780_;
}
else
{
uint8_t v___x_2786_; 
v___x_2786_ = 0;
v___y_2781_ = v___x_2786_;
goto v___jp_2780_;
}
v___jp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2782_ = lean_box(0);
v___x_2783_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_2783_, 0, v_fvarId_2770_);
lean_ctor_set(v___x_2783_, 1, v___x_2779_);
lean_ctor_set(v___x_2783_, 2, v___x_2782_);
lean_ctor_set(v___x_2783_, 3, v_k_2771_);
lean_ctor_set_uint8(v___x_2783_, sizeof(void*)*4, v___y_2781_);
lean_ctor_set_uint8(v___x_2783_, sizeof(void*)*4 + 1, v_persistent_2778_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
return v___x_2784_;
}
}
else
{
uint8_t v_persistent_2787_; lean_object* v_val_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2802_; 
v_persistent_2787_ = lean_ctor_get_uint8(v___x_2775_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_2775_);
v_val_2788_ = lean_ctor_get(v_ctorInfo_2776_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_ctorInfo_2776_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2790_ = v_ctorInfo_2776_;
v_isShared_2791_ = v_isSharedCheck_2802_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_val_2788_);
lean_dec(v_ctorInfo_2776_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2802_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
uint8_t v___x_2792_; 
v___x_2792_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_val_2788_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; 
lean_del_object(v___x_2790_);
lean_dec(v_val_2788_);
lean_dec(v_fvarId_2770_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v_k_2771_);
return v___x_2793_;
}
else
{
lean_object* v_size_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; lean_object* v___x_2798_; 
v_size_2794_ = lean_ctor_get(v_val_2788_, 2);
lean_inc(v_size_2794_);
lean_dec(v_val_2788_);
v___x_2795_ = lean_unsigned_to_nat(1u);
v___x_2796_ = 0;
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v_size_2794_);
v___x_2798_ = v___x_2790_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_size_2794_);
v___x_2798_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_2799_, 0, v_fvarId_2770_);
lean_ctor_set(v___x_2799_, 1, v___x_2795_);
lean_ctor_set(v___x_2799_, 2, v___x_2798_);
lean_ctor_set(v___x_2799_, 3, v_k_2771_);
lean_ctor_set_uint8(v___x_2799_, sizeof(void*)*4, v___x_2796_);
lean_ctor_set_uint8(v___x_2799_, sizeof(void*)*4 + 1, v_persistent_2787_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2770_ = stack[0].m_obj;
lean_object* v_k_2771_ = stack[1].m_obj;
lean_object* v_a_2772_ = stack[2].m_obj;
lean_object* v_res_2803_;
v_res_2803_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_2770_, v_k_2771_, v_a_2772_);
stack->m_obj
 = v_res_2803_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg___boxed(lean_object* v_fvarId_2804_, lean_object* v_k_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_2804_, v_k_2805_, v_a_2806_);
lean_dec_ref(v_a_2806_);
return v_res_2808_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(lean_object* v_fvarId_2809_, lean_object* v_k_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_2809_, v_k_2810_, v_a_2811_);
return v___x_2818_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2809_ = stack[0].m_obj;
lean_object* v_k_2810_ = stack[1].m_obj;
lean_object* v_a_2811_ = stack[2].m_obj;
lean_object* v_a_2812_ = stack[3].m_obj;
lean_object* v_a_2813_ = stack[4].m_obj;
lean_object* v_a_2814_ = stack[5].m_obj;
lean_object* v_a_2815_ = stack[6].m_obj;
lean_object* v_a_2816_ = stack[7].m_obj;
lean_object* v_res_2819_;
v_res_2819_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(v_fvarId_2809_, v_k_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_);
stack->m_obj
 = v_res_2819_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___boxed(lean_object* v_fvarId_2820_, lean_object* v_k_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(v_fvarId_2820_, v_k_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
return v_res_2829_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(lean_object* v_x_2830_, lean_object* v_x_2831_){
_start:
{
lean_object* v_snd_2832_; lean_object* v_snd_2833_; uint8_t v___x_2834_; 
v_snd_2832_ = lean_ctor_get(v_x_2830_, 1);
v_snd_2833_ = lean_ctor_get(v_x_2831_, 1);
v___x_2834_ = lean_nat_dec_lt(v_snd_2832_, v_snd_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2830_ = stack[0].m_obj;
lean_object* v_x_2831_ = stack[1].m_obj;
uint8_t v_res_2835_;
v_res_2835_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v_x_2830_, v_x_2831_);
stack->m_num = v_res_2835_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0___boxed(lean_object* v_x_2836_, lean_object* v_x_2837_){
_start:
{
uint8_t v_res_2838_; lean_object* v_r_2839_; 
v_res_2838_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v_x_2836_, v_x_2837_);
lean_dec_ref(v_x_2837_);
lean_dec_ref(v_x_2836_);
v_r_2839_ = lean_box(v_res_2838_);
return v_r_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(lean_object* v_hi_2840_, lean_object* v_pivot_2841_, lean_object* v_as_2842_, lean_object* v_i_2843_, lean_object* v_k_2844_){
_start:
{
uint8_t v___x_2845_; 
v___x_2845_ = lean_nat_dec_lt(v_k_2844_, v_hi_2840_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_dec(v_k_2844_);
v___x_2846_ = lean_array_fswap(v_as_2842_, v_i_2843_, v_hi_2840_);
v___x_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2847_, 0, v_i_2843_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
return v___x_2847_;
}
else
{
lean_object* v___x_2848_; lean_object* v_snd_2849_; lean_object* v_snd_2850_; uint8_t v___x_2851_; 
v___x_2848_ = lean_array_fget_borrowed(v_as_2842_, v_k_2844_);
v_snd_2849_ = lean_ctor_get(v___x_2848_, 1);
v_snd_2850_ = lean_ctor_get(v_pivot_2841_, 1);
v___x_2851_ = lean_nat_dec_lt(v_snd_2849_, v_snd_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_unsigned_to_nat(1u);
v___x_2853_ = lean_nat_add(v_k_2844_, v___x_2852_);
lean_dec(v_k_2844_);
v_k_2844_ = v___x_2853_;
goto _start;
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2855_ = lean_array_fswap(v_as_2842_, v_i_2843_, v_k_2844_);
v___x_2856_ = lean_unsigned_to_nat(1u);
v___x_2857_ = lean_nat_add(v_i_2843_, v___x_2856_);
lean_dec(v_i_2843_);
v___x_2858_ = lean_nat_add(v_k_2844_, v___x_2856_);
lean_dec(v_k_2844_);
v_as_2842_ = v___x_2855_;
v_i_2843_ = v___x_2857_;
v_k_2844_ = v___x_2858_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg___boxed(lean_object* v_hi_2860_, lean_object* v_pivot_2861_, lean_object* v_as_2862_, lean_object* v_i_2863_, lean_object* v_k_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(v_hi_2860_, v_pivot_2861_, v_as_2862_, v_i_2863_, v_k_2864_);
lean_dec_ref(v_pivot_2861_);
lean_dec(v_hi_2860_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(lean_object* v_n_2866_, lean_object* v_as_2867_, lean_object* v_lo_2868_, lean_object* v_hi_2869_){
_start:
{
lean_object* v___y_2871_; uint8_t v___x_2881_; 
v___x_2881_ = lean_nat_dec_lt(v_lo_2868_, v_hi_2869_);
if (v___x_2881_ == 0)
{
lean_dec(v_lo_2868_);
return v_as_2867_;
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v_mid_2884_; lean_object* v___y_2886_; lean_object* v___y_2892_; lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v___x_2882_ = lean_nat_add(v_lo_2868_, v_hi_2869_);
v___x_2883_ = lean_unsigned_to_nat(1u);
v_mid_2884_ = lean_nat_shiftr(v___x_2882_, v___x_2883_);
lean_dec(v___x_2882_);
v___x_2897_ = lean_array_fget_borrowed(v_as_2867_, v_mid_2884_);
v___x_2898_ = lean_array_fget_borrowed(v_as_2867_, v_lo_2868_);
v___x_2899_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v___x_2897_, v___x_2898_);
if (v___x_2899_ == 0)
{
v___y_2892_ = v_as_2867_;
goto v___jp_2891_;
}
else
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_array_fswap(v_as_2867_, v_lo_2868_, v_mid_2884_);
v___y_2892_ = v___x_2900_;
goto v___jp_2891_;
}
v___jp_2885_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2887_ = lean_array_fget_borrowed(v___y_2886_, v_mid_2884_);
v___x_2888_ = lean_array_fget_borrowed(v___y_2886_, v_hi_2869_);
v___x_2889_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v___x_2887_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_dec(v_mid_2884_);
v___y_2871_ = v___y_2886_;
goto v___jp_2870_;
}
else
{
lean_object* v___x_2890_; 
v___x_2890_ = lean_array_fswap(v___y_2886_, v_mid_2884_, v_hi_2869_);
lean_dec(v_mid_2884_);
v___y_2871_ = v___x_2890_;
goto v___jp_2870_;
}
}
v___jp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v___x_2893_ = lean_array_fget_borrowed(v___y_2892_, v_hi_2869_);
v___x_2894_ = lean_array_fget_borrowed(v___y_2892_, v_lo_2868_);
v___x_2895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v___x_2893_, v___x_2894_);
if (v___x_2895_ == 0)
{
v___y_2886_ = v___y_2892_;
goto v___jp_2885_;
}
else
{
lean_object* v___x_2896_; 
v___x_2896_ = lean_array_fswap(v___y_2892_, v_lo_2868_, v_hi_2869_);
v___y_2886_ = v___x_2896_;
goto v___jp_2885_;
}
}
}
v___jp_2870_:
{
lean_object* v_pivot_2872_; lean_object* v___x_2873_; lean_object* v_fst_2874_; lean_object* v_snd_2875_; uint8_t v___x_2876_; 
v_pivot_2872_ = lean_array_fget(v___y_2871_, v_hi_2869_);
lean_inc_n(v_lo_2868_, 2);
v___x_2873_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(v_hi_2869_, v_pivot_2872_, v___y_2871_, v_lo_2868_, v_lo_2868_);
lean_dec(v_pivot_2872_);
v_fst_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_fst_2874_);
v_snd_2875_ = lean_ctor_get(v___x_2873_, 1);
lean_inc(v_snd_2875_);
lean_dec_ref(v___x_2873_);
v___x_2876_ = lean_nat_dec_le(v_hi_2869_, v_fst_2874_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_n_2866_, v_snd_2875_, v_lo_2868_, v_fst_2874_);
v___x_2878_ = lean_unsigned_to_nat(1u);
v___x_2879_ = lean_nat_add(v_fst_2874_, v___x_2878_);
lean_dec(v_fst_2874_);
v_as_2867_ = v___x_2877_;
v_lo_2868_ = v___x_2879_;
goto _start;
}
else
{
lean_dec(v_fst_2874_);
lean_dec(v_lo_2868_);
return v_snd_2875_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___boxed(lean_object* v_n_2901_, lean_object* v_as_2902_, lean_object* v_lo_2903_, lean_object* v_hi_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_n_2901_, v_as_2902_, v_lo_2903_, v_hi_2904_);
lean_dec(v_hi_2904_);
lean_dec(v_n_2901_);
return v_res_2905_;
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(lean_object* v_altLiveVars_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
if (lean_obj_tag(v_a_2907_) == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_a_2908_);
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
return v___x_2913_;
}
else
{
lean_object* v_key_2914_; lean_object* v_tail_2915_; lean_object* v_fst_2916_; lean_object* v_snd_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2968_; 
v_key_2914_ = lean_ctor_get(v_a_2907_, 0);
v_tail_2915_ = lean_ctor_get(v_a_2907_, 2);
v_fst_2916_ = lean_ctor_get(v_a_2908_, 0);
v_snd_2917_ = lean_ctor_get(v_a_2908_, 1);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_a_2908_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2919_ = v_a_2908_;
v_isShared_2920_ = v_isSharedCheck_2968_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_snd_2917_);
lean_inc(v_fst_2916_);
lean_dec(v_a_2908_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2968_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v_varMap_2921_; lean_object* v_vars_2922_; lean_object* v_borrows_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v_varMap_2921_ = lean_ctor_get(v___y_2909_, 3);
v_vars_2922_ = lean_ctor_get(v_altLiveVars_2906_, 0);
v_borrows_2923_ = lean_ctor_get(v_altLiveVars_2906_, 1);
v___x_2924_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_2921_, v_key_2914_);
v___x_2925_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2922_, v_key_2914_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; uint8_t v_isPossibleRef_2932_; 
v___x_2926_ = lean_st_ref_get(v___y_2910_);
v_isPossibleRef_2932_ = lean_ctor_get_uint8(v___x_2924_, sizeof(void*)*2);
if (v_isPossibleRef_2932_ == 0)
{
lean_dec(v___x_2926_);
lean_dec_ref(v___x_2924_);
goto v___jp_2927_;
}
else
{
lean_object* v_idx_2933_; lean_object* v_borrows_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2945_; 
v_idx_2933_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_idx_2933_);
lean_dec_ref(v___x_2924_);
v_borrows_2934_ = lean_ctor_get(v___x_2926_, 1);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2945_ == 0)
{
lean_object* v_unused_2946_; 
v_unused_2946_ = lean_ctor_get(v___x_2926_, 0);
lean_dec(v_unused_2946_);
v___x_2936_ = v___x_2926_;
v_isShared_2937_ = v_isSharedCheck_2945_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_borrows_2934_);
lean_dec(v___x_2926_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2945_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
uint8_t v___x_2938_; 
v___x_2938_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_2934_, v_key_2914_);
lean_dec_ref(v_borrows_2934_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2940_; 
lean_del_object(v___x_2919_);
lean_inc(v_key_2914_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 1, v_idx_2933_);
lean_ctor_set(v___x_2936_, 0, v_key_2914_);
v___x_2940_ = v___x_2936_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_key_2914_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_idx_2933_);
v___x_2940_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = lean_array_push(v_snd_2917_, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v_fst_2916_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v_a_2907_ = v_tail_2915_;
v_a_2908_ = v___x_2942_;
goto _start;
}
}
else
{
lean_del_object(v___x_2936_);
lean_dec(v_idx_2933_);
goto v___jp_2927_;
}
}
}
v___jp_2927_:
{
lean_object* v___x_2929_; 
if (v_isShared_2920_ == 0)
{
v___x_2929_ = v___x_2919_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_fst_2916_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_snd_2917_);
v___x_2929_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
v_a_2907_ = v_tail_2915_;
v_a_2908_ = v___x_2929_;
goto _start;
}
}
}
else
{
lean_object* v___x_2947_; lean_object* v_borrows_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2966_; 
v___x_2947_ = lean_st_ref_get(v___y_2910_);
v_borrows_2953_ = lean_ctor_get(v___x_2947_, 1);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2966_ == 0)
{
lean_object* v_unused_2967_; 
v_unused_2967_ = lean_ctor_get(v___x_2947_, 0);
lean_dec(v_unused_2967_);
v___x_2955_ = v___x_2947_;
v_isShared_2956_ = v_isSharedCheck_2966_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_borrows_2953_);
lean_dec(v___x_2947_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2966_;
goto v_resetjp_2954_;
}
v___jp_2948_:
{
lean_object* v___x_2950_; 
if (v_isShared_2920_ == 0)
{
v___x_2950_ = v___x_2919_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_fst_2916_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_snd_2917_);
v___x_2950_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
v_a_2907_ = v_tail_2915_;
v_a_2908_ = v___x_2950_;
goto _start;
}
}
v_resetjp_2954_:
{
uint8_t v___x_2957_; 
v___x_2957_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_2953_, v_key_2914_);
lean_dec_ref(v_borrows_2953_);
if (v___x_2957_ == 0)
{
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2924_);
goto v___jp_2948_;
}
else
{
uint8_t v___x_2958_; 
v___x_2958_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_2923_, v_key_2914_);
if (v___x_2958_ == 0)
{
if (v___x_2957_ == 0)
{
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2924_);
goto v___jp_2948_;
}
else
{
lean_object* v_idx_2959_; lean_object* v___x_2961_; 
lean_del_object(v___x_2919_);
v_idx_2959_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_idx_2959_);
lean_dec_ref(v___x_2924_);
lean_inc(v_key_2914_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v_idx_2959_);
lean_ctor_set(v___x_2955_, 0, v_key_2914_);
v___x_2961_ = v___x_2955_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_key_2914_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_idx_2959_);
v___x_2961_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_array_push(v_fst_2916_, v___x_2961_);
v___x_2963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
lean_ctor_set(v___x_2963_, 1, v_snd_2917_);
v_a_2907_ = v_tail_2915_;
v_a_2908_ = v___x_2963_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2924_);
goto v___jp_2948_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_altLiveVars_2906_ = stack[0].m_obj;
lean_object* v_a_2907_ = stack[1].m_obj;
lean_object* v_a_2908_ = stack[2].m_obj;
lean_object* v___y_2909_ = stack[3].m_obj;
lean_object* v___y_2910_ = stack[4].m_obj;
lean_object* v_res_2969_;
v_res_2969_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_2906_, v_a_2907_, v_a_2908_, v___y_2909_, v___y_2910_);
stack->m_obj
 = v_res_2969_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___boxed(lean_object* v_altLiveVars_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_2970_, v_a_2971_, v_a_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v_a_2971_);
lean_dec_ref(v_altLiveVars_2970_);
return v_res_2976_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(lean_object* v_altLiveVars_2977_, lean_object* v_as_2978_, size_t v_sz_2979_, size_t v_i_2980_, lean_object* v_b_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
uint8_t v___x_2989_; 
v___x_2989_ = lean_usize_dec_lt(v_i_2980_, v_sz_2979_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2990_, 0, v_b_2981_);
return v___x_2990_;
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2992_; 
v_a_2991_ = lean_array_uget_borrowed(v_as_2978_, v_i_2980_);
v___x_2992_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_2977_, v_a_2991_, v_b_2981_, v___y_2982_, v___y_2983_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3005_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3005_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3005_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
if (lean_obj_tag(v_a_2993_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2999_; 
v_a_2997_ = lean_ctor_get(v_a_2993_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v_a_2993_, 1);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v_a_2997_);
v___x_2999_ = v___x_2995_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2997_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
else
{
lean_object* v_a_3001_; size_t v___x_3002_; size_t v___x_3003_; 
lean_del_object(v___x_2995_);
v_a_3001_ = lean_ctor_get(v_a_2993_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v_a_2993_, 1);
v___x_3002_ = ((size_t)1ULL);
v___x_3003_ = lean_usize_add(v_i_2980_, v___x_3002_);
v_i_2980_ = v___x_3003_;
v_b_2981_ = v_a_3001_;
goto _start;
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
v_a_3006_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2992_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2992_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_altLiveVars_2977_ = stack[0].m_obj;
lean_object* v_as_2978_ = stack[1].m_obj;
size_t v_sz_2979_ = stack[2].m_num;
size_t v_i_2980_ = stack[3].m_num;
lean_object* v_b_2981_ = stack[4].m_obj;
lean_object* v___y_2982_ = stack[5].m_obj;
lean_object* v___y_2983_ = stack[6].m_obj;
lean_object* v___y_2984_ = stack[7].m_obj;
lean_object* v___y_2985_ = stack[8].m_obj;
lean_object* v___y_2986_ = stack[9].m_obj;
lean_object* v___y_2987_ = stack[10].m_obj;
lean_object* v_res_3014_;
v_res_3014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(v_altLiveVars_2977_, v_as_2978_, v_sz_2979_, v_i_2980_, v_b_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
stack->m_obj
 = v_res_3014_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___boxed(lean_object* v_altLiveVars_3015_, lean_object* v_as_3016_, lean_object* v_sz_3017_, lean_object* v_i_3018_, lean_object* v_b_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
size_t v_sz_boxed_3027_; size_t v_i_boxed_3028_; lean_object* v_res_3029_; 
v_sz_boxed_3027_ = lean_unbox_usize(v_sz_3017_);
lean_dec(v_sz_3017_);
v_i_boxed_3028_ = lean_unbox_usize(v_i_3018_);
lean_dec(v_i_3018_);
v_res_3029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(v_altLiveVars_3015_, v_as_3016_, v_sz_boxed_3027_, v_i_boxed_3028_, v_b_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec_ref(v_as_3016_);
lean_dec_ref(v_altLiveVars_3015_);
return v_res_3029_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(lean_object* v_as_3030_, size_t v_i_3031_, size_t v_stop_3032_, lean_object* v_b_3033_, lean_object* v___y_3034_){
_start:
{
uint8_t v___x_3036_; 
v___x_3036_ = lean_usize_dec_eq(v_i_3031_, v_stop_3032_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v_fst_3038_; lean_object* v___x_3039_; 
v___x_3037_ = lean_array_uget_borrowed(v_as_3030_, v_i_3031_);
v_fst_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_fst_3038_);
v___x_3039_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fst_3038_, v_b_3033_, v___y_3034_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; size_t v___x_3041_; size_t v___x_3042_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref_known(v___x_3039_, 1);
v___x_3041_ = ((size_t)1ULL);
v___x_3042_ = lean_usize_add(v_i_3031_, v___x_3041_);
v_i_3031_ = v___x_3042_;
v_b_3033_ = v_a_3040_;
goto _start;
}
else
{
return v___x_3039_;
}
}
else
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3044_, 0, v_b_3033_);
return v___x_3044_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3030_ = stack[0].m_obj;
size_t v_i_3031_ = stack[1].m_num;
size_t v_stop_3032_ = stack[2].m_num;
lean_object* v_b_3033_ = stack[3].m_obj;
lean_object* v___y_3034_ = stack[4].m_obj;
lean_object* v_res_3045_;
v_res_3045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_as_3030_, v_i_3031_, v_stop_3032_, v_b_3033_, v___y_3034_);
stack->m_obj
 = v_res_3045_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___boxed(lean_object* v_as_3046_, lean_object* v_i_3047_, lean_object* v_stop_3048_, lean_object* v_b_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
size_t v_i_boxed_3052_; size_t v_stop_boxed_3053_; lean_object* v_res_3054_; 
v_i_boxed_3052_ = lean_unbox_usize(v_i_3047_);
lean_dec(v_i_3047_);
v_stop_boxed_3053_ = lean_unbox_usize(v_stop_3048_);
lean_dec(v_stop_3048_);
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_as_3046_, v_i_boxed_3052_, v_stop_boxed_3053_, v_b_3049_, v___y_3050_);
lean_dec_ref(v___y_3050_);
lean_dec_ref(v_as_3046_);
return v_res_3054_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(lean_object* v_as_3055_, size_t v_i_3056_, size_t v_stop_3057_, lean_object* v_b_3058_, lean_object* v___y_3059_){
_start:
{
uint8_t v___x_3061_; 
v___x_3061_ = lean_usize_dec_eq(v_i_3056_, v_stop_3057_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; lean_object* v_fst_3063_; lean_object* v_varMap_3064_; lean_object* v___x_3065_; uint8_t v_isDefiniteRef_3066_; lean_object* v___x_3067_; uint8_t v___y_3069_; 
v___x_3062_ = lean_array_uget_borrowed(v_as_3055_, v_i_3056_);
v_fst_3063_ = lean_ctor_get(v___x_3062_, 0);
v_varMap_3064_ = lean_ctor_get(v___y_3059_, 3);
v___x_3065_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3064_, v_fst_3063_);
v_isDefiniteRef_3066_ = lean_ctor_get_uint8(v___x_3065_, sizeof(void*)*2 + 1);
v___x_3067_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_3066_ == 0)
{
uint8_t v___x_3075_; 
v___x_3075_ = 1;
v___y_3069_ = v___x_3075_;
goto v___jp_3068_;
}
else
{
v___y_3069_ = v___x_3061_;
goto v___jp_3068_;
}
v___jp_3068_:
{
uint8_t v_persistent_3070_; lean_object* v___x_3071_; size_t v___x_3072_; size_t v___x_3073_; 
v_persistent_3070_ = lean_ctor_get_uint8(v___x_3065_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_3065_);
lean_inc(v_fst_3063_);
v___x_3071_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_3071_, 0, v_fst_3063_);
lean_ctor_set(v___x_3071_, 1, v___x_3067_);
lean_ctor_set(v___x_3071_, 2, v_b_3058_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*3, v___y_3069_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*3 + 1, v_persistent_3070_);
v___x_3072_ = ((size_t)1ULL);
v___x_3073_ = lean_usize_add(v_i_3056_, v___x_3072_);
v_i_3056_ = v___x_3073_;
v_b_3058_ = v___x_3071_;
goto _start;
}
}
else
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_b_3058_);
return v___x_3076_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3055_ = stack[0].m_obj;
size_t v_i_3056_ = stack[1].m_num;
size_t v_stop_3057_ = stack[2].m_num;
lean_object* v_b_3058_ = stack[3].m_obj;
lean_object* v___y_3059_ = stack[4].m_obj;
lean_object* v_res_3077_;
v_res_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v_as_3055_, v_i_3056_, v_stop_3057_, v_b_3058_, v___y_3059_);
stack->m_obj
 = v_res_3077_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg___boxed(lean_object* v_as_3078_, lean_object* v_i_3079_, lean_object* v_stop_3080_, lean_object* v_b_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
size_t v_i_boxed_3084_; size_t v_stop_boxed_3085_; lean_object* v_res_3086_; 
v_i_boxed_3084_ = lean_unbox_usize(v_i_3079_);
lean_dec(v_i_3079_);
v_stop_boxed_3085_ = lean_unbox_usize(v_stop_3080_);
lean_dec(v_stop_3080_);
v_res_3086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v_as_3078_, v_i_boxed_3084_, v_stop_boxed_3085_, v_b_3081_, v___y_3082_);
lean_dec_ref(v___y_3082_);
lean_dec_ref(v_as_3078_);
return v_res_3086_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(lean_object* v_altLiveVars_3091_, lean_object* v_k_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v_vars_3102_; lean_object* v___x_3103_; lean_object* v_buckets_3104_; size_t v_sz_3105_; size_t v___x_3106_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___x_3118_; 
v___x_3100_ = lean_unsigned_to_nat(0u);
v___x_3101_ = lean_st_ref_get(v_a_3094_);
v_vars_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc_ref(v_vars_3102_);
lean_dec(v___x_3101_);
v___x_3103_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1));
v_buckets_3104_ = lean_ctor_get(v_vars_3102_, 1);
lean_inc_ref(v_buckets_3104_);
lean_dec_ref(v_vars_3102_);
v_sz_3105_ = lean_array_size(v_buckets_3104_);
v___x_3106_ = ((size_t)0ULL);
v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(v_altLiveVars_3091_, v_buckets_3104_, v_sz_3105_, v___x_3106_, v___x_3103_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
lean_dec_ref(v_buckets_3104_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3176_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3176_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3176_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v_fst_3123_; lean_object* v_snd_3124_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___x_3139_; lean_object* v___y_3141_; lean_object* v_a_3142_; lean_object* v___y_3148_; lean_object* v___y_3151_; lean_object* v___x_3165_; lean_object* v___y_3167_; lean_object* v___y_3168_; uint8_t v___x_3170_; 
v_fst_3123_ = lean_ctor_get(v_a_3119_, 0);
lean_inc(v_fst_3123_);
v_snd_3124_ = lean_ctor_get(v_a_3119_, 1);
lean_inc(v_snd_3124_);
lean_dec(v_a_3119_);
v___x_3139_ = lean_unsigned_to_nat(1u);
v___x_3165_ = lean_array_get_size(v_snd_3124_);
v___x_3170_ = lean_nat_dec_eq(v___x_3165_, v___x_3100_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3171_; lean_object* v___y_3173_; uint8_t v___x_3175_; 
v___x_3171_ = lean_nat_sub(v___x_3165_, v___x_3139_);
v___x_3175_ = lean_nat_dec_le(v___x_3100_, v___x_3171_);
if (v___x_3175_ == 0)
{
lean_inc(v___x_3171_);
v___y_3173_ = v___x_3171_;
goto v___jp_3172_;
}
else
{
v___y_3173_ = v___x_3100_;
goto v___jp_3172_;
}
v___jp_3172_:
{
uint8_t v___x_3174_; 
v___x_3174_ = lean_nat_dec_le(v___y_3173_, v___x_3171_);
if (v___x_3174_ == 0)
{
lean_dec(v___x_3171_);
lean_inc(v___y_3173_);
v___y_3167_ = v___y_3173_;
v___y_3168_ = v___y_3173_;
goto v___jp_3166_;
}
else
{
v___y_3167_ = v___y_3173_;
v___y_3168_ = v___x_3171_;
goto v___jp_3166_;
}
}
}
else
{
v___y_3151_ = v_snd_3124_;
goto v___jp_3150_;
}
v___jp_3125_:
{
lean_object* v___x_3131_; 
v___x_3131_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v___y_3129_, v_fst_3123_, v___y_3128_, v___y_3130_);
lean_dec(v___y_3130_);
lean_dec(v___y_3129_);
v___y_3108_ = v___y_3126_;
v___y_3109_ = v___y_3127_;
v___y_3110_ = v___x_3131_;
goto v___jp_3107_;
}
v___jp_3132_:
{
uint8_t v___x_3138_; 
v___x_3138_ = lean_nat_dec_le(v___y_3137_, v___y_3136_);
if (v___x_3138_ == 0)
{
lean_dec(v___y_3136_);
lean_inc(v___y_3137_);
v___y_3126_ = v___y_3133_;
v___y_3127_ = v___y_3134_;
v___y_3128_ = v___y_3137_;
v___y_3129_ = v___y_3135_;
v___y_3130_ = v___y_3137_;
goto v___jp_3125_;
}
else
{
v___y_3126_ = v___y_3133_;
v___y_3127_ = v___y_3134_;
v___y_3128_ = v___y_3137_;
v___y_3129_ = v___y_3135_;
v___y_3130_ = v___y_3136_;
goto v___jp_3125_;
}
}
v___jp_3140_:
{
lean_object* v___x_3143_; uint8_t v___x_3144_; 
v___x_3143_ = lean_array_get_size(v_fst_3123_);
v___x_3144_ = lean_nat_dec_eq(v___x_3143_, v___x_3100_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3145_ = lean_nat_sub(v___x_3143_, v___x_3139_);
v___x_3146_ = lean_nat_dec_le(v___x_3100_, v___x_3145_);
if (v___x_3146_ == 0)
{
lean_inc(v___x_3145_);
v___y_3133_ = v___y_3141_;
v___y_3134_ = v_a_3142_;
v___y_3135_ = v___x_3143_;
v___y_3136_ = v___x_3145_;
v___y_3137_ = v___x_3145_;
goto v___jp_3132_;
}
else
{
v___y_3133_ = v___y_3141_;
v___y_3134_ = v_a_3142_;
v___y_3135_ = v___x_3143_;
v___y_3136_ = v___x_3145_;
v___y_3137_ = v___x_3100_;
goto v___jp_3132_;
}
}
else
{
v___y_3108_ = v___y_3141_;
v___y_3109_ = v_a_3142_;
v___y_3110_ = v_fst_3123_;
goto v___jp_3107_;
}
}
v___jp_3147_:
{
if (lean_obj_tag(v___y_3148_) == 0)
{
lean_object* v_a_3149_; 
v_a_3149_ = lean_ctor_get(v___y_3148_, 0);
lean_inc(v_a_3149_);
v___y_3141_ = v___y_3148_;
v_a_3142_ = v_a_3149_;
goto v___jp_3140_;
}
else
{
lean_dec(v_fst_3123_);
return v___y_3148_;
}
}
v___jp_3150_:
{
lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3152_ = lean_array_get_size(v___y_3151_);
v___x_3153_ = lean_nat_dec_lt(v___x_3100_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3155_; 
lean_dec_ref(v___y_3151_);
lean_inc_ref(v_k_3092_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v_k_3092_);
v___x_3155_ = v___x_3121_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_k_3092_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
v___y_3141_ = v___x_3155_;
v_a_3142_ = v_k_3092_;
goto v___jp_3140_;
}
}
else
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_nat_dec_le(v___x_3152_, v___x_3152_);
if (v___x_3157_ == 0)
{
if (v___x_3153_ == 0)
{
lean_object* v___x_3159_; 
lean_dec_ref(v___y_3151_);
lean_inc_ref(v_k_3092_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v_k_3092_);
v___x_3159_ = v___x_3121_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_k_3092_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
v___y_3141_ = v___x_3159_;
v_a_3142_ = v_k_3092_;
goto v___jp_3140_;
}
}
else
{
size_t v___x_3161_; lean_object* v___x_3162_; 
lean_del_object(v___x_3121_);
v___x_3161_ = lean_usize_of_nat(v___x_3152_);
v___x_3162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v___y_3151_, v___x_3106_, v___x_3161_, v_k_3092_, v_a_3093_);
lean_dec_ref(v___y_3151_);
v___y_3148_ = v___x_3162_;
goto v___jp_3147_;
}
}
else
{
size_t v___x_3163_; lean_object* v___x_3164_; 
lean_del_object(v___x_3121_);
v___x_3163_ = lean_usize_of_nat(v___x_3152_);
v___x_3164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v___y_3151_, v___x_3106_, v___x_3163_, v_k_3092_, v_a_3093_);
lean_dec_ref(v___y_3151_);
v___y_3148_ = v___x_3164_;
goto v___jp_3147_;
}
}
}
v___jp_3166_:
{
lean_object* v___x_3169_; 
v___x_3169_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v___x_3165_, v_snd_3124_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
v___y_3151_ = v___x_3169_;
goto v___jp_3150_;
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec_ref(v_k_3092_);
v_a_3177_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3118_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3118_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
v___jp_3107_:
{
lean_object* v___x_3111_; uint8_t v___x_3112_; 
v___x_3111_ = lean_array_get_size(v___y_3110_);
v___x_3112_ = lean_nat_dec_lt(v___x_3100_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_dec_ref(v___y_3110_);
lean_dec_ref(v___y_3109_);
return v___y_3108_;
}
else
{
uint8_t v___x_3113_; 
v___x_3113_ = lean_nat_dec_le(v___x_3111_, v___x_3111_);
if (v___x_3113_ == 0)
{
if (v___x_3112_ == 0)
{
lean_dec_ref(v___y_3110_);
lean_dec_ref(v___y_3109_);
return v___y_3108_;
}
else
{
size_t v___x_3114_; lean_object* v___x_3115_; 
lean_dec_ref(v___y_3108_);
v___x_3114_ = lean_usize_of_nat(v___x_3111_);
v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v___y_3110_, v___x_3106_, v___x_3114_, v___y_3109_, v_a_3093_);
lean_dec_ref(v___y_3110_);
return v___x_3115_;
}
}
else
{
size_t v___x_3116_; lean_object* v___x_3117_; 
lean_dec_ref(v___y_3108_);
v___x_3116_ = lean_usize_of_nat(v___x_3111_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v___y_3110_, v___x_3106_, v___x_3116_, v___y_3109_, v_a_3093_);
lean_dec_ref(v___y_3110_);
return v___x_3117_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_0interp(lean_interpreter_value* stack)
{
lean_object* v_altLiveVars_3091_ = stack[0].m_obj;
lean_object* v_k_3092_ = stack[1].m_obj;
lean_object* v_a_3093_ = stack[2].m_obj;
lean_object* v_a_3094_ = stack[3].m_obj;
lean_object* v_a_3095_ = stack[4].m_obj;
lean_object* v_a_3096_ = stack[5].m_obj;
lean_object* v_a_3097_ = stack[6].m_obj;
lean_object* v_a_3098_ = stack[7].m_obj;
lean_object* v_res_3185_;
v_res_3185_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_altLiveVars_3091_, v_k_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
stack->m_obj
 = v_res_3185_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___boxed(lean_object* v_altLiveVars_3186_, lean_object* v_k_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_altLiveVars_3186_, v_k_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
lean_dec(v_a_3193_);
lean_dec_ref(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3188_);
lean_dec_ref(v_altLiveVars_3186_);
return v_res_3195_;
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(lean_object* v_altLiveVars_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_3196_, v_a_3197_, v_a_3198_, v___y_3199_, v___y_3200_);
return v___x_3206_;
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_altLiveVars_3196_ = stack[0].m_obj;
lean_object* v_a_3197_ = stack[1].m_obj;
lean_object* v_a_3198_ = stack[2].m_obj;
lean_object* v___y_3199_ = stack[3].m_obj;
lean_object* v___y_3200_ = stack[4].m_obj;
lean_object* v___y_3201_ = stack[5].m_obj;
lean_object* v___y_3202_ = stack[6].m_obj;
lean_object* v___y_3203_ = stack[7].m_obj;
lean_object* v___y_3204_ = stack[8].m_obj;
lean_object* v_res_3207_;
v_res_3207_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(v_altLiveVars_3196_, v_a_3197_, v_a_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
stack->m_obj
 = v_res_3207_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___boxed(lean_object* v_altLiveVars_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(v_altLiveVars_3208_, v_a_3209_, v_a_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v_a_3209_);
lean_dec_ref(v_altLiveVars_3208_);
return v_res_3218_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(lean_object* v_as_3219_, size_t v_i_3220_, size_t v_stop_3221_, lean_object* v_b_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v_as_3219_, v_i_3220_, v_stop_3221_, v_b_3222_, v___y_3223_);
return v___x_3230_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3219_ = stack[0].m_obj;
size_t v_i_3220_ = stack[1].m_num;
size_t v_stop_3221_ = stack[2].m_num;
lean_object* v_b_3222_ = stack[3].m_obj;
lean_object* v___y_3223_ = stack[4].m_obj;
lean_object* v___y_3224_ = stack[5].m_obj;
lean_object* v___y_3225_ = stack[6].m_obj;
lean_object* v___y_3226_ = stack[7].m_obj;
lean_object* v___y_3227_ = stack[8].m_obj;
lean_object* v___y_3228_ = stack[9].m_obj;
lean_object* v_res_3231_;
v_res_3231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(v_as_3219_, v_i_3220_, v_stop_3221_, v_b_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
stack->m_obj
 = v_res_3231_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___boxed(lean_object* v_as_3232_, lean_object* v_i_3233_, lean_object* v_stop_3234_, lean_object* v_b_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
size_t v_i_boxed_3243_; size_t v_stop_boxed_3244_; lean_object* v_res_3245_; 
v_i_boxed_3243_ = lean_unbox_usize(v_i_3233_);
lean_dec(v_i_3233_);
v_stop_boxed_3244_ = lean_unbox_usize(v_stop_3234_);
lean_dec(v_stop_3234_);
v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(v_as_3232_, v_i_boxed_3243_, v_stop_boxed_3244_, v_b_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec_ref(v_as_3232_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3(lean_object* v_n_3246_, lean_object* v_as_3247_, lean_object* v_lo_3248_, lean_object* v_hi_3249_, lean_object* v_w_3250_, lean_object* v_hlo_3251_, lean_object* v_hhi_3252_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_n_3246_, v_as_3247_, v_lo_3248_, v_hi_3249_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___boxed(lean_object* v_n_3254_, lean_object* v_as_3255_, lean_object* v_lo_3256_, lean_object* v_hi_3257_, lean_object* v_w_3258_, lean_object* v_hlo_3259_, lean_object* v_hhi_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3(v_n_3254_, v_as_3255_, v_lo_3256_, v_hi_3257_, v_w_3258_, v_hlo_3259_, v_hhi_3260_);
lean_dec(v_hi_3257_);
lean_dec(v_n_3254_);
return v_res_3261_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(lean_object* v_as_3262_, size_t v_i_3263_, size_t v_stop_3264_, lean_object* v_b_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_as_3262_, v_i_3263_, v_stop_3264_, v_b_3265_, v___y_3266_);
return v___x_3273_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3262_ = stack[0].m_obj;
size_t v_i_3263_ = stack[1].m_num;
size_t v_stop_3264_ = stack[2].m_num;
lean_object* v_b_3265_ = stack[3].m_obj;
lean_object* v___y_3266_ = stack[4].m_obj;
lean_object* v___y_3267_ = stack[5].m_obj;
lean_object* v___y_3268_ = stack[6].m_obj;
lean_object* v___y_3269_ = stack[7].m_obj;
lean_object* v___y_3270_ = stack[8].m_obj;
lean_object* v___y_3271_ = stack[9].m_obj;
lean_object* v_res_3274_;
v_res_3274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(v_as_3262_, v_i_3263_, v_stop_3264_, v_b_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
stack->m_obj
 = v_res_3274_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___boxed(lean_object* v_as_3275_, lean_object* v_i_3276_, lean_object* v_stop_3277_, lean_object* v_b_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
size_t v_i_boxed_3286_; size_t v_stop_boxed_3287_; lean_object* v_res_3288_; 
v_i_boxed_3286_ = lean_unbox_usize(v_i_3276_);
lean_dec(v_i_3276_);
v_stop_boxed_3287_ = lean_unbox_usize(v_stop_3277_);
lean_dec(v_stop_3277_);
v_res_3288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(v_as_3275_, v_i_boxed_3286_, v_stop_boxed_3287_, v_b_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec_ref(v_as_3275_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3(lean_object* v_n_3289_, lean_object* v_lo_3290_, lean_object* v_hi_3291_, lean_object* v_hhi_3292_, lean_object* v_pivot_3293_, lean_object* v_as_3294_, lean_object* v_i_3295_, lean_object* v_k_3296_, lean_object* v_ilo_3297_, lean_object* v_ik_3298_, lean_object* v_w_3299_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(v_hi_3291_, v_pivot_3293_, v_as_3294_, v_i_3295_, v_k_3296_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___boxed(lean_object* v_n_3301_, lean_object* v_lo_3302_, lean_object* v_hi_3303_, lean_object* v_hhi_3304_, lean_object* v_pivot_3305_, lean_object* v_as_3306_, lean_object* v_i_3307_, lean_object* v_k_3308_, lean_object* v_ilo_3309_, lean_object* v_ik_3310_, lean_object* v_w_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3(v_n_3301_, v_lo_3302_, v_hi_3303_, v_hhi_3304_, v_pivot_3305_, v_as_3306_, v_i_3307_, v_k_3308_, v_ilo_3309_, v_ik_3310_, v_w_3311_);
lean_dec_ref(v_pivot_3305_);
lean_dec(v_hi_3303_);
lean_dec(v_lo_3302_);
lean_dec(v_n_3301_);
return v_res_3312_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(lean_object* v_args_3313_, lean_object* v_x_3314_, lean_object* v_n_3315_, lean_object* v_i_3316_){
_start:
{
lean_object* v_zero_3317_; uint8_t v_isZero_3318_; 
v_zero_3317_ = lean_unsigned_to_nat(0u);
v_isZero_3318_ = lean_nat_dec_eq(v_i_3316_, v_zero_3317_);
if (v_isZero_3318_ == 1)
{
lean_dec(v_i_3316_);
return v_isZero_3318_;
}
else
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3319_ = lean_box(0);
v___x_3320_ = lean_nat_sub(v_n_3315_, v_i_3316_);
v___x_3321_ = lean_array_get_borrowed(v___x_3319_, v_args_3313_, v___x_3320_);
lean_dec(v___x_3320_);
v___x_3322_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_3321_, v_x_3314_);
if (v___x_3322_ == 0)
{
lean_object* v_one_3323_; lean_object* v_n_3324_; 
v_one_3323_ = lean_unsigned_to_nat(1u);
v_n_3324_ = lean_nat_sub(v_i_3316_, v_one_3323_);
lean_dec(v_i_3316_);
v_i_3316_ = v_n_3324_;
goto _start;
}
else
{
lean_dec(v_i_3316_);
return v_isZero_3318_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_3313_ = stack[0].m_obj;
lean_object* v_x_3314_ = stack[1].m_obj;
lean_object* v_n_3315_ = stack[2].m_obj;
lean_object* v_i_3316_ = stack[3].m_obj;
uint8_t v_res_3326_;
v_res_3326_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3313_, v_x_3314_, v_n_3315_, v_i_3316_);
stack->m_num = v_res_3326_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg___boxed(lean_object* v_args_3327_, lean_object* v_x_3328_, lean_object* v_n_3329_, lean_object* v_i_3330_){
_start:
{
uint8_t v_res_3331_; lean_object* v_r_3332_; 
v_res_3331_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3327_, v_x_3328_, v_n_3329_, v_i_3330_);
lean_dec(v_n_3329_);
lean_dec(v_x_3328_);
lean_dec_ref(v_args_3327_);
v_r_3332_ = lean_box(v_res_3331_);
return v_r_3332_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(lean_object* v_args_3333_, lean_object* v_i_3334_){
_start:
{
lean_object* v___x_3335_; lean_object* v_x_3336_; uint8_t v___x_3337_; 
v___x_3335_ = lean_box(0);
v_x_3336_ = lean_array_get_borrowed(v___x_3335_, v_args_3333_, v_i_3334_);
lean_inc(v_i_3334_);
v___x_3337_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3333_, v_x_3336_, v_i_3334_, v_i_3334_);
lean_dec(v_i_3334_);
return v___x_3337_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_3333_ = stack[0].m_obj;
lean_object* v_i_3334_ = stack[1].m_obj;
uint8_t v_res_3338_;
v_res_3338_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3333_, v_i_3334_);
stack->m_num = v_res_3338_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc___boxed(lean_object* v_args_3339_, lean_object* v_i_3340_){
_start:
{
uint8_t v_res_3341_; lean_object* v_r_3342_; 
v_res_3341_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3339_, v_i_3340_);
lean_dec_ref(v_args_3339_);
v_r_3342_ = lean_box(v_res_3341_);
return v_r_3342_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(lean_object* v_args_3343_, lean_object* v_x_3344_, lean_object* v_n_3345_, lean_object* v_i_3346_, lean_object* v_a_3347_){
_start:
{
uint8_t v___x_3348_; 
v___x_3348_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3343_, v_x_3344_, v_n_3345_, v_i_3346_);
return v___x_3348_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_3343_ = stack[0].m_obj;
lean_object* v_x_3344_ = stack[1].m_obj;
lean_object* v_n_3345_ = stack[2].m_obj;
lean_object* v_i_3346_ = stack[3].m_obj;
uint8_t v_res_3349_;
v_res_3349_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(v_args_3343_, v_x_3344_, v_n_3345_, v_i_3346_, lean_box(0));
stack->m_num = v_res_3349_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___boxed(lean_object* v_args_3350_, lean_object* v_x_3351_, lean_object* v_n_3352_, lean_object* v_i_3353_, lean_object* v_a_3354_){
_start:
{
uint8_t v_res_3355_; lean_object* v_r_3356_; 
v_res_3355_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(v_args_3350_, v_x_3351_, v_n_3352_, v_i_3353_, v_a_3354_);
lean_dec(v_n_3352_);
lean_dec(v_x_3351_);
lean_dec_ref(v_args_3350_);
v_r_3356_ = lean_box(v_res_3355_);
return v_r_3356_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(lean_object* v_args_3357_, lean_object* v_arg_3358_, lean_object* v_consumeParamPred_3359_, lean_object* v_n_3360_, lean_object* v_i_3361_){
_start:
{
lean_object* v_zero_3362_; uint8_t v_isZero_3363_; 
v_zero_3362_ = lean_unsigned_to_nat(0u);
v_isZero_3363_ = lean_nat_dec_eq(v_i_3361_, v_zero_3362_);
if (v_isZero_3363_ == 1)
{
uint8_t v___x_3364_; 
lean_dec(v_i_3361_);
lean_dec_ref(v_consumeParamPred_3359_);
v___x_3364_ = 0;
return v___x_3364_;
}
else
{
lean_object* v_one_3365_; lean_object* v_n_3366_; uint8_t v___y_3368_; lean_object* v___x_3370_; lean_object* v_arg_x27_3371_; 
v_one_3365_ = lean_unsigned_to_nat(1u);
v_n_3366_ = lean_nat_sub(v_i_3361_, v_one_3365_);
v___x_3370_ = lean_nat_sub(v_n_3360_, v_i_3361_);
lean_dec(v_i_3361_);
v_arg_x27_3371_ = lean_array_fget_borrowed(v_args_3357_, v___x_3370_);
if (lean_obj_tag(v_arg_x27_3371_) == 0)
{
lean_dec(v___x_3370_);
v_i_3361_ = v_n_3366_;
goto _start;
}
else
{
lean_object* v_fvarId_3373_; uint8_t v___x_3374_; 
v_fvarId_3373_ = lean_ctor_get(v_arg_x27_3371_, 0);
v___x_3374_ = l_Lean_instBEqFVarId_beq(v_arg_3358_, v_fvarId_3373_);
if (v___x_3374_ == 0)
{
lean_dec(v___x_3370_);
v___y_3368_ = v___x_3374_;
goto v___jp_3367_;
}
else
{
lean_object* v___x_3375_; uint8_t v___x_3376_; 
lean_inc_ref(v_consumeParamPred_3359_);
v___x_3375_ = lean_apply_1(v_consumeParamPred_3359_, v___x_3370_);
v___x_3376_ = lean_unbox(v___x_3375_);
if (v___x_3376_ == 0)
{
v___y_3368_ = v___x_3374_;
goto v___jp_3367_;
}
else
{
v_i_3361_ = v_n_3366_;
goto _start;
}
}
}
v___jp_3367_:
{
if (v___y_3368_ == 0)
{
v_i_3361_ = v_n_3366_;
goto _start;
}
else
{
lean_dec(v_n_3366_);
lean_dec_ref(v_consumeParamPred_3359_);
return v___y_3368_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_3357_ = stack[0].m_obj;
lean_object* v_arg_3358_ = stack[1].m_obj;
lean_object* v_consumeParamPred_3359_ = stack[2].m_obj;
lean_object* v_n_3360_ = stack[3].m_obj;
lean_object* v_i_3361_ = stack[4].m_obj;
uint8_t v_res_3378_;
v_res_3378_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3357_, v_arg_3358_, v_consumeParamPred_3359_, v_n_3360_, v_i_3361_);
stack->m_num = v_res_3378_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg___boxed(lean_object* v_args_3379_, lean_object* v_arg_3380_, lean_object* v_consumeParamPred_3381_, lean_object* v_n_3382_, lean_object* v_i_3383_){
_start:
{
uint8_t v_res_3384_; lean_object* v_r_3385_; 
v_res_3384_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3379_, v_arg_3380_, v_consumeParamPred_3381_, v_n_3382_, v_i_3383_);
lean_dec(v_n_3382_);
lean_dec(v_arg_3380_);
lean_dec_ref(v_args_3379_);
v_r_3385_ = lean_box(v_res_3384_);
return v_r_3385_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(lean_object* v_arg_3386_, lean_object* v_args_3387_, lean_object* v_consumeParamPred_3388_){
_start:
{
lean_object* v___x_3389_; uint8_t v___x_3390_; 
v___x_3389_ = lean_array_get_size(v_args_3387_);
v___x_3390_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3387_, v_arg_3386_, v_consumeParamPred_3388_, v___x_3389_, v___x_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_3386_ = stack[0].m_obj;
lean_object* v_args_3387_ = stack[1].m_obj;
lean_object* v_consumeParamPred_3388_ = stack[2].m_obj;
uint8_t v_res_3391_;
v_res_3391_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_arg_3386_, v_args_3387_, v_consumeParamPred_3388_);
stack->m_num = v_res_3391_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux___boxed(lean_object* v_arg_3392_, lean_object* v_args_3393_, lean_object* v_consumeParamPred_3394_){
_start:
{
uint8_t v_res_3395_; lean_object* v_r_3396_; 
v_res_3395_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_arg_3392_, v_args_3393_, v_consumeParamPred_3394_);
lean_dec_ref(v_args_3393_);
lean_dec(v_arg_3392_);
v_r_3396_ = lean_box(v_res_3395_);
return v_r_3396_;
}
}
uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(lean_object* v_args_3397_, lean_object* v_arg_3398_, lean_object* v_consumeParamPred_3399_, lean_object* v_n_3400_, lean_object* v_i_3401_, lean_object* v_a_3402_){
_start:
{
uint8_t v___x_3403_; 
v___x_3403_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3397_, v_arg_3398_, v_consumeParamPred_3399_, v_n_3400_, v_i_3401_);
return v___x_3403_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_3397_ = stack[0].m_obj;
lean_object* v_arg_3398_ = stack[1].m_obj;
lean_object* v_consumeParamPred_3399_ = stack[2].m_obj;
lean_object* v_n_3400_ = stack[3].m_obj;
lean_object* v_i_3401_ = stack[4].m_obj;
uint8_t v_res_3404_;
v_res_3404_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(v_args_3397_, v_arg_3398_, v_consumeParamPred_3399_, v_n_3400_, v_i_3401_, lean_box(0));
stack->m_num = v_res_3404_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___boxed(lean_object* v_args_3405_, lean_object* v_arg_3406_, lean_object* v_consumeParamPred_3407_, lean_object* v_n_3408_, lean_object* v_i_3409_, lean_object* v_a_3410_){
_start:
{
uint8_t v_res_3411_; lean_object* v_r_3412_; 
v_res_3411_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(v_args_3405_, v_arg_3406_, v_consumeParamPred_3407_, v_n_3408_, v_i_3409_, v_a_3410_);
lean_dec(v_n_3408_);
lean_dec(v_arg_3406_);
lean_dec_ref(v_args_3405_);
v_r_3412_ = lean_box(v_res_3411_);
return v_r_3412_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_3413_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(lean_object* v_ps_3414_, lean_object* v_i_3415_){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; uint8_t v_borrow_3418_; 
v___x_3416_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0);
v___x_3417_ = lean_array_get_borrowed(v___x_3416_, v_ps_3414_, v_i_3415_);
v_borrow_3418_ = lean_ctor_get_uint8(v___x_3417_, sizeof(void*)*3);
if (v_borrow_3418_ == 0)
{
uint8_t v___x_3419_; 
v___x_3419_ = 1;
return v___x_3419_;
}
else
{
uint8_t v___x_3420_; 
v___x_3420_ = 0;
return v___x_3420_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ps_3414_ = stack[0].m_obj;
lean_object* v_i_3415_ = stack[1].m_obj;
uint8_t v_res_3421_;
v_res_3421_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(v_ps_3414_, v_i_3415_);
stack->m_num = v_res_3421_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed(lean_object* v_ps_3422_, lean_object* v_i_3423_){
_start:
{
uint8_t v_res_3424_; lean_object* v_r_3425_; 
v_res_3424_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(v_ps_3422_, v_i_3423_);
lean_dec(v_i_3423_);
lean_dec_ref(v_ps_3422_);
v_r_3425_ = lean_box(v_res_3424_);
return v_r_3425_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(lean_object* v_arg_3426_, lean_object* v_args_3427_, lean_object* v_ps_3428_){
_start:
{
lean_object* v___f_3429_; uint8_t v___x_3430_; 
v___f_3429_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3429_, 0, v_ps_3428_);
v___x_3430_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_arg_3426_, v_args_3427_, v___f_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_3426_ = stack[0].m_obj;
lean_object* v_args_3427_ = stack[1].m_obj;
lean_object* v_ps_3428_ = stack[2].m_obj;
uint8_t v_res_3431_;
v_res_3431_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(v_arg_3426_, v_args_3427_, v_ps_3428_);
stack->m_num = v_res_3431_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___boxed(lean_object* v_arg_3432_, lean_object* v_args_3433_, lean_object* v_ps_3434_){
_start:
{
uint8_t v_res_3435_; lean_object* v_r_3436_; 
v_res_3435_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(v_arg_3432_, v_args_3433_, v_ps_3434_);
lean_dec_ref(v_args_3433_);
lean_dec(v_arg_3432_);
v_r_3436_ = lean_box(v_res_3435_);
return v_r_3436_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(lean_object* v_upperBound_3437_, lean_object* v_args_3438_, lean_object* v_arg_3439_, lean_object* v_consumeParamPred_3440_, lean_object* v_a_3441_, lean_object* v_b_3442_){
_start:
{
lean_object* v_a_3444_; uint8_t v___y_3449_; uint8_t v___x_3452_; 
v___x_3452_ = lean_nat_dec_lt(v_a_3441_, v_upperBound_3437_);
if (v___x_3452_ == 0)
{
lean_dec(v_a_3441_);
lean_dec_ref(v_consumeParamPred_3440_);
return v_b_3442_;
}
else
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_array_fget_borrowed(v_args_3438_, v_a_3441_);
if (lean_obj_tag(v___x_3453_) == 1)
{
lean_object* v_fvarId_3454_; uint8_t v___x_3455_; 
v_fvarId_3454_ = lean_ctor_get(v___x_3453_, 0);
v___x_3455_ = l_Lean_instBEqFVarId_beq(v_arg_3439_, v_fvarId_3454_);
if (v___x_3455_ == 0)
{
v___y_3449_ = v___x_3455_;
goto v___jp_3448_;
}
else
{
lean_object* v___x_3456_; uint8_t v___x_3457_; 
lean_inc_ref(v_consumeParamPred_3440_);
lean_inc(v_a_3441_);
v___x_3456_ = lean_apply_1(v_consumeParamPred_3440_, v_a_3441_);
v___x_3457_ = lean_unbox(v___x_3456_);
v___y_3449_ = v___x_3457_;
goto v___jp_3448_;
}
}
else
{
v_a_3444_ = v_b_3442_;
goto v___jp_3443_;
}
}
v___jp_3443_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = lean_unsigned_to_nat(1u);
v___x_3446_ = lean_nat_add(v_a_3441_, v___x_3445_);
lean_dec(v_a_3441_);
v_a_3441_ = v___x_3446_;
v_b_3442_ = v_a_3444_;
goto _start;
}
v___jp_3448_:
{
if (v___y_3449_ == 0)
{
v_a_3444_ = v_b_3442_;
goto v___jp_3443_;
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = lean_unsigned_to_nat(1u);
v___x_3451_ = lean_nat_add(v_b_3442_, v___x_3450_);
lean_dec(v_b_3442_);
v_a_3444_ = v___x_3451_;
goto v___jp_3443_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg___boxed(lean_object* v_upperBound_3458_, lean_object* v_args_3459_, lean_object* v_arg_3460_, lean_object* v_consumeParamPred_3461_, lean_object* v_a_3462_, lean_object* v_b_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v_upperBound_3458_, v_args_3459_, v_arg_3460_, v_consumeParamPred_3461_, v_a_3462_, v_b_3463_);
lean_dec(v_arg_3460_);
lean_dec_ref(v_args_3459_);
lean_dec(v_upperBound_3458_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(lean_object* v_arg_3465_, lean_object* v_args_3466_, lean_object* v_consumeParamPred_3467_){
_start:
{
lean_object* v_num_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v_num_3468_ = lean_unsigned_to_nat(0u);
v___x_3469_ = lean_array_get_size(v_args_3466_);
v___x_3470_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v___x_3469_, v_args_3466_, v_arg_3465_, v_consumeParamPred_3467_, v_num_3468_, v_num_3468_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions___boxed(lean_object* v_arg_3471_, lean_object* v_args_3472_, lean_object* v_consumeParamPred_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(v_arg_3471_, v_args_3472_, v_consumeParamPred_3473_);
lean_dec_ref(v_args_3472_);
lean_dec(v_arg_3471_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0(lean_object* v_upperBound_3475_, lean_object* v_args_3476_, lean_object* v_arg_3477_, lean_object* v_consumeParamPred_3478_, lean_object* v_inst_3479_, lean_object* v_R_3480_, lean_object* v_a_3481_, lean_object* v_b_3482_, lean_object* v_c_3483_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v_upperBound_3475_, v_args_3476_, v_arg_3477_, v_consumeParamPred_3478_, v_a_3481_, v_b_3482_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___boxed(lean_object* v_upperBound_3485_, lean_object* v_args_3486_, lean_object* v_arg_3487_, lean_object* v_consumeParamPred_3488_, lean_object* v_inst_3489_, lean_object* v_R_3490_, lean_object* v_a_3491_, lean_object* v_b_3492_, lean_object* v_c_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0(v_upperBound_3485_, v_args_3486_, v_arg_3487_, v_consumeParamPred_3488_, v_inst_3489_, v_R_3490_, v_a_3491_, v_b_3492_, v_c_3493_);
lean_dec(v_arg_3487_);
lean_dec_ref(v_args_3486_);
lean_dec(v_upperBound_3485_);
return v_res_3494_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(lean_object* v_fvarId_3495_, lean_object* v_b_3496_, uint8_t v___x_3497_, lean_object* v_numIncs_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_a_3507_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
v___x_3510_ = lean_unsigned_to_nat(0u);
v___x_3511_ = lean_nat_dec_eq(v_numIncs_3498_, v___x_3510_);
if (v___x_3511_ == 0)
{
lean_object* v_varMap_3512_; lean_object* v___x_3513_; uint8_t v___y_3515_; uint8_t v_isDefiniteRef_3518_; 
v_varMap_3512_ = lean_ctor_get(v___y_3499_, 3);
v___x_3513_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3512_, v_fvarId_3495_);
v_isDefiniteRef_3518_ = lean_ctor_get_uint8(v___x_3513_, sizeof(void*)*2 + 1);
if (v_isDefiniteRef_3518_ == 0)
{
v___y_3515_ = v___x_3497_;
goto v___jp_3514_;
}
else
{
v___y_3515_ = v___x_3511_;
goto v___jp_3514_;
}
v___jp_3514_:
{
uint8_t v_persistent_3516_; lean_object* v___x_3517_; 
v_persistent_3516_ = lean_ctor_get_uint8(v___x_3513_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_3513_);
v___x_3517_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_3517_, 0, v_fvarId_3495_);
lean_ctor_set(v___x_3517_, 1, v_numIncs_3498_);
lean_ctor_set(v___x_3517_, 2, v_b_3496_);
lean_ctor_set_uint8(v___x_3517_, sizeof(void*)*3, v___y_3515_);
lean_ctor_set_uint8(v___x_3517_, sizeof(void*)*3 + 1, v_persistent_3516_);
v_a_3507_ = v___x_3517_;
goto v___jp_3506_;
}
}
else
{
lean_dec(v_numIncs_3498_);
lean_dec(v_fvarId_3495_);
v_a_3507_ = v_b_3496_;
goto v___jp_3506_;
}
v___jp_3506_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_a_3507_);
v___x_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
return v___x_3509_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_3495_ = stack[0].m_obj;
lean_object* v_b_3496_ = stack[1].m_obj;
uint8_t v___x_3497_ = stack[2].m_num;
lean_object* v_numIncs_3498_ = stack[3].m_obj;
lean_object* v___y_3499_ = stack[4].m_obj;
lean_object* v___y_3500_ = stack[5].m_obj;
lean_object* v___y_3501_ = stack[6].m_obj;
lean_object* v___y_3502_ = stack[7].m_obj;
lean_object* v___y_3503_ = stack[8].m_obj;
lean_object* v___y_3504_ = stack[9].m_obj;
lean_object* v_res_3519_;
v_res_3519_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3495_, v_b_3496_, v___x_3497_, v_numIncs_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
stack->m_obj
 = v_res_3519_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_3520_, lean_object* v_b_3521_, lean_object* v___x_3522_, lean_object* v_numIncs_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
uint8_t v___x_7163__boxed_3531_; lean_object* v_res_3532_; 
v___x_7163__boxed_3531_ = lean_unbox(v___x_3522_);
v_res_3532_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3520_, v_b_3521_, v___x_7163__boxed_3531_, v_numIncs_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
return v_res_3532_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(lean_object* v_upperBound_3533_, lean_object* v_args_3534_, lean_object* v_consumeParamPred_3535_, lean_object* v_a_3536_, lean_object* v_b_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_a_3546_; lean_object* v___y_3551_; uint8_t v___x_3570_; 
v___x_3570_ = lean_nat_dec_lt(v_a_3536_, v_upperBound_3533_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
lean_dec(v_a_3536_);
lean_dec_ref(v_consumeParamPred_3535_);
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v_b_3537_);
return v___x_3571_;
}
else
{
lean_object* v___x_3572_; 
v___x_3572_ = lean_array_fget_borrowed(v_args_3534_, v_a_3536_);
if (lean_obj_tag(v___x_3572_) == 1)
{
lean_object* v_fvarId_3573_; lean_object* v_varMap_3574_; lean_object* v___x_3575_; uint8_t v_isPossibleRef_3576_; 
v_fvarId_3573_ = lean_ctor_get(v___x_3572_, 0);
v_varMap_3574_ = lean_ctor_get(v___y_3538_, 3);
v___x_3575_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3574_, v_fvarId_3573_);
v_isPossibleRef_3576_ = lean_ctor_get_uint8(v___x_3575_, sizeof(void*)*2);
lean_dec_ref(v___x_3575_);
if (v_isPossibleRef_3576_ == 0)
{
v_a_3546_ = v_b_3537_;
goto v___jp_3545_;
}
else
{
uint8_t v___x_3577_; 
lean_inc(v_a_3536_);
v___x_3577_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3534_, v_a_3536_);
if (v___x_3577_ == 0)
{
v_a_3546_ = v_b_3537_;
goto v___jp_3545_;
}
else
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v_vars_3580_; uint8_t v___x_3581_; lean_object* v___x_3582_; uint8_t v___y_3586_; 
lean_inc_ref(v_consumeParamPred_3535_);
v___x_3578_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(v_fvarId_3573_, v_args_3534_, v_consumeParamPred_3535_);
v___x_3579_ = lean_st_ref_get(v___y_3539_);
v_vars_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc_ref(v_vars_3580_);
lean_dec(v___x_3579_);
v___x_3581_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_3580_, v_fvarId_3573_);
lean_dec_ref(v_vars_3580_);
v___x_3582_ = lean_st_ref_get(v___y_3539_);
if (v___x_3581_ == 0)
{
lean_object* v_borrows_3591_; uint8_t v___x_3592_; 
v_borrows_3591_ = lean_ctor_get(v___x_3582_, 1);
lean_inc_ref(v_borrows_3591_);
lean_dec(v___x_3582_);
v___x_3592_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_3591_, v_fvarId_3573_);
lean_dec_ref(v_borrows_3591_);
v___y_3586_ = v___x_3592_;
goto v___jp_3585_;
}
else
{
lean_dec(v___x_3582_);
v___y_3586_ = v___x_3581_;
goto v___jp_3585_;
}
v___jp_3583_:
{
lean_object* v___x_3584_; 
lean_inc(v_fvarId_3573_);
v___x_3584_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3573_, v_b_3537_, v___x_3570_, v___x_3578_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3551_ = v___x_3584_;
goto v___jp_3550_;
}
v___jp_3585_:
{
if (v___y_3586_ == 0)
{
uint8_t v___x_3587_; 
lean_inc_ref(v_consumeParamPred_3535_);
v___x_3587_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_fvarId_3573_, v_args_3534_, v_consumeParamPred_3535_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3588_ = lean_unsigned_to_nat(1u);
v___x_3589_ = lean_nat_sub(v___x_3578_, v___x_3588_);
lean_dec(v___x_3578_);
lean_inc(v_fvarId_3573_);
v___x_3590_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3573_, v_b_3537_, v___x_3570_, v___x_3589_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
v___y_3551_ = v___x_3590_;
goto v___jp_3550_;
}
else
{
goto v___jp_3583_;
}
}
else
{
goto v___jp_3583_;
}
}
}
}
}
else
{
v_a_3546_ = v_b_3537_;
goto v___jp_3545_;
}
}
v___jp_3545_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = lean_nat_add(v_a_3536_, v___x_3547_);
lean_dec(v_a_3536_);
v_a_3536_ = v___x_3548_;
v_b_3537_ = v_a_3546_;
goto _start;
}
v___jp_3550_:
{
if (lean_obj_tag(v___y_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3561_; 
v_a_3552_ = lean_ctor_get(v___y_3551_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___y_3551_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3554_ = v___y_3551_;
v_isShared_3555_ = v_isSharedCheck_3561_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___y_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3561_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
if (lean_obj_tag(v_a_3552_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; 
lean_dec(v_a_3536_);
lean_dec_ref(v_consumeParamPred_3535_);
v_a_3556_ = lean_ctor_get(v_a_3552_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v_a_3552_, 1);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v_a_3556_);
v___x_3558_ = v___x_3554_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
else
{
lean_object* v_a_3560_; 
lean_del_object(v___x_3554_);
v_a_3560_ = lean_ctor_get(v_a_3552_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v_a_3552_, 1);
v_a_3546_ = v_a_3560_;
goto v___jp_3545_;
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec(v_a_3536_);
lean_dec_ref(v_consumeParamPred_3535_);
v_a_3562_ = lean_ctor_get(v___y_3551_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___y_3551_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___y_3551_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___y_3551_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3533_ = stack[0].m_obj;
lean_object* v_args_3534_ = stack[1].m_obj;
lean_object* v_consumeParamPred_3535_ = stack[2].m_obj;
lean_object* v_a_3536_ = stack[3].m_obj;
lean_object* v_b_3537_ = stack[4].m_obj;
lean_object* v___y_3538_ = stack[5].m_obj;
lean_object* v___y_3539_ = stack[6].m_obj;
lean_object* v___y_3540_ = stack[7].m_obj;
lean_object* v___y_3541_ = stack[8].m_obj;
lean_object* v___y_3542_ = stack[9].m_obj;
lean_object* v___y_3543_ = stack[10].m_obj;
lean_object* v_res_3593_;
v_res_3593_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v_upperBound_3533_, v_args_3534_, v_consumeParamPred_3535_, v_a_3536_, v_b_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
stack->m_obj
 = v_res_3593_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___boxed(lean_object* v_upperBound_3594_, lean_object* v_args_3595_, lean_object* v_consumeParamPred_3596_, lean_object* v_a_3597_, lean_object* v_b_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v_upperBound_3594_, v_args_3595_, v_consumeParamPred_3596_, v_a_3597_, v_b_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec_ref(v_args_3595_);
lean_dec(v_upperBound_3594_);
return v_res_3606_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(lean_object* v_args_3607_, lean_object* v_consumeParamPred_3608_, lean_object* v_k_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = lean_unsigned_to_nat(0u);
v___x_3618_ = lean_array_get_size(v_args_3607_);
v___x_3619_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v___x_3618_, v_args_3607_, v_consumeParamPred_3608_, v___x_3617_, v_k_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
return v___x_3619_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_3607_ = stack[0].m_obj;
lean_object* v_consumeParamPred_3608_ = stack[1].m_obj;
lean_object* v_k_3609_ = stack[2].m_obj;
lean_object* v_a_3610_ = stack[3].m_obj;
lean_object* v_a_3611_ = stack[4].m_obj;
lean_object* v_a_3612_ = stack[5].m_obj;
lean_object* v_a_3613_ = stack[6].m_obj;
lean_object* v_a_3614_ = stack[7].m_obj;
lean_object* v_a_3615_ = stack[8].m_obj;
lean_object* v_res_3620_;
v_res_3620_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3607_, v_consumeParamPred_3608_, v_k_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
stack->m_obj
 = v_res_3620_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux___boxed(lean_object* v_args_3621_, lean_object* v_consumeParamPred_3622_, lean_object* v_k_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3621_, v_consumeParamPred_3622_, v_k_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
lean_dec(v_a_3629_);
lean_dec_ref(v_a_3628_);
lean_dec(v_a_3627_);
lean_dec_ref(v_a_3626_);
lean_dec(v_a_3625_);
lean_dec_ref(v_a_3624_);
lean_dec_ref(v_args_3621_);
return v_res_3631_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(lean_object* v_upperBound_3632_, lean_object* v_args_3633_, lean_object* v_consumeParamPred_3634_, lean_object* v_inst_3635_, lean_object* v_R_3636_, lean_object* v_a_3637_, lean_object* v_b_3638_, lean_object* v_c_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v_upperBound_3632_, v_args_3633_, v_consumeParamPred_3634_, v_a_3637_, v_b_3638_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
return v___x_3647_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3632_ = stack[0].m_obj;
lean_object* v_args_3633_ = stack[1].m_obj;
lean_object* v_consumeParamPred_3634_ = stack[2].m_obj;
lean_object* v_a_3637_ = stack[5].m_obj;
lean_object* v_b_3638_ = stack[6].m_obj;
lean_object* v___y_3640_ = stack[8].m_obj;
lean_object* v___y_3641_ = stack[9].m_obj;
lean_object* v___y_3642_ = stack[10].m_obj;
lean_object* v___y_3643_ = stack[11].m_obj;
lean_object* v___y_3644_ = stack[12].m_obj;
lean_object* v___y_3645_ = stack[13].m_obj;
lean_object* v_res_3648_;
v_res_3648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(v_upperBound_3632_, v_args_3633_, v_consumeParamPred_3634_, lean_box(0), lean_box(0), v_a_3637_, v_b_3638_, lean_box(0), v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
stack->m_obj
 = v_res_3648_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___boxed(lean_object* v_upperBound_3649_, lean_object* v_args_3650_, lean_object* v_consumeParamPred_3651_, lean_object* v_inst_3652_, lean_object* v_R_3653_, lean_object* v_a_3654_, lean_object* v_b_3655_, lean_object* v_c_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(v_upperBound_3649_, v_args_3650_, v_consumeParamPred_3651_, v_inst_3652_, v_R_3653_, v_a_3654_, v_b_3655_, v_c_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec_ref(v_args_3650_);
lean_dec(v_upperBound_3649_);
return v_res_3664_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(lean_object* v_args_3665_, lean_object* v_ps_3666_, lean_object* v_k_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v___f_3675_; lean_object* v___x_3676_; 
v___f_3675_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3675_, 0, v_ps_3666_);
v___x_3676_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3665_, v___f_3675_, v_k_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_);
return v___x_3676_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_3665_ = stack[0].m_obj;
lean_object* v_ps_3666_ = stack[1].m_obj;
lean_object* v_k_3667_ = stack[2].m_obj;
lean_object* v_a_3668_ = stack[3].m_obj;
lean_object* v_a_3669_ = stack[4].m_obj;
lean_object* v_a_3670_ = stack[5].m_obj;
lean_object* v_a_3671_ = stack[6].m_obj;
lean_object* v_a_3672_ = stack[7].m_obj;
lean_object* v_a_3673_ = stack[8].m_obj;
lean_object* v_res_3677_;
v_res_3677_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_3665_, v_ps_3666_, v_k_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_);
stack->m_obj
 = v_res_3677_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore___boxed(lean_object* v_args_3678_, lean_object* v_ps_3679_, lean_object* v_k_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_3678_, v_ps_3679_, v_k_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
lean_dec(v_a_3686_);
lean_dec_ref(v_a_3685_);
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
lean_dec_ref(v_args_3678_);
return v_res_3688_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(lean_object* v_x_3689_){
_start:
{
uint8_t v___x_3690_; 
v___x_3690_ = 1;
return v___x_3690_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3689_ = stack[0].m_obj;
uint8_t v_res_3691_;
v_res_3691_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(v_x_3689_);
stack->m_num = v_res_3691_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0___boxed(lean_object* v_x_3692_){
_start:
{
uint8_t v_res_3693_; lean_object* v_r_3694_; 
v_res_3693_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(v_x_3692_);
lean_dec(v_x_3692_);
v_r_3694_ = lean_box(v_res_3693_);
return v_r_3694_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(lean_object* v_args_3696_, lean_object* v_k_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v___f_3705_; lean_object* v___x_3706_; 
v___f_3705_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___closed__0));
v___x_3706_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3696_, v___f_3705_, v_k_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
return v___x_3706_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_3696_ = stack[0].m_obj;
lean_object* v_k_3697_ = stack[1].m_obj;
lean_object* v_a_3698_ = stack[2].m_obj;
lean_object* v_a_3699_ = stack[3].m_obj;
lean_object* v_a_3700_ = stack[4].m_obj;
lean_object* v_a_3701_ = stack[5].m_obj;
lean_object* v_a_3702_ = stack[6].m_obj;
lean_object* v_a_3703_ = stack[7].m_obj;
lean_object* v_res_3707_;
v_res_3707_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_3696_, v_k_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
stack->m_obj
 = v_res_3707_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___boxed(lean_object* v_args_3708_, lean_object* v_k_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_3708_, v_k_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_);
lean_dec(v_a_3715_);
lean_dec_ref(v_a_3714_);
lean_dec(v_a_3713_);
lean_dec_ref(v_a_3712_);
lean_dec(v_a_3711_);
lean_dec_ref(v_a_3710_);
lean_dec_ref(v_args_3708_);
return v_res_3717_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(lean_object* v_upperBound_3718_, lean_object* v_args_3719_, lean_object* v_ps_3720_, lean_object* v_a_3721_, lean_object* v_b_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v_a_3727_; uint8_t v___x_3731_; 
v___x_3731_ = lean_nat_dec_lt(v_a_3721_, v_upperBound_3718_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; 
lean_dec(v_a_3721_);
lean_dec_ref(v_ps_3720_);
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v_b_3722_);
return v___x_3732_;
}
else
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_array_fget_borrowed(v_args_3719_, v_a_3721_);
if (lean_obj_tag(v___x_3733_) == 0)
{
v_a_3727_ = v_b_3722_;
goto v___jp_3726_;
}
else
{
lean_object* v_fvarId_3734_; lean_object* v_varMap_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v_vars_3738_; uint8_t v___x_3739_; lean_object* v___x_3740_; uint8_t v_isPossibleRef_3741_; 
v_fvarId_3734_ = lean_ctor_get(v___x_3733_, 0);
v_varMap_3735_ = lean_ctor_get(v___y_3723_, 3);
v___x_3736_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3735_, v_fvarId_3734_);
v___x_3737_ = lean_st_ref_get(v___y_3724_);
v_vars_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc_ref(v_vars_3738_);
lean_dec(v___x_3737_);
v___x_3739_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_3738_, v_fvarId_3734_);
lean_dec_ref(v_vars_3738_);
v___x_3740_ = lean_st_ref_get(v___y_3724_);
v_isPossibleRef_3741_ = lean_ctor_get_uint8(v___x_3736_, sizeof(void*)*2);
lean_dec_ref(v___x_3736_);
if (v_isPossibleRef_3741_ == 0)
{
lean_dec(v___x_3740_);
v_a_3727_ = v_b_3722_;
goto v___jp_3726_;
}
else
{
uint8_t v___x_3742_; 
lean_inc(v_a_3721_);
v___x_3742_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3719_, v_a_3721_);
if (v___x_3742_ == 0)
{
lean_dec(v___x_3740_);
v_a_3727_ = v_b_3722_;
goto v___jp_3726_;
}
else
{
uint8_t v___x_3743_; 
lean_inc_ref(v_ps_3720_);
v___x_3743_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(v_fvarId_3734_, v_args_3719_, v_ps_3720_);
if (v___x_3743_ == 0)
{
lean_dec(v___x_3740_);
v_a_3727_ = v_b_3722_;
goto v___jp_3726_;
}
else
{
if (v___x_3739_ == 0)
{
lean_object* v_borrows_3744_; uint8_t v___x_3745_; 
v_borrows_3744_ = lean_ctor_get(v___x_3740_, 1);
lean_inc_ref(v_borrows_3744_);
lean_dec(v___x_3740_);
v___x_3745_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_3744_, v_fvarId_3734_);
lean_dec_ref(v_borrows_3744_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3746_; 
lean_inc(v_fvarId_3734_);
v___x_3746_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_3734_, v_b_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3746_, 1);
v_a_3727_ = v_a_3747_;
goto v___jp_3726_;
}
else
{
lean_dec(v_a_3721_);
lean_dec_ref(v_ps_3720_);
return v___x_3746_;
}
}
else
{
v_a_3727_ = v_b_3722_;
goto v___jp_3726_;
}
}
else
{
lean_dec(v___x_3740_);
v_a_3727_ = v_b_3722_;
goto v___jp_3726_;
}
}
}
}
}
}
v___jp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = lean_unsigned_to_nat(1u);
v___x_3729_ = lean_nat_add(v_a_3721_, v___x_3728_);
lean_dec(v_a_3721_);
v_a_3721_ = v___x_3729_;
v_b_3722_ = v_a_3727_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3718_ = stack[0].m_obj;
lean_object* v_args_3719_ = stack[1].m_obj;
lean_object* v_ps_3720_ = stack[2].m_obj;
lean_object* v_a_3721_ = stack[3].m_obj;
lean_object* v_b_3722_ = stack[4].m_obj;
lean_object* v___y_3723_ = stack[5].m_obj;
lean_object* v___y_3724_ = stack[6].m_obj;
lean_object* v_res_3748_;
v_res_3748_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v_upperBound_3718_, v_args_3719_, v_ps_3720_, v_a_3721_, v_b_3722_, v___y_3723_, v___y_3724_);
stack->m_obj
 = v_res_3748_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg___boxed(lean_object* v_upperBound_3749_, lean_object* v_args_3750_, lean_object* v_ps_3751_, lean_object* v_a_3752_, lean_object* v_b_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v_upperBound_3749_, v_args_3750_, v_ps_3751_, v_a_3752_, v_b_3753_, v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_args_3750_);
lean_dec(v_upperBound_3749_);
return v_res_3757_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(lean_object* v_args_3758_, lean_object* v_ps_3759_, lean_object* v_k_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3768_ = lean_unsigned_to_nat(0u);
v___x_3769_ = lean_array_get_size(v_args_3758_);
v___x_3770_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v___x_3769_, v_args_3758_, v_ps_3759_, v___x_3768_, v_k_3760_, v_a_3761_, v_a_3762_);
return v___x_3770_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_3758_ = stack[0].m_obj;
lean_object* v_ps_3759_ = stack[1].m_obj;
lean_object* v_k_3760_ = stack[2].m_obj;
lean_object* v_a_3761_ = stack[3].m_obj;
lean_object* v_a_3762_ = stack[4].m_obj;
lean_object* v_a_3763_ = stack[5].m_obj;
lean_object* v_a_3764_ = stack[6].m_obj;
lean_object* v_a_3765_ = stack[7].m_obj;
lean_object* v_a_3766_ = stack[8].m_obj;
lean_object* v_res_3771_;
v_res_3771_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(v_args_3758_, v_ps_3759_, v_k_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_);
stack->m_obj
 = v_res_3771_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp___boxed(lean_object* v_args_3772_, lean_object* v_ps_3773_, lean_object* v_k_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(v_args_3772_, v_ps_3773_, v_k_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec_ref(v_args_3772_);
return v_res_3782_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(lean_object* v_upperBound_3783_, lean_object* v_args_3784_, lean_object* v_ps_3785_, lean_object* v_inst_3786_, lean_object* v_R_3787_, lean_object* v_a_3788_, lean_object* v_b_3789_, lean_object* v_c_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v_upperBound_3783_, v_args_3784_, v_ps_3785_, v_a_3788_, v_b_3789_, v___y_3791_, v___y_3792_);
return v___x_3798_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3783_ = stack[0].m_obj;
lean_object* v_args_3784_ = stack[1].m_obj;
lean_object* v_ps_3785_ = stack[2].m_obj;
lean_object* v_a_3788_ = stack[5].m_obj;
lean_object* v_b_3789_ = stack[6].m_obj;
lean_object* v___y_3791_ = stack[8].m_obj;
lean_object* v___y_3792_ = stack[9].m_obj;
lean_object* v___y_3793_ = stack[10].m_obj;
lean_object* v___y_3794_ = stack[11].m_obj;
lean_object* v___y_3795_ = stack[12].m_obj;
lean_object* v___y_3796_ = stack[13].m_obj;
lean_object* v_res_3799_;
v_res_3799_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(v_upperBound_3783_, v_args_3784_, v_ps_3785_, lean_box(0), lean_box(0), v_a_3788_, v_b_3789_, lean_box(0), v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
stack->m_obj
 = v_res_3799_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___boxed(lean_object* v_upperBound_3800_, lean_object* v_args_3801_, lean_object* v_ps_3802_, lean_object* v_inst_3803_, lean_object* v_R_3804_, lean_object* v_a_3805_, lean_object* v_b_3806_, lean_object* v_c_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(v_upperBound_3800_, v_args_3801_, v_ps_3802_, v_inst_3803_, v_R_3804_, v_a_3805_, v_b_3806_, v_c_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec_ref(v_args_3801_);
lean_dec(v_upperBound_3800_);
return v_res_3815_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(lean_object* v_fvarId_3816_, lean_object* v_k_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v_varMap_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v_borrows_3824_; uint8_t v___x_3825_; lean_object* v___x_3826_; uint8_t v_isPossibleRef_3827_; 
v_varMap_3821_ = lean_ctor_get(v_a_3818_, 3);
v___x_3822_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3821_, v_fvarId_3816_);
v___x_3823_ = lean_st_ref_get(v_a_3819_);
v_borrows_3824_ = lean_ctor_get(v___x_3823_, 1);
lean_inc_ref(v_borrows_3824_);
lean_dec(v___x_3823_);
v___x_3825_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_3824_, v_fvarId_3816_);
lean_dec_ref(v_borrows_3824_);
v___x_3826_ = lean_st_ref_get(v_a_3819_);
v_isPossibleRef_3827_ = lean_ctor_get_uint8(v___x_3822_, sizeof(void*)*2);
lean_dec_ref(v___x_3822_);
if (v_isPossibleRef_3827_ == 0)
{
lean_object* v___x_3828_; 
lean_dec(v___x_3826_);
lean_dec(v_fvarId_3816_);
v___x_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3828_, 0, v_k_3817_);
return v___x_3828_;
}
else
{
if (v___x_3825_ == 0)
{
lean_object* v_vars_3829_; uint8_t v___x_3830_; 
v_vars_3829_ = lean_ctor_get(v___x_3826_, 0);
lean_inc_ref(v_vars_3829_);
lean_dec(v___x_3826_);
v___x_3830_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_3829_, v_fvarId_3816_);
lean_dec_ref(v_vars_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; 
v___x_3831_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_3816_, v_k_3817_, v_a_3818_);
return v___x_3831_;
}
else
{
lean_object* v___x_3832_; 
lean_dec(v_fvarId_3816_);
v___x_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3832_, 0, v_k_3817_);
return v___x_3832_;
}
}
else
{
lean_object* v___x_3833_; 
lean_dec(v___x_3826_);
lean_dec(v_fvarId_3816_);
v___x_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3833_, 0, v_k_3817_);
return v___x_3833_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_3816_ = stack[0].m_obj;
lean_object* v_k_3817_ = stack[1].m_obj;
lean_object* v_a_3818_ = stack[2].m_obj;
lean_object* v_a_3819_ = stack[3].m_obj;
lean_object* v_res_3834_;
v_res_3834_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3816_, v_k_3817_, v_a_3818_, v_a_3819_);
stack->m_obj
 = v_res_3834_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg___boxed(lean_object* v_fvarId_3835_, lean_object* v_k_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3835_, v_k_3836_, v_a_3837_, v_a_3838_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
return v_res_3840_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(lean_object* v_fvarId_3841_, lean_object* v_k_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3841_, v_k_3842_, v_a_3843_, v_a_3844_);
return v___x_3850_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_3841_ = stack[0].m_obj;
lean_object* v_k_3842_ = stack[1].m_obj;
lean_object* v_a_3843_ = stack[2].m_obj;
lean_object* v_a_3844_ = stack[3].m_obj;
lean_object* v_a_3845_ = stack[4].m_obj;
lean_object* v_a_3846_ = stack[5].m_obj;
lean_object* v_a_3847_ = stack[6].m_obj;
lean_object* v_a_3848_ = stack[7].m_obj;
lean_object* v_res_3851_;
v_res_3851_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(v_fvarId_3841_, v_k_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
stack->m_obj
 = v_res_3851_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___boxed(lean_object* v_fvarId_3852_, lean_object* v_k_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(v_fvarId_3852_, v_k_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
lean_dec(v_a_3859_);
lean_dec_ref(v_a_3858_);
lean_dec(v_a_3857_);
lean_dec_ref(v_a_3856_);
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(lean_object* v_a_3862_, lean_object* v_x_3863_){
_start:
{
if (lean_obj_tag(v_x_3863_) == 0)
{
return v_x_3863_;
}
else
{
lean_object* v_key_3864_; lean_object* v_value_3865_; lean_object* v_tail_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3875_; 
v_key_3864_ = lean_ctor_get(v_x_3863_, 0);
v_value_3865_ = lean_ctor_get(v_x_3863_, 1);
v_tail_3866_ = lean_ctor_get(v_x_3863_, 2);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_x_3863_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3868_ = v_x_3863_;
v_isShared_3869_ = v_isSharedCheck_3875_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_tail_3866_);
lean_inc(v_value_3865_);
lean_inc(v_key_3864_);
lean_dec(v_x_3863_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3875_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
uint8_t v___x_3870_; 
v___x_3870_ = l_Lean_instBEqFVarId_beq(v_key_3864_, v_a_3862_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; lean_object* v___x_3873_; 
v___x_3871_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3862_, v_tail_3866_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 2, v___x_3871_);
v___x_3873_ = v___x_3868_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_key_3864_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v_value_3865_);
lean_ctor_set(v_reuseFailAlloc_3874_, 2, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
else
{
lean_del_object(v___x_3868_);
lean_dec(v_value_3865_);
lean_dec(v_key_3864_);
return v_tail_3866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg___boxed(lean_object* v_a_3876_, lean_object* v_x_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3876_, v_x_3877_);
lean_dec(v_a_3876_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(lean_object* v_m_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v_size_3881_; lean_object* v_buckets_3882_; lean_object* v___x_3883_; uint64_t v___x_3884_; uint64_t v___x_3885_; uint64_t v___x_3886_; uint64_t v_fold_3887_; uint64_t v___x_3888_; uint64_t v___x_3889_; uint64_t v___x_3890_; size_t v___x_3891_; size_t v___x_3892_; size_t v___x_3893_; size_t v___x_3894_; size_t v___x_3895_; lean_object* v_bkt_3896_; uint8_t v___x_3897_; 
v_size_3881_ = lean_ctor_get(v_m_3879_, 0);
v_buckets_3882_ = lean_ctor_get(v_m_3879_, 1);
v___x_3883_ = lean_array_get_size(v_buckets_3882_);
v___x_3884_ = l_Lean_instHashableFVarId_hash(v_a_3880_);
v___x_3885_ = 32ULL;
v___x_3886_ = lean_uint64_shift_right(v___x_3884_, v___x_3885_);
v_fold_3887_ = lean_uint64_xor(v___x_3884_, v___x_3886_);
v___x_3888_ = 16ULL;
v___x_3889_ = lean_uint64_shift_right(v_fold_3887_, v___x_3888_);
v___x_3890_ = lean_uint64_xor(v_fold_3887_, v___x_3889_);
v___x_3891_ = lean_uint64_to_usize(v___x_3890_);
v___x_3892_ = lean_usize_of_nat(v___x_3883_);
v___x_3893_ = ((size_t)1ULL);
v___x_3894_ = lean_usize_sub(v___x_3892_, v___x_3893_);
v___x_3895_ = lean_usize_land(v___x_3891_, v___x_3894_);
v_bkt_3896_ = lean_array_uget_borrowed(v_buckets_3882_, v___x_3895_);
v___x_3897_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_3880_, v_bkt_3896_);
if (v___x_3897_ == 0)
{
return v_m_3879_;
}
else
{
lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3910_; 
lean_inc(v_bkt_3896_);
lean_inc_ref(v_buckets_3882_);
lean_inc(v_size_3881_);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_m_3879_);
if (v_isSharedCheck_3910_ == 0)
{
lean_object* v_unused_3911_; lean_object* v_unused_3912_; 
v_unused_3911_ = lean_ctor_get(v_m_3879_, 1);
lean_dec(v_unused_3911_);
v_unused_3912_ = lean_ctor_get(v_m_3879_, 0);
lean_dec(v_unused_3912_);
v___x_3899_ = v_m_3879_;
v_isShared_3900_ = v_isSharedCheck_3910_;
goto v_resetjp_3898_;
}
else
{
lean_dec(v_m_3879_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3910_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3901_; lean_object* v_buckets_x27_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3901_ = lean_box(0);
v_buckets_x27_3902_ = lean_array_uset(v_buckets_3882_, v___x_3895_, v___x_3901_);
v___x_3903_ = lean_unsigned_to_nat(1u);
v___x_3904_ = lean_nat_sub(v_size_3881_, v___x_3903_);
lean_dec(v_size_3881_);
v___x_3905_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3880_, v_bkt_3896_);
v___x_3906_ = lean_array_uset(v_buckets_x27_3902_, v___x_3895_, v___x_3905_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 1, v___x_3906_);
lean_ctor_set(v___x_3899_, 0, v___x_3904_);
v___x_3908_ = v___x_3899_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg___boxed(lean_object* v_m_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_m_3913_, v_a_3914_);
lean_dec(v_a_3914_);
return v_res_3915_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(lean_object* v_as_3916_, size_t v_i_3917_, size_t v_stop_3918_, lean_object* v_b_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v_a_3924_; uint8_t v___x_3928_; 
v___x_3928_ = lean_usize_dec_eq(v_i_3917_, v_stop_3918_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; lean_object* v_fvarId_3930_; lean_object* v___x_3931_; 
v___x_3929_ = lean_array_uget_borrowed(v_as_3916_, v_i_3917_);
v_fvarId_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_fvarId_3930_);
v___x_3931_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3930_, v_b_3919_, v___y_3920_, v___y_3921_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3933_; lean_object* v_vars_3934_; lean_object* v_borrows_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3945_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v___x_3933_ = lean_st_ref_take(v___y_3921_);
v_vars_3934_ = lean_ctor_get(v___x_3933_, 0);
v_borrows_3935_ = lean_ctor_get(v___x_3933_, 1);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3937_ = v___x_3933_;
v_isShared_3938_ = v_isSharedCheck_3945_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_borrows_3935_);
lean_inc(v_vars_3934_);
lean_dec(v___x_3933_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3945_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v_vars_3939_; lean_object* v_borrows_3940_; lean_object* v___x_3942_; 
v_vars_3939_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_vars_3934_, v_fvarId_3930_);
v_borrows_3940_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_borrows_3935_, v_fvarId_3930_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 1, v_borrows_3940_);
lean_ctor_set(v___x_3937_, 0, v_vars_3939_);
v___x_3942_ = v___x_3937_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_vars_3939_);
lean_ctor_set(v_reuseFailAlloc_3944_, 1, v_borrows_3940_);
v___x_3942_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3943_; 
v___x_3943_ = lean_st_ref_put(v___y_3921_, v___x_3942_);
v_a_3924_ = v_a_3932_;
goto v___jp_3923_;
}
}
}
else
{
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3946_; 
v_a_3946_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___x_3931_, 1);
v_a_3924_ = v_a_3946_;
goto v___jp_3923_;
}
else
{
return v___x_3931_;
}
}
}
else
{
lean_object* v___x_3947_; 
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v_b_3919_);
return v___x_3947_;
}
v___jp_3923_:
{
size_t v___x_3925_; size_t v___x_3926_; 
v___x_3925_ = ((size_t)1ULL);
v___x_3926_ = lean_usize_add(v_i_3917_, v___x_3925_);
v_i_3917_ = v___x_3926_;
v_b_3919_ = v_a_3924_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3916_ = stack[0].m_obj;
size_t v_i_3917_ = stack[1].m_num;
size_t v_stop_3918_ = stack[2].m_num;
lean_object* v_b_3919_ = stack[3].m_obj;
lean_object* v___y_3920_ = stack[4].m_obj;
lean_object* v___y_3921_ = stack[5].m_obj;
lean_object* v_res_3948_;
v_res_3948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_as_3916_, v_i_3917_, v_stop_3918_, v_b_3919_, v___y_3920_, v___y_3921_);
stack->m_obj
 = v_res_3948_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg___boxed(lean_object* v_as_3949_, lean_object* v_i_3950_, lean_object* v_stop_3951_, lean_object* v_b_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
size_t v_i_boxed_3956_; size_t v_stop_boxed_3957_; lean_object* v_res_3958_; 
v_i_boxed_3956_ = lean_unbox_usize(v_i_3950_);
lean_dec(v_i_3950_);
v_stop_boxed_3957_ = lean_unbox_usize(v_stop_3951_);
lean_dec(v_stop_3951_);
v_res_3958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_as_3949_, v_i_boxed_3956_, v_stop_boxed_3957_, v_b_3952_, v___y_3953_, v___y_3954_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec_ref(v_as_3949_);
return v_res_3958_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(lean_object* v_ps_3959_, lean_object* v_k_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; 
v___x_3968_ = lean_unsigned_to_nat(0u);
v___x_3969_ = lean_array_get_size(v_ps_3959_);
v___x_3970_ = lean_nat_dec_lt(v___x_3968_, v___x_3969_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3971_; 
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v_k_3960_);
return v___x_3971_;
}
else
{
uint8_t v___x_3972_; 
v___x_3972_ = lean_nat_dec_le(v___x_3969_, v___x_3969_);
if (v___x_3972_ == 0)
{
if (v___x_3970_ == 0)
{
lean_object* v___x_3973_; 
v___x_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3973_, 0, v_k_3960_);
return v___x_3973_;
}
else
{
size_t v___x_3974_; size_t v___x_3975_; lean_object* v___x_3976_; 
v___x_3974_ = ((size_t)0ULL);
v___x_3975_ = lean_usize_of_nat(v___x_3969_);
v___x_3976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_ps_3959_, v___x_3974_, v___x_3975_, v_k_3960_, v_a_3961_, v_a_3962_);
return v___x_3976_;
}
}
else
{
size_t v___x_3977_; size_t v___x_3978_; lean_object* v___x_3979_; 
v___x_3977_ = ((size_t)0ULL);
v___x_3978_ = lean_usize_of_nat(v___x_3969_);
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_ps_3959_, v___x_3977_, v___x_3978_, v_k_3960_, v_a_3961_, v_a_3962_);
return v___x_3979_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_ps_3959_ = stack[0].m_obj;
lean_object* v_k_3960_ = stack[1].m_obj;
lean_object* v_a_3961_ = stack[2].m_obj;
lean_object* v_a_3962_ = stack[3].m_obj;
lean_object* v_a_3963_ = stack[4].m_obj;
lean_object* v_a_3964_ = stack[5].m_obj;
lean_object* v_a_3965_ = stack[6].m_obj;
lean_object* v_a_3966_ = stack[7].m_obj;
lean_object* v_res_3980_;
v_res_3980_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_ps_3959_, v_k_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
stack->m_obj
 = v_res_3980_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams___boxed(lean_object* v_ps_3981_, lean_object* v_k_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_ps_3981_, v_k_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
lean_dec(v_a_3984_);
lean_dec_ref(v_a_3983_);
lean_dec_ref(v_ps_3981_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(lean_object* v_00_u03b2_3991_, lean_object* v_m_3992_, lean_object* v_a_3993_){
_start:
{
lean_object* v___x_3994_; 
v___x_3994_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_m_3992_, v_a_3993_);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___boxed(lean_object* v_00_u03b2_3995_, lean_object* v_m_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(v_00_u03b2_3995_, v_m_3996_, v_a_3997_);
lean_dec(v_a_3997_);
return v_res_3998_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1(lean_object* v_as_3999_, size_t v_i_4000_, size_t v_stop_4001_, lean_object* v_b_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_as_3999_, v_i_4000_, v_stop_4001_, v_b_4002_, v___y_4003_, v___y_4004_);
return v___x_4010_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3999_ = stack[0].m_obj;
size_t v_i_4000_ = stack[1].m_num;
size_t v_stop_4001_ = stack[2].m_num;
lean_object* v_b_4002_ = stack[3].m_obj;
lean_object* v___y_4003_ = stack[4].m_obj;
lean_object* v___y_4004_ = stack[5].m_obj;
lean_object* v___y_4005_ = stack[6].m_obj;
lean_object* v___y_4006_ = stack[7].m_obj;
lean_object* v___y_4007_ = stack[8].m_obj;
lean_object* v___y_4008_ = stack[9].m_obj;
lean_object* v_res_4011_;
v_res_4011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1(v_as_3999_, v_i_4000_, v_stop_4001_, v_b_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
stack->m_obj
 = v_res_4011_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___boxed(lean_object* v_as_4012_, lean_object* v_i_4013_, lean_object* v_stop_4014_, lean_object* v_b_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
size_t v_i_boxed_4023_; size_t v_stop_boxed_4024_; lean_object* v_res_4025_; 
v_i_boxed_4023_ = lean_unbox_usize(v_i_4013_);
lean_dec(v_i_4013_);
v_stop_boxed_4024_ = lean_unbox_usize(v_stop_4014_);
lean_dec(v_stop_4014_);
v_res_4025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1(v_as_4012_, v_i_boxed_4023_, v_stop_boxed_4024_, v_b_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec_ref(v_as_4012_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0(lean_object* v_00_u03b2_4026_, lean_object* v_a_4027_, lean_object* v_x_4028_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_4027_, v_x_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4030_, lean_object* v_a_4031_, lean_object* v_x_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0(v_00_u03b2_4030_, v_a_4031_, v_x_4032_);
lean_dec(v_a_4031_);
return v_res_4033_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(lean_object* v_msg_4035_){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0);
v___x_4037_ = lean_panic_fn_borrowed(v___x_4036_, v_msg_4035_);
return v___x_4037_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default___redArg();
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1(lean_object* v_msg_4039_){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4040_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0);
v___x_4041_ = lean_panic_fn_borrowed(v___x_4040_, v_msg_4039_);
return v___x_4041_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(lean_object* v_msg_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v_toApplicative_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4115_; 
v___x_4050_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0);
v___x_4051_ = l_StateRefT_x27_instMonad___redArg(v___x_4050_);
v_toApplicative_4052_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4115_ == 0)
{
lean_object* v_unused_4116_; 
v_unused_4116_ = lean_ctor_get(v___x_4051_, 1);
lean_dec(v_unused_4116_);
v___x_4054_ = v___x_4051_;
v_isShared_4055_ = v_isSharedCheck_4115_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_toApplicative_4052_);
lean_dec(v___x_4051_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4115_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v_toFunctor_4056_; lean_object* v_toSeq_4057_; lean_object* v_toSeqLeft_4058_; lean_object* v_toSeqRight_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4113_; 
v_toFunctor_4056_ = lean_ctor_get(v_toApplicative_4052_, 0);
v_toSeq_4057_ = lean_ctor_get(v_toApplicative_4052_, 2);
v_toSeqLeft_4058_ = lean_ctor_get(v_toApplicative_4052_, 3);
v_toSeqRight_4059_ = lean_ctor_get(v_toApplicative_4052_, 4);
v_isSharedCheck_4113_ = !lean_is_exclusive(v_toApplicative_4052_);
if (v_isSharedCheck_4113_ == 0)
{
lean_object* v_unused_4114_; 
v_unused_4114_ = lean_ctor_get(v_toApplicative_4052_, 1);
lean_dec(v_unused_4114_);
v___x_4061_ = v_toApplicative_4052_;
v_isShared_4062_ = v_isSharedCheck_4113_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_toSeqRight_4059_);
lean_inc(v_toSeqLeft_4058_);
lean_inc(v_toSeq_4057_);
lean_inc(v_toFunctor_4056_);
lean_dec(v_toApplicative_4052_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4113_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___f_4063_; lean_object* v___f_4064_; lean_object* v___f_4065_; lean_object* v___f_4066_; lean_object* v___x_4067_; lean_object* v___f_4068_; lean_object* v___f_4069_; lean_object* v___f_4070_; lean_object* v___x_4072_; 
v___f_4063_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__1));
v___f_4064_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4056_);
v___f_4065_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4065_, 0, v_toFunctor_4056_);
v___f_4066_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4066_, 0, v_toFunctor_4056_);
v___x_4067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___f_4065_);
lean_ctor_set(v___x_4067_, 1, v___f_4066_);
v___f_4068_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4068_, 0, v_toSeqRight_4059_);
v___f_4069_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4069_, 0, v_toSeqLeft_4058_);
v___f_4070_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4070_, 0, v_toSeq_4057_);
if (v_isShared_4062_ == 0)
{
lean_ctor_set(v___x_4061_, 4, v___f_4068_);
lean_ctor_set(v___x_4061_, 3, v___f_4069_);
lean_ctor_set(v___x_4061_, 2, v___f_4070_);
lean_ctor_set(v___x_4061_, 1, v___f_4063_);
lean_ctor_set(v___x_4061_, 0, v___x_4067_);
v___x_4072_ = v___x_4061_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4112_, 1, v___f_4063_);
lean_ctor_set(v_reuseFailAlloc_4112_, 2, v___f_4070_);
lean_ctor_set(v_reuseFailAlloc_4112_, 3, v___f_4069_);
lean_ctor_set(v_reuseFailAlloc_4112_, 4, v___f_4068_);
v___x_4072_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4074_; 
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 1, v___f_4064_);
lean_ctor_set(v___x_4054_, 0, v___x_4072_);
v___x_4074_ = v___x_4054_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4072_);
lean_ctor_set(v_reuseFailAlloc_4111_, 1, v___f_4064_);
v___x_4074_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4075_; lean_object* v_toApplicative_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4109_; 
v___x_4075_ = l_StateRefT_x27_instMonad___redArg(v___x_4074_);
v_toApplicative_4076_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4109_ == 0)
{
lean_object* v_unused_4110_; 
v_unused_4110_ = lean_ctor_get(v___x_4075_, 1);
lean_dec(v_unused_4110_);
v___x_4078_ = v___x_4075_;
v_isShared_4079_ = v_isSharedCheck_4109_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_toApplicative_4076_);
lean_dec(v___x_4075_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4109_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v_toFunctor_4080_; lean_object* v_toSeq_4081_; lean_object* v_toSeqLeft_4082_; lean_object* v_toSeqRight_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4107_; 
v_toFunctor_4080_ = lean_ctor_get(v_toApplicative_4076_, 0);
v_toSeq_4081_ = lean_ctor_get(v_toApplicative_4076_, 2);
v_toSeqLeft_4082_ = lean_ctor_get(v_toApplicative_4076_, 3);
v_toSeqRight_4083_ = lean_ctor_get(v_toApplicative_4076_, 4);
v_isSharedCheck_4107_ = !lean_is_exclusive(v_toApplicative_4076_);
if (v_isSharedCheck_4107_ == 0)
{
lean_object* v_unused_4108_; 
v_unused_4108_ = lean_ctor_get(v_toApplicative_4076_, 1);
lean_dec(v_unused_4108_);
v___x_4085_ = v_toApplicative_4076_;
v_isShared_4086_ = v_isSharedCheck_4107_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_toSeqRight_4083_);
lean_inc(v_toSeqLeft_4082_);
lean_inc(v_toSeq_4081_);
lean_inc(v_toFunctor_4080_);
lean_dec(v_toApplicative_4076_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4107_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___f_4087_; lean_object* v___f_4088_; lean_object* v___f_4089_; lean_object* v___f_4090_; lean_object* v___x_4091_; lean_object* v___f_4092_; lean_object* v___f_4093_; lean_object* v___f_4094_; lean_object* v___x_4096_; 
v___f_4087_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__3));
v___f_4088_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4080_);
v___f_4089_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4089_, 0, v_toFunctor_4080_);
v___f_4090_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4090_, 0, v_toFunctor_4080_);
v___x_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___f_4089_);
lean_ctor_set(v___x_4091_, 1, v___f_4090_);
v___f_4092_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4092_, 0, v_toSeqRight_4083_);
v___f_4093_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4093_, 0, v_toSeqLeft_4082_);
v___f_4094_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4094_, 0, v_toSeq_4081_);
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 4, v___f_4092_);
lean_ctor_set(v___x_4085_, 3, v___f_4093_);
lean_ctor_set(v___x_4085_, 2, v___f_4094_);
lean_ctor_set(v___x_4085_, 1, v___f_4087_);
lean_ctor_set(v___x_4085_, 0, v___x_4091_);
v___x_4096_ = v___x_4085_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4091_);
lean_ctor_set(v_reuseFailAlloc_4106_, 1, v___f_4087_);
lean_ctor_set(v_reuseFailAlloc_4106_, 2, v___f_4094_);
lean_ctor_set(v_reuseFailAlloc_4106_, 3, v___f_4093_);
lean_ctor_set(v_reuseFailAlloc_4106_, 4, v___f_4092_);
v___x_4096_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
lean_object* v___x_4098_; 
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 1, v___f_4088_);
lean_ctor_set(v___x_4078_, 0, v___x_4096_);
v___x_4098_ = v___x_4078_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4096_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v___f_4088_);
v___x_4098_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___f_4102_; lean_object* v___x_15460__overap_4103_; lean_object* v___x_4104_; 
v___x_4099_ = l_StateRefT_x27_instMonad___redArg(v___x_4098_);
v___x_4100_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0);
v___x_4101_ = l_instInhabitedOfMonad___redArg(v___x_4099_, v___x_4100_);
v___f_4102_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4102_, 0, v___x_4101_);
v___x_15460__overap_4103_ = lean_panic_fn_borrowed(v___f_4102_, v_msg_4042_);
lean_dec_ref(v___f_4102_);
lean_inc(v___y_4048_);
lean_inc_ref(v___y_4047_);
lean_inc(v___y_4046_);
lean_inc_ref(v___y_4045_);
lean_inc(v___y_4044_);
lean_inc_ref(v___y_4043_);
v___x_4104_ = lean_apply_7(v___x_15460__overap_4103_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, lean_box(0));
return v___x_4104_;
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4042_ = stack[0].m_obj;
lean_object* v___y_4043_ = stack[1].m_obj;
lean_object* v___y_4044_ = stack[2].m_obj;
lean_object* v___y_4045_ = stack[3].m_obj;
lean_object* v___y_4046_ = stack[4].m_obj;
lean_object* v___y_4047_ = stack[5].m_obj;
lean_object* v___y_4048_ = stack[6].m_obj;
lean_object* v_res_4117_;
v_res_4117_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v_msg_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
stack->m_obj
 = v_res_4117_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2___boxed(lean_object* v_msg_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v_msg_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
return v_res_4126_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2(void){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4129_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_4130_ = lean_unsigned_to_nat(9u);
v___x_4131_ = lean_unsigned_to_nat(625u);
v___x_4132_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__1));
v___x_4133_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__0));
v___x_4134_ = l_mkPanicMessageWithDecl(v___x_4133_, v___x_4132_, v___x_4131_, v___x_4130_, v___x_4129_);
return v___x_4134_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10(void){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4144_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9));
v___x_4145_ = lean_unsigned_to_nat(14u);
v___x_4146_ = lean_unsigned_to_nat(22u);
v___x_4147_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8));
v___x_4148_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7));
v___x_4149_ = l_mkPanicMessageWithDecl(v___x_4148_, v___x_4147_, v___x_4146_, v___x_4145_, v___x_4144_);
return v___x_4149_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12(void){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4151_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_4152_ = lean_unsigned_to_nat(22u);
v___x_4153_ = lean_unsigned_to_nat(575u);
v___x_4154_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11));
v___x_4155_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_4156_ = l_mkPanicMessageWithDecl(v___x_4155_, v___x_4154_, v___x_4153_, v___x_4152_, v___x_4151_);
return v___x_4156_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(lean_object* v_code_4157_, lean_object* v_decl_4158_, lean_object* v_k_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_){
_start:
{
lean_object* v_fvarId_4167_; lean_object* v_value_4168_; lean_object* v_k_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v_k_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___x_4243_; 
v_fvarId_4167_ = lean_ctor_get(v_decl_4158_, 0);
lean_inc_n(v_fvarId_4167_, 2);
v_value_4168_ = lean_ctor_get(v_decl_4158_, 3);
lean_inc(v_value_4168_);
v___x_4243_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_4167_, v_k_4159_, v_a_4160_, v_a_4161_);
switch(lean_obj_tag(v_value_4168_))
{
case 4:
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4286_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4246_ = v___x_4243_;
v_isShared_4247_ = v_isSharedCheck_4286_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4243_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4286_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v_fvarId_4248_; lean_object* v_args_4249_; lean_object* v___x_4251_; 
v_fvarId_4248_ = lean_ctor_get(v_value_4168_, 0);
v_args_4249_ = lean_ctor_get(v_value_4168_, 1);
lean_inc(v_fvarId_4248_);
if (v_isShared_4247_ == 0)
{
lean_ctor_set_tag(v___x_4246_, 1);
lean_ctor_set(v___x_4246_, 0, v_fvarId_4248_);
v___x_4251_ = v___x_4246_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_fvarId_4248_);
v___x_4251_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
lean_object* v___x_4252_; lean_object* v___y_4254_; 
lean_inc_ref(v_args_4249_);
v___x_4252_ = lean_array_push(v_args_4249_, v___x_4251_);
if (lean_obj_tag(v_code_4157_) == 0)
{
lean_object* v_decl_4257_; lean_object* v_k_4258_; size_t v___x_4259_; size_t v___x_4260_; uint8_t v___x_4261_; 
v_decl_4257_ = lean_ctor_get(v_code_4157_, 0);
v_k_4258_ = lean_ctor_get(v_code_4157_, 1);
v___x_4259_ = lean_ptr_addr(v_k_4258_);
v___x_4260_ = lean_ptr_addr(v_a_4244_);
v___x_4261_ = lean_usize_dec_eq(v___x_4259_, v___x_4260_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
v_isSharedCheck_4268_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4268_ == 0)
{
lean_object* v_unused_4269_; lean_object* v_unused_4270_; 
v_unused_4269_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4269_);
v_unused_4270_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4270_);
v___x_4263_ = v_code_4157_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_dec(v_code_4157_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 1, v_a_4244_);
lean_ctor_set(v___x_4263_, 0, v_decl_4158_);
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4267_, 1, v_a_4244_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
v___y_4254_ = v___x_4266_;
goto v___jp_4253_;
}
}
}
else
{
size_t v___x_4271_; size_t v___x_4272_; uint8_t v___x_4273_; 
v___x_4271_ = lean_ptr_addr(v_decl_4257_);
v___x_4272_ = lean_ptr_addr(v_decl_4158_);
v___x_4273_ = lean_usize_dec_eq(v___x_4271_, v___x_4272_);
if (v___x_4273_ == 0)
{
lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
v_isSharedCheck_4280_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4280_ == 0)
{
lean_object* v_unused_4281_; lean_object* v_unused_4282_; 
v_unused_4281_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4281_);
v_unused_4282_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4282_);
v___x_4275_ = v_code_4157_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_dec(v_code_4157_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
lean_ctor_set(v___x_4275_, 1, v_a_4244_);
lean_ctor_set(v___x_4275_, 0, v_decl_4158_);
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4279_, 1, v_a_4244_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
v___y_4254_ = v___x_4278_;
goto v___jp_4253_;
}
}
}
else
{
lean_dec(v_a_4244_);
lean_dec_ref(v_decl_4158_);
v___y_4254_ = v_code_4157_;
goto v___jp_4253_;
}
}
}
else
{
lean_object* v___x_4283_; lean_object* v___x_4284_; 
lean_dec(v_a_4244_);
lean_dec_ref(v_decl_4158_);
lean_dec_ref(v_code_4157_);
v___x_4283_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4284_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4283_);
v___y_4254_ = v___x_4284_;
goto v___jp_4253_;
}
v___jp_4253_:
{
lean_object* v___x_4255_; 
v___x_4255_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v___x_4252_, v___y_4254_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
lean_dec_ref(v___x_4252_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
v_k_4170_ = v_a_4256_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
else
{
lean_dec_ref_known(v_value_4168_, 2);
lean_dec(v_fvarId_4167_);
return v___x_4255_;
}
}
}
}
}
case 5:
{
lean_object* v_a_4287_; lean_object* v_args_4288_; lean_object* v___y_4290_; 
v_a_4287_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4287_);
lean_dec_ref(v___x_4243_);
v_args_4288_ = lean_ctor_get(v_value_4168_, 1);
if (lean_obj_tag(v_code_4157_) == 0)
{
lean_object* v_decl_4293_; lean_object* v_k_4294_; size_t v___x_4295_; size_t v___x_4296_; uint8_t v___x_4297_; 
v_decl_4293_ = lean_ctor_get(v_code_4157_, 0);
v_k_4294_ = lean_ctor_get(v_code_4157_, 1);
v___x_4295_ = lean_ptr_addr(v_k_4294_);
v___x_4296_ = lean_ptr_addr(v_a_4287_);
v___x_4297_ = lean_usize_dec_eq(v___x_4295_, v___x_4296_);
if (v___x_4297_ == 0)
{
lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
v_isSharedCheck_4304_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4304_ == 0)
{
lean_object* v_unused_4305_; lean_object* v_unused_4306_; 
v_unused_4305_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4305_);
v_unused_4306_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4306_);
v___x_4299_ = v_code_4157_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_dec(v_code_4157_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 1, v_a_4287_);
lean_ctor_set(v___x_4299_, 0, v_decl_4158_);
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4303_, 1, v_a_4287_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
v___y_4290_ = v___x_4302_;
goto v___jp_4289_;
}
}
}
else
{
size_t v___x_4307_; size_t v___x_4308_; uint8_t v___x_4309_; 
v___x_4307_ = lean_ptr_addr(v_decl_4293_);
v___x_4308_ = lean_ptr_addr(v_decl_4158_);
v___x_4309_ = lean_usize_dec_eq(v___x_4307_, v___x_4308_);
if (v___x_4309_ == 0)
{
lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
v_isSharedCheck_4316_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4316_ == 0)
{
lean_object* v_unused_4317_; lean_object* v_unused_4318_; 
v_unused_4317_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4317_);
v_unused_4318_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4318_);
v___x_4311_ = v_code_4157_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_dec(v_code_4157_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
lean_ctor_set(v___x_4311_, 1, v_a_4287_);
lean_ctor_set(v___x_4311_, 0, v_decl_4158_);
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4315_, 1, v_a_4287_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
v___y_4290_ = v___x_4314_;
goto v___jp_4289_;
}
}
}
else
{
lean_dec(v_a_4287_);
lean_dec_ref(v_decl_4158_);
v___y_4290_ = v_code_4157_;
goto v___jp_4289_;
}
}
}
else
{
lean_object* v___x_4319_; lean_object* v___x_4320_; 
lean_dec(v_a_4287_);
lean_dec_ref(v_decl_4158_);
lean_dec_ref(v_code_4157_);
v___x_4319_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4320_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4319_);
v___y_4290_ = v___x_4320_;
goto v___jp_4289_;
}
v___jp_4289_:
{
lean_object* v___x_4291_; 
v___x_4291_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4288_, v___y_4290_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
v_k_4170_ = v_a_4292_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
else
{
lean_dec_ref_known(v_value_4168_, 2);
lean_dec(v_fvarId_4167_);
return v___x_4291_;
}
}
}
case 6:
{
lean_object* v_a_4321_; lean_object* v_var_4322_; lean_object* v___x_4323_; lean_object* v_a_4324_; lean_object* v___x_4325_; lean_object* v_borrows_4326_; uint8_t v___x_4327_; 
v_a_4321_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4321_);
lean_dec_ref(v___x_4243_);
v_var_4322_ = lean_ctor_get(v_value_4168_, 1);
lean_inc(v_var_4322_);
v___x_4323_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4322_, v_a_4321_, v_a_4160_, v_a_4161_);
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref(v___x_4323_);
v___x_4325_ = lean_st_ref_get(v_a_4161_);
v_borrows_4326_ = lean_ctor_get(v___x_4325_, 1);
lean_inc_ref(v_borrows_4326_);
lean_dec(v___x_4325_);
v___x_4327_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4326_, v_fvarId_4167_);
lean_dec_ref(v_borrows_4326_);
if (v___x_4327_ == 0)
{
lean_object* v_varMap_4328_; lean_object* v___x_4329_; uint8_t v_isDefiniteRef_4330_; lean_object* v___x_4331_; uint8_t v___y_4333_; 
v_varMap_4328_ = lean_ctor_get(v_a_4160_, 3);
v___x_4329_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_4328_, v_fvarId_4167_);
v_isDefiniteRef_4330_ = lean_ctor_get_uint8(v___x_4329_, sizeof(void*)*2 + 1);
v___x_4331_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_4330_ == 0)
{
uint8_t v___x_4336_; 
v___x_4336_ = 1;
v___y_4333_ = v___x_4336_;
goto v___jp_4332_;
}
else
{
v___y_4333_ = v___x_4327_;
goto v___jp_4332_;
}
v___jp_4332_:
{
uint8_t v_persistent_4334_; lean_object* v___x_4335_; 
v_persistent_4334_ = lean_ctor_get_uint8(v___x_4329_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_4329_);
lean_inc(v_fvarId_4167_);
v___x_4335_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_4335_, 0, v_fvarId_4167_);
lean_ctor_set(v___x_4335_, 1, v___x_4331_);
lean_ctor_set(v___x_4335_, 2, v_a_4324_);
lean_ctor_set_uint8(v___x_4335_, sizeof(void*)*3, v___y_4333_);
lean_ctor_set_uint8(v___x_4335_, sizeof(void*)*3 + 1, v_persistent_4334_);
v_k_4208_ = v___x_4335_;
v___y_4209_ = v_a_4160_;
v___y_4210_ = v_a_4161_;
v___y_4211_ = v_a_4162_;
v___y_4212_ = v_a_4163_;
v___y_4213_ = v_a_4164_;
v___y_4214_ = v_a_4165_;
goto v___jp_4207_;
}
}
else
{
v_k_4208_ = v_a_4324_;
v___y_4209_ = v_a_4160_;
v___y_4210_ = v_a_4161_;
v___y_4211_ = v_a_4162_;
v___y_4212_ = v_a_4163_;
v___y_4213_ = v_a_4164_;
v___y_4214_ = v_a_4165_;
goto v___jp_4207_;
}
}
case 7:
{
lean_object* v_a_4337_; lean_object* v_var_4338_; lean_object* v___x_4339_; 
v_a_4337_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4337_);
lean_dec_ref(v___x_4243_);
v_var_4338_ = lean_ctor_get(v_value_4168_, 1);
lean_inc(v_var_4338_);
v___x_4339_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4338_, v_a_4337_, v_a_4160_, v_a_4161_);
if (lean_obj_tag(v_code_4157_) == 0)
{
lean_object* v_a_4340_; lean_object* v_decl_4341_; lean_object* v_k_4342_; size_t v___x_4343_; size_t v___x_4344_; uint8_t v___x_4345_; 
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
lean_inc(v_a_4340_);
lean_dec_ref(v___x_4339_);
v_decl_4341_ = lean_ctor_get(v_code_4157_, 0);
v_k_4342_ = lean_ctor_get(v_code_4157_, 1);
v___x_4343_ = lean_ptr_addr(v_k_4342_);
v___x_4344_ = lean_ptr_addr(v_a_4340_);
v___x_4345_ = lean_usize_dec_eq(v___x_4343_, v___x_4344_);
if (v___x_4345_ == 0)
{
lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4352_; 
v_isSharedCheck_4352_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4352_ == 0)
{
lean_object* v_unused_4353_; lean_object* v_unused_4354_; 
v_unused_4353_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4353_);
v_unused_4354_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4354_);
v___x_4347_ = v_code_4157_;
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
else
{
lean_dec(v_code_4157_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4350_; 
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 1, v_a_4340_);
lean_ctor_set(v___x_4347_, 0, v_decl_4158_);
v___x_4350_ = v___x_4347_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v_a_4340_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
v_k_4170_ = v___x_4350_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
else
{
size_t v___x_4355_; size_t v___x_4356_; uint8_t v___x_4357_; 
v___x_4355_ = lean_ptr_addr(v_decl_4341_);
v___x_4356_ = lean_ptr_addr(v_decl_4158_);
v___x_4357_ = lean_usize_dec_eq(v___x_4355_, v___x_4356_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
v_isSharedCheck_4364_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4364_ == 0)
{
lean_object* v_unused_4365_; lean_object* v_unused_4366_; 
v_unused_4365_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4365_);
v_unused_4366_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4366_);
v___x_4359_ = v_code_4157_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_dec(v_code_4157_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
lean_ctor_set(v___x_4359_, 1, v_a_4340_);
lean_ctor_set(v___x_4359_, 0, v_decl_4158_);
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v_a_4340_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
v_k_4170_ = v___x_4362_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
else
{
lean_dec(v_a_4340_);
lean_dec_ref(v_decl_4158_);
v_k_4170_ = v_code_4157_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
else
{
lean_object* v___x_4367_; lean_object* v___x_4368_; 
lean_dec_ref(v___x_4339_);
lean_dec_ref(v_decl_4158_);
lean_dec_ref(v_code_4157_);
v___x_4367_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4368_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4367_);
v_k_4170_ = v___x_4368_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
case 8:
{
lean_object* v_a_4369_; lean_object* v_var_4370_; lean_object* v___x_4371_; 
v_a_4369_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4369_);
lean_dec_ref(v___x_4243_);
v_var_4370_ = lean_ctor_get(v_value_4168_, 2);
lean_inc(v_var_4370_);
v___x_4371_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4370_, v_a_4369_, v_a_4160_, v_a_4161_);
if (lean_obj_tag(v_code_4157_) == 0)
{
lean_object* v_a_4372_; lean_object* v_decl_4373_; lean_object* v_k_4374_; size_t v___x_4375_; size_t v___x_4376_; uint8_t v___x_4377_; 
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_a_4372_);
lean_dec_ref(v___x_4371_);
v_decl_4373_ = lean_ctor_get(v_code_4157_, 0);
v_k_4374_ = lean_ctor_get(v_code_4157_, 1);
v___x_4375_ = lean_ptr_addr(v_k_4374_);
v___x_4376_ = lean_ptr_addr(v_a_4372_);
v___x_4377_ = lean_usize_dec_eq(v___x_4375_, v___x_4376_);
if (v___x_4377_ == 0)
{
lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
v_isSharedCheck_4384_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4384_ == 0)
{
lean_object* v_unused_4385_; lean_object* v_unused_4386_; 
v_unused_4385_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4385_);
v_unused_4386_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4386_);
v___x_4379_ = v_code_4157_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_dec(v_code_4157_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 1, v_a_4372_);
lean_ctor_set(v___x_4379_, 0, v_decl_4158_);
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4383_, 1, v_a_4372_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
v_k_4170_ = v___x_4382_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
else
{
size_t v___x_4387_; size_t v___x_4388_; uint8_t v___x_4389_; 
v___x_4387_ = lean_ptr_addr(v_decl_4373_);
v___x_4388_ = lean_ptr_addr(v_decl_4158_);
v___x_4389_ = lean_usize_dec_eq(v___x_4387_, v___x_4388_);
if (v___x_4389_ == 0)
{
lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
v_isSharedCheck_4396_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4396_ == 0)
{
lean_object* v_unused_4397_; lean_object* v_unused_4398_; 
v_unused_4397_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4397_);
v_unused_4398_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4398_);
v___x_4391_ = v_code_4157_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_dec(v_code_4157_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 1, v_a_4372_);
lean_ctor_set(v___x_4391_, 0, v_decl_4158_);
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4395_, 1, v_a_4372_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
v_k_4170_ = v___x_4394_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
else
{
lean_dec(v_a_4372_);
lean_dec_ref(v_decl_4158_);
v_k_4170_ = v_code_4157_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
else
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
lean_dec_ref(v___x_4371_);
lean_dec_ref(v_decl_4158_);
lean_dec_ref(v_code_4157_);
v___x_4399_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4400_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4399_);
v_k_4170_ = v___x_4400_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
case 9:
{
lean_object* v_a_4401_; lean_object* v_fn_4402_; lean_object* v_args_4403_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___x_4415_; 
v_a_4401_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4401_);
lean_dec_ref(v___x_4243_);
v_fn_4402_ = lean_ctor_get(v_value_4168_, 0);
v_args_4403_ = lean_ctor_get(v_value_4168_, 1);
lean_inc(v_fn_4402_);
v___x_4415_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_4402_, v_a_4165_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; uint8_t v___x_4417_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v_value_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; uint8_t v___y_4470_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; uint8_t v___y_4478_; uint8_t v___y_4479_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; uint8_t v___y_4490_; uint8_t v___y_4491_; uint8_t v___y_4492_; lean_object* v___y_4500_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4416_);
lean_dec_ref_known(v___x_4415_, 1);
v___x_4417_ = 1;
if (lean_obj_tag(v_a_4416_) == 0)
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10);
v___x_4517_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1(v___x_4516_);
v___y_4500_ = v___x_4517_;
goto v___jp_4499_;
}
else
{
lean_object* v_val_4518_; 
v_val_4518_ = lean_ctor_get(v_a_4416_, 0);
lean_inc(v_val_4518_);
lean_dec_ref_known(v_a_4416_, 1);
v___y_4500_ = v_val_4518_;
goto v___jp_4499_;
}
v___jp_4418_:
{
lean_object* v___x_4428_; 
v___x_4428_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_4417_, v_decl_4158_, v_value_4421_, v___y_4425_);
if (lean_obj_tag(v___x_4428_) == 0)
{
if (lean_obj_tag(v_code_4157_) == 0)
{
lean_object* v_a_4429_; lean_object* v_decl_4430_; lean_object* v_k_4431_; size_t v___x_4432_; size_t v___x_4433_; uint8_t v___x_4434_; 
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
lean_inc(v_a_4429_);
lean_dec_ref_known(v___x_4428_, 1);
v_decl_4430_ = lean_ctor_get(v_code_4157_, 0);
v_k_4431_ = lean_ctor_get(v_code_4157_, 1);
v___x_4432_ = lean_ptr_addr(v_k_4431_);
v___x_4433_ = lean_ptr_addr(v___y_4419_);
v___x_4434_ = lean_usize_dec_eq(v___x_4432_, v___x_4433_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
v_isSharedCheck_4441_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4441_ == 0)
{
lean_object* v_unused_4442_; lean_object* v_unused_4443_; 
v_unused_4442_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4442_);
v_unused_4443_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4443_);
v___x_4436_ = v_code_4157_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_dec(v_code_4157_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 1, v___y_4419_);
lean_ctor_set(v___x_4436_, 0, v_a_4429_);
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4429_);
lean_ctor_set(v_reuseFailAlloc_4440_, 1, v___y_4419_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
v___y_4405_ = v___y_4425_;
v___y_4406_ = v___y_4426_;
v___y_4407_ = v___y_4422_;
v___y_4408_ = v___y_4420_;
v___y_4409_ = v___y_4423_;
v___y_4410_ = v___y_4427_;
v___y_4411_ = v___y_4424_;
v___y_4412_ = v___x_4439_;
goto v___jp_4404_;
}
}
}
else
{
size_t v___x_4444_; size_t v___x_4445_; uint8_t v___x_4446_; 
v___x_4444_ = lean_ptr_addr(v_decl_4430_);
v___x_4445_ = lean_ptr_addr(v_a_4429_);
v___x_4446_ = lean_usize_dec_eq(v___x_4444_, v___x_4445_);
if (v___x_4446_ == 0)
{
lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
v_isSharedCheck_4453_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4453_ == 0)
{
lean_object* v_unused_4454_; lean_object* v_unused_4455_; 
v_unused_4454_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4454_);
v_unused_4455_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4455_);
v___x_4448_ = v_code_4157_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_dec(v_code_4157_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 1, v___y_4419_);
lean_ctor_set(v___x_4448_, 0, v_a_4429_);
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4429_);
lean_ctor_set(v_reuseFailAlloc_4452_, 1, v___y_4419_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
v___y_4405_ = v___y_4425_;
v___y_4406_ = v___y_4426_;
v___y_4407_ = v___y_4422_;
v___y_4408_ = v___y_4420_;
v___y_4409_ = v___y_4423_;
v___y_4410_ = v___y_4427_;
v___y_4411_ = v___y_4424_;
v___y_4412_ = v___x_4451_;
goto v___jp_4404_;
}
}
}
else
{
lean_dec(v_a_4429_);
lean_dec_ref(v___y_4419_);
v___y_4405_ = v___y_4425_;
v___y_4406_ = v___y_4426_;
v___y_4407_ = v___y_4422_;
v___y_4408_ = v___y_4420_;
v___y_4409_ = v___y_4423_;
v___y_4410_ = v___y_4427_;
v___y_4411_ = v___y_4424_;
v___y_4412_ = v_code_4157_;
goto v___jp_4404_;
}
}
}
else
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
lean_dec_ref_known(v___x_4428_, 1);
lean_dec_ref(v___y_4419_);
lean_dec_ref(v_code_4157_);
v___x_4456_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4457_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4456_);
v___y_4405_ = v___y_4425_;
v___y_4406_ = v___y_4426_;
v___y_4407_ = v___y_4422_;
v___y_4408_ = v___y_4420_;
v___y_4409_ = v___y_4423_;
v___y_4410_ = v___y_4427_;
v___y_4411_ = v___y_4424_;
v___y_4412_ = v___x_4457_;
goto v___jp_4404_;
}
}
else
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_dec_ref(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec_ref_known(v_value_4168_, 2);
lean_dec(v_fvarId_4167_);
lean_dec_ref(v_code_4157_);
v_a_4458_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4428_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4428_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
v___jp_4466_:
{
if (v___y_4470_ == 0)
{
lean_inc_ref(v_value_4168_);
v___y_4419_ = v___y_4467_;
v___y_4420_ = v___y_4468_;
v_value_4421_ = v_value_4168_;
v___y_4422_ = v_a_4160_;
v___y_4423_ = v_a_4161_;
v___y_4424_ = v_a_4162_;
v___y_4425_ = v_a_4163_;
v___y_4426_ = v_a_4164_;
v___y_4427_ = v_a_4165_;
goto v___jp_4418_;
}
else
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4471_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__3));
lean_inc_ref(v___y_4469_);
v___x_4472_ = l_Lean_Name_mkStr2(v___y_4469_, v___x_4471_);
lean_inc_ref(v_args_4403_);
v___x_4473_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4472_);
lean_ctor_set(v___x_4473_, 1, v_args_4403_);
v___y_4419_ = v___y_4467_;
v___y_4420_ = v___y_4468_;
v_value_4421_ = v___x_4473_;
v___y_4422_ = v_a_4160_;
v___y_4423_ = v_a_4161_;
v___y_4424_ = v_a_4162_;
v___y_4425_ = v_a_4163_;
v___y_4426_ = v_a_4164_;
v___y_4427_ = v_a_4165_;
goto v___jp_4418_;
}
}
v___jp_4474_:
{
if (v___y_4479_ == 0)
{
lean_object* v___x_4480_; lean_object* v___x_4481_; uint8_t v___x_4482_; 
v___x_4480_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__3));
lean_inc_ref(v___y_4477_);
v___x_4481_ = l_Lean_Name_mkStr2(v___y_4477_, v___x_4480_);
v___x_4482_ = lean_name_eq(v_fn_4402_, v___x_4481_);
lean_dec(v___x_4481_);
if (v___x_4482_ == 0)
{
v___y_4467_ = v___y_4475_;
v___y_4468_ = v___y_4476_;
v___y_4469_ = v___y_4477_;
v___y_4470_ = v___x_4482_;
goto v___jp_4466_;
}
else
{
v___y_4467_ = v___y_4475_;
v___y_4468_ = v___y_4476_;
v___y_4469_ = v___y_4477_;
v___y_4470_ = v___y_4478_;
goto v___jp_4466_;
}
}
else
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4483_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__4));
lean_inc_ref(v___y_4477_);
v___x_4484_ = l_Lean_Name_mkStr2(v___y_4477_, v___x_4483_);
lean_inc_ref(v_args_4403_);
v___x_4485_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
lean_ctor_set(v___x_4485_, 1, v_args_4403_);
v___y_4419_ = v___y_4475_;
v___y_4420_ = v___y_4476_;
v_value_4421_ = v___x_4485_;
v___y_4422_ = v_a_4160_;
v___y_4423_ = v_a_4161_;
v___y_4424_ = v_a_4162_;
v___y_4425_ = v_a_4163_;
v___y_4426_ = v_a_4164_;
v___y_4427_ = v_a_4165_;
goto v___jp_4418_;
}
}
v___jp_4486_:
{
if (v___y_4492_ == 0)
{
lean_object* v___x_4493_; lean_object* v___x_4494_; uint8_t v___x_4495_; 
v___x_4493_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__2));
lean_inc_ref(v___y_4489_);
v___x_4494_ = l_Lean_Name_mkStr2(v___y_4489_, v___x_4493_);
v___x_4495_ = lean_name_eq(v_fn_4402_, v___x_4494_);
lean_dec(v___x_4494_);
if (v___x_4495_ == 0)
{
v___y_4475_ = v___y_4487_;
v___y_4476_ = v___y_4488_;
v___y_4477_ = v___y_4489_;
v___y_4478_ = v___y_4491_;
v___y_4479_ = v___x_4495_;
goto v___jp_4474_;
}
else
{
v___y_4475_ = v___y_4487_;
v___y_4476_ = v___y_4488_;
v___y_4477_ = v___y_4489_;
v___y_4478_ = v___y_4491_;
v___y_4479_ = v___y_4490_;
goto v___jp_4474_;
}
}
else
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4496_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5));
lean_inc_ref(v___y_4489_);
v___x_4497_ = l_Lean_Name_mkStr2(v___y_4489_, v___x_4496_);
lean_inc_ref(v_args_4403_);
v___x_4498_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
lean_ctor_set(v___x_4498_, 1, v_args_4403_);
v___y_4419_ = v___y_4487_;
v___y_4420_ = v___y_4488_;
v_value_4421_ = v___x_4498_;
v___y_4422_ = v_a_4160_;
v___y_4423_ = v_a_4161_;
v___y_4424_ = v_a_4162_;
v___y_4425_ = v_a_4163_;
v___y_4426_ = v_a_4164_;
v___y_4427_ = v_a_4165_;
goto v___jp_4418_;
}
}
v___jp_4499_:
{
lean_object* v_params_4501_; lean_object* v___x_4502_; 
v_params_4501_ = lean_ctor_get(v___y_4500_, 3);
lean_inc_ref_n(v_params_4501_, 2);
lean_dec_ref(v___y_4500_);
v___x_4502_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(v_args_4403_, v_params_4501_, v_a_4401_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v_a_4503_; lean_object* v___x_4504_; lean_object* v_borrows_4505_; uint8_t v___x_4506_; lean_object* v___x_4507_; lean_object* v_borrows_4508_; uint8_t v___x_4509_; lean_object* v___x_4510_; lean_object* v_borrows_4511_; uint8_t v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; uint8_t v___x_4515_; 
v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc(v_a_4503_);
lean_dec_ref_known(v___x_4502_, 1);
v___x_4504_ = lean_st_ref_get(v_a_4161_);
v_borrows_4505_ = lean_ctor_get(v___x_4504_, 1);
lean_inc_ref(v_borrows_4505_);
lean_dec(v___x_4504_);
v___x_4506_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4505_, v_fvarId_4167_);
lean_dec_ref(v_borrows_4505_);
v___x_4507_ = lean_st_ref_get(v_a_4161_);
v_borrows_4508_ = lean_ctor_get(v___x_4507_, 1);
lean_inc_ref(v_borrows_4508_);
lean_dec(v___x_4507_);
v___x_4509_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4508_, v_fvarId_4167_);
lean_dec_ref(v_borrows_4508_);
v___x_4510_ = lean_st_ref_get(v_a_4161_);
v_borrows_4511_ = lean_ctor_get(v___x_4510_, 1);
lean_inc_ref(v_borrows_4511_);
lean_dec(v___x_4510_);
v___x_4512_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4511_, v_fvarId_4167_);
lean_dec_ref(v_borrows_4511_);
v___x_4513_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0));
v___x_4514_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6));
v___x_4515_ = lean_name_eq(v_fn_4402_, v___x_4514_);
if (v___x_4515_ == 0)
{
v___y_4487_ = v_a_4503_;
v___y_4488_ = v_params_4501_;
v___y_4489_ = v___x_4513_;
v___y_4490_ = v___x_4509_;
v___y_4491_ = v___x_4512_;
v___y_4492_ = v___x_4515_;
goto v___jp_4486_;
}
else
{
v___y_4487_ = v_a_4503_;
v___y_4488_ = v_params_4501_;
v___y_4489_ = v___x_4513_;
v___y_4490_ = v___x_4509_;
v___y_4491_ = v___x_4512_;
v___y_4492_ = v___x_4506_;
goto v___jp_4486_;
}
}
else
{
lean_dec_ref(v_params_4501_);
lean_dec_ref_known(v_value_4168_, 2);
lean_dec(v_fvarId_4167_);
lean_dec_ref(v_decl_4158_);
lean_dec_ref(v_code_4157_);
return v___x_4502_;
}
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec_ref_known(v_value_4168_, 2);
lean_dec(v_a_4401_);
lean_dec(v_fvarId_4167_);
lean_dec_ref(v_decl_4158_);
lean_dec_ref(v_code_4157_);
v_a_4519_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4415_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4415_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
v___jp_4404_:
{
lean_object* v___x_4413_; 
v___x_4413_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_4403_, v___y_4408_, v___y_4412_, v___y_4407_, v___y_4409_, v___y_4411_, v___y_4405_, v___y_4406_, v___y_4410_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref_known(v___x_4413_, 1);
v_k_4170_ = v_a_4414_;
v___y_4171_ = v___y_4407_;
v___y_4172_ = v___y_4409_;
v___y_4173_ = v___y_4411_;
v___y_4174_ = v___y_4405_;
v___y_4175_ = v___y_4406_;
v___y_4176_ = v___y_4410_;
goto v___jp_4169_;
}
else
{
lean_dec_ref_known(v_value_4168_, 2);
lean_dec(v_fvarId_4167_);
return v___x_4413_;
}
}
}
case 10:
{
lean_object* v_a_4527_; lean_object* v_args_4528_; lean_object* v___y_4530_; 
v_a_4527_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4527_);
lean_dec_ref(v___x_4243_);
v_args_4528_ = lean_ctor_get(v_value_4168_, 1);
if (lean_obj_tag(v_code_4157_) == 0)
{
lean_object* v_decl_4533_; lean_object* v_k_4534_; size_t v___x_4535_; size_t v___x_4536_; uint8_t v___x_4537_; 
v_decl_4533_ = lean_ctor_get(v_code_4157_, 0);
v_k_4534_ = lean_ctor_get(v_code_4157_, 1);
v___x_4535_ = lean_ptr_addr(v_k_4534_);
v___x_4536_ = lean_ptr_addr(v_a_4527_);
v___x_4537_ = lean_usize_dec_eq(v___x_4535_, v___x_4536_);
if (v___x_4537_ == 0)
{
lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
v_isSharedCheck_4544_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4544_ == 0)
{
lean_object* v_unused_4545_; lean_object* v_unused_4546_; 
v_unused_4545_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4545_);
v_unused_4546_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4546_);
v___x_4539_ = v_code_4157_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_dec(v_code_4157_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 1, v_a_4527_);
lean_ctor_set(v___x_4539_, 0, v_decl_4158_);
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4543_, 1, v_a_4527_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
v___y_4530_ = v___x_4542_;
goto v___jp_4529_;
}
}
}
else
{
size_t v___x_4547_; size_t v___x_4548_; uint8_t v___x_4549_; 
v___x_4547_ = lean_ptr_addr(v_decl_4533_);
v___x_4548_ = lean_ptr_addr(v_decl_4158_);
v___x_4549_ = lean_usize_dec_eq(v___x_4547_, v___x_4548_);
if (v___x_4549_ == 0)
{
lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
v_isSharedCheck_4556_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4556_ == 0)
{
lean_object* v_unused_4557_; lean_object* v_unused_4558_; 
v_unused_4557_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4557_);
v_unused_4558_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4558_);
v___x_4551_ = v_code_4157_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_dec(v_code_4157_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 1, v_a_4527_);
lean_ctor_set(v___x_4551_, 0, v_decl_4158_);
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4555_, 1, v_a_4527_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
v___y_4530_ = v___x_4554_;
goto v___jp_4529_;
}
}
}
else
{
lean_dec(v_a_4527_);
lean_dec_ref(v_decl_4158_);
v___y_4530_ = v_code_4157_;
goto v___jp_4529_;
}
}
}
else
{
lean_object* v___x_4559_; lean_object* v___x_4560_; 
lean_dec(v_a_4527_);
lean_dec_ref(v_decl_4158_);
lean_dec_ref(v_code_4157_);
v___x_4559_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4560_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4559_);
v___y_4530_ = v___x_4560_;
goto v___jp_4529_;
}
v___jp_4529_:
{
lean_object* v___x_4531_; 
v___x_4531_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4528_, v___y_4530_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref_known(v___x_4531_, 1);
v_k_4170_ = v_a_4532_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
else
{
lean_dec_ref_known(v_value_4168_, 2);
lean_dec(v_fvarId_4167_);
return v___x_4531_;
}
}
}
case 12:
{
lean_object* v_a_4561_; lean_object* v_args_4562_; lean_object* v___y_4564_; 
v_a_4561_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4561_);
lean_dec_ref(v___x_4243_);
v_args_4562_ = lean_ctor_get(v_value_4168_, 2);
if (lean_obj_tag(v_code_4157_) == 0)
{
lean_object* v_decl_4567_; lean_object* v_k_4568_; size_t v___x_4569_; size_t v___x_4570_; uint8_t v___x_4571_; 
v_decl_4567_ = lean_ctor_get(v_code_4157_, 0);
v_k_4568_ = lean_ctor_get(v_code_4157_, 1);
v___x_4569_ = lean_ptr_addr(v_k_4568_);
v___x_4570_ = lean_ptr_addr(v_a_4561_);
v___x_4571_ = lean_usize_dec_eq(v___x_4569_, v___x_4570_);
if (v___x_4571_ == 0)
{
lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
v_isSharedCheck_4578_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4578_ == 0)
{
lean_object* v_unused_4579_; lean_object* v_unused_4580_; 
v_unused_4579_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4579_);
v_unused_4580_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4580_);
v___x_4573_ = v_code_4157_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_dec(v_code_4157_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 1, v_a_4561_);
lean_ctor_set(v___x_4573_, 0, v_decl_4158_);
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4577_, 1, v_a_4561_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
v___y_4564_ = v___x_4576_;
goto v___jp_4563_;
}
}
}
else
{
size_t v___x_4581_; size_t v___x_4582_; uint8_t v___x_4583_; 
v___x_4581_ = lean_ptr_addr(v_decl_4567_);
v___x_4582_ = lean_ptr_addr(v_decl_4158_);
v___x_4583_ = lean_usize_dec_eq(v___x_4581_, v___x_4582_);
if (v___x_4583_ == 0)
{
lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
v_isSharedCheck_4590_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4590_ == 0)
{
lean_object* v_unused_4591_; lean_object* v_unused_4592_; 
v_unused_4591_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4591_);
v_unused_4592_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4592_);
v___x_4585_ = v_code_4157_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_dec(v_code_4157_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
lean_ctor_set(v___x_4585_, 1, v_a_4561_);
lean_ctor_set(v___x_4585_, 0, v_decl_4158_);
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4589_, 1, v_a_4561_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
v___y_4564_ = v___x_4588_;
goto v___jp_4563_;
}
}
}
else
{
lean_dec(v_a_4561_);
lean_dec_ref(v_decl_4158_);
v___y_4564_ = v_code_4157_;
goto v___jp_4563_;
}
}
}
else
{
lean_object* v___x_4593_; lean_object* v___x_4594_; 
lean_dec(v_a_4561_);
lean_dec_ref(v_decl_4158_);
lean_dec_ref(v_code_4157_);
v___x_4593_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4594_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4593_);
v___y_4564_ = v___x_4594_;
goto v___jp_4563_;
}
v___jp_4563_:
{
lean_object* v___x_4565_; 
v___x_4565_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4562_, v___y_4564_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v___x_4565_, 1);
v_k_4170_ = v_a_4566_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
else
{
lean_dec_ref_known(v_value_4168_, 3);
lean_dec(v_fvarId_4167_);
return v___x_4565_;
}
}
}
case 14:
{
lean_object* v_a_4595_; lean_object* v_fvarId_4596_; lean_object* v___x_4597_; 
v_a_4595_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4595_);
lean_dec_ref(v___x_4243_);
v_fvarId_4596_ = lean_ctor_get(v_value_4168_, 0);
lean_inc(v_fvarId_4596_);
v___x_4597_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_4596_, v_a_4595_, v_a_4160_, v_a_4161_);
if (lean_obj_tag(v_code_4157_) == 0)
{
lean_object* v_a_4598_; lean_object* v_decl_4599_; lean_object* v_k_4600_; size_t v___x_4601_; size_t v___x_4602_; uint8_t v___x_4603_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref(v___x_4597_);
v_decl_4599_ = lean_ctor_get(v_code_4157_, 0);
v_k_4600_ = lean_ctor_get(v_code_4157_, 1);
v___x_4601_ = lean_ptr_addr(v_k_4600_);
v___x_4602_ = lean_ptr_addr(v_a_4598_);
v___x_4603_ = lean_usize_dec_eq(v___x_4601_, v___x_4602_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4610_; 
v_isSharedCheck_4610_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4610_ == 0)
{
lean_object* v_unused_4611_; lean_object* v_unused_4612_; 
v_unused_4611_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4611_);
v_unused_4612_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4612_);
v___x_4605_ = v_code_4157_;
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
else
{
lean_dec(v_code_4157_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 1, v_a_4598_);
lean_ctor_set(v___x_4605_, 0, v_decl_4158_);
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4609_, 1, v_a_4598_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
v_k_4170_ = v___x_4608_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
else
{
size_t v___x_4613_; size_t v___x_4614_; uint8_t v___x_4615_; 
v___x_4613_ = lean_ptr_addr(v_decl_4599_);
v___x_4614_ = lean_ptr_addr(v_decl_4158_);
v___x_4615_ = lean_usize_dec_eq(v___x_4613_, v___x_4614_);
if (v___x_4615_ == 0)
{
lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
v_isSharedCheck_4622_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4622_ == 0)
{
lean_object* v_unused_4623_; lean_object* v_unused_4624_; 
v_unused_4623_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4623_);
v_unused_4624_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4624_);
v___x_4617_ = v_code_4157_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_dec(v_code_4157_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 1, v_a_4598_);
lean_ctor_set(v___x_4617_, 0, v_decl_4158_);
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_a_4598_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
v_k_4170_ = v___x_4620_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
else
{
lean_dec(v_a_4598_);
lean_dec_ref(v_decl_4158_);
v_k_4170_ = v_code_4157_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
else
{
lean_object* v___x_4625_; lean_object* v___x_4626_; 
lean_dec_ref(v___x_4597_);
lean_dec_ref(v_decl_4158_);
lean_dec_ref(v_code_4157_);
v___x_4625_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4626_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4625_);
v_k_4170_ = v___x_4626_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
case 15:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; 
lean_dec_ref(v___x_4243_);
lean_dec_ref(v_decl_4158_);
lean_dec_ref(v_code_4157_);
v___x_4627_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12);
v___x_4628_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v___x_4627_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc(v_a_4629_);
lean_dec_ref_known(v___x_4628_, 1);
v_k_4170_ = v_a_4629_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
else
{
lean_dec_ref_known(v_value_4168_, 1);
lean_dec(v_fvarId_4167_);
return v___x_4628_;
}
}
default: 
{
if (lean_obj_tag(v_code_4157_) == 0)
{
lean_object* v_a_4630_; lean_object* v_decl_4631_; lean_object* v_k_4632_; size_t v___x_4633_; size_t v___x_4634_; uint8_t v___x_4635_; 
v_a_4630_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4630_);
lean_dec_ref(v___x_4243_);
v_decl_4631_ = lean_ctor_get(v_code_4157_, 0);
v_k_4632_ = lean_ctor_get(v_code_4157_, 1);
v___x_4633_ = lean_ptr_addr(v_k_4632_);
v___x_4634_ = lean_ptr_addr(v_a_4630_);
v___x_4635_ = lean_usize_dec_eq(v___x_4633_, v___x_4634_);
if (v___x_4635_ == 0)
{
lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
v_isSharedCheck_4642_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4642_ == 0)
{
lean_object* v_unused_4643_; lean_object* v_unused_4644_; 
v_unused_4643_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4643_);
v_unused_4644_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4644_);
v___x_4637_ = v_code_4157_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_dec(v_code_4157_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4640_; 
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 1, v_a_4630_);
lean_ctor_set(v___x_4637_, 0, v_decl_4158_);
v___x_4640_ = v___x_4637_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4641_, 1, v_a_4630_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
v_k_4170_ = v___x_4640_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
else
{
size_t v___x_4645_; size_t v___x_4646_; uint8_t v___x_4647_; 
v___x_4645_ = lean_ptr_addr(v_decl_4631_);
v___x_4646_ = lean_ptr_addr(v_decl_4158_);
v___x_4647_ = lean_usize_dec_eq(v___x_4645_, v___x_4646_);
if (v___x_4647_ == 0)
{
lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4654_; 
v_isSharedCheck_4654_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4654_ == 0)
{
lean_object* v_unused_4655_; lean_object* v_unused_4656_; 
v_unused_4655_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4655_);
v_unused_4656_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4656_);
v___x_4649_ = v_code_4157_;
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
else
{
lean_dec(v_code_4157_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 1, v_a_4630_);
lean_ctor_set(v___x_4649_, 0, v_decl_4158_);
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4653_, 1, v_a_4630_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
v_k_4170_ = v___x_4652_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
else
{
lean_dec(v_a_4630_);
lean_dec_ref(v_decl_4158_);
v_k_4170_ = v_code_4157_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
else
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
lean_dec_ref(v___x_4243_);
lean_dec_ref(v_decl_4158_);
lean_dec_ref(v_code_4157_);
v___x_4657_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4658_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4657_);
v_k_4170_ = v___x_4658_;
v___y_4171_ = v_a_4160_;
v___y_4172_ = v_a_4161_;
v___y_4173_ = v_a_4162_;
v___y_4174_ = v_a_4163_;
v___y_4175_ = v_a_4164_;
v___y_4176_ = v_a_4165_;
goto v___jp_4169_;
}
}
}
v___jp_4169_:
{
lean_object* v___x_4177_; 
v___x_4177_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(v_value_4168_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4197_; 
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4197_ == 0)
{
lean_object* v_unused_4198_; 
v_unused_4198_ = lean_ctor_get(v___x_4177_, 0);
lean_dec(v_unused_4198_);
v___x_4179_ = v___x_4177_;
v_isShared_4180_ = v_isSharedCheck_4197_;
goto v_resetjp_4178_;
}
else
{
lean_dec(v___x_4177_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4197_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4181_; lean_object* v_vars_4182_; lean_object* v_borrows_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4196_; 
v___x_4181_ = lean_st_ref_take(v___y_4172_);
v_vars_4182_ = lean_ctor_get(v___x_4181_, 0);
v_borrows_4183_ = lean_ctor_get(v___x_4181_, 1);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4185_ = v___x_4181_;
v_isShared_4186_ = v_isSharedCheck_4196_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_borrows_4183_);
lean_inc(v_vars_4182_);
lean_dec(v___x_4181_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4196_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v_vars_4187_; lean_object* v_borrows_4188_; lean_object* v___x_4190_; 
v_vars_4187_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_vars_4182_, v_fvarId_4167_);
v_borrows_4188_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_borrows_4183_, v_fvarId_4167_);
lean_dec(v_fvarId_4167_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 1, v_borrows_4188_);
lean_ctor_set(v___x_4185_, 0, v_vars_4187_);
v___x_4190_ = v___x_4185_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_vars_4187_);
lean_ctor_set(v_reuseFailAlloc_4195_, 1, v_borrows_4188_);
v___x_4190_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
lean_object* v___x_4191_; lean_object* v___x_4193_; 
v___x_4191_ = lean_st_ref_put(v___y_4172_, v___x_4190_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 0, v_k_4170_);
v___x_4193_ = v___x_4179_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_k_4170_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
lean_dec_ref(v_k_4170_);
lean_dec(v_fvarId_4167_);
v_a_4199_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4177_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4177_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
v___jp_4207_:
{
if (lean_obj_tag(v_code_4157_) == 0)
{
lean_object* v_decl_4215_; lean_object* v_k_4216_; size_t v___x_4217_; size_t v___x_4218_; uint8_t v___x_4219_; 
v_decl_4215_ = lean_ctor_get(v_code_4157_, 0);
v_k_4216_ = lean_ctor_get(v_code_4157_, 1);
v___x_4217_ = lean_ptr_addr(v_k_4216_);
v___x_4218_ = lean_ptr_addr(v_k_4208_);
v___x_4219_ = lean_usize_dec_eq(v___x_4217_, v___x_4218_);
if (v___x_4219_ == 0)
{
lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
v_isSharedCheck_4226_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4226_ == 0)
{
lean_object* v_unused_4227_; lean_object* v_unused_4228_; 
v_unused_4227_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4227_);
v_unused_4228_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4228_);
v___x_4221_ = v_code_4157_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_dec(v_code_4157_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 1, v_k_4208_);
lean_ctor_set(v___x_4221_, 0, v_decl_4158_);
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_k_4208_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
v_k_4170_ = v___x_4224_;
v___y_4171_ = v___y_4209_;
v___y_4172_ = v___y_4210_;
v___y_4173_ = v___y_4211_;
v___y_4174_ = v___y_4212_;
v___y_4175_ = v___y_4213_;
v___y_4176_ = v___y_4214_;
goto v___jp_4169_;
}
}
}
else
{
size_t v___x_4229_; size_t v___x_4230_; uint8_t v___x_4231_; 
v___x_4229_ = lean_ptr_addr(v_decl_4215_);
v___x_4230_ = lean_ptr_addr(v_decl_4158_);
v___x_4231_ = lean_usize_dec_eq(v___x_4229_, v___x_4230_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
v_isSharedCheck_4238_ = !lean_is_exclusive(v_code_4157_);
if (v_isSharedCheck_4238_ == 0)
{
lean_object* v_unused_4239_; lean_object* v_unused_4240_; 
v_unused_4239_ = lean_ctor_get(v_code_4157_, 1);
lean_dec(v_unused_4239_);
v_unused_4240_ = lean_ctor_get(v_code_4157_, 0);
lean_dec(v_unused_4240_);
v___x_4233_ = v_code_4157_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_dec(v_code_4157_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 1, v_k_4208_);
lean_ctor_set(v___x_4233_, 0, v_decl_4158_);
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_decl_4158_);
lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_k_4208_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
v_k_4170_ = v___x_4236_;
v___y_4171_ = v___y_4209_;
v___y_4172_ = v___y_4210_;
v___y_4173_ = v___y_4211_;
v___y_4174_ = v___y_4212_;
v___y_4175_ = v___y_4213_;
v___y_4176_ = v___y_4214_;
goto v___jp_4169_;
}
}
}
else
{
lean_dec_ref(v_k_4208_);
lean_dec_ref(v_decl_4158_);
v_k_4170_ = v_code_4157_;
v___y_4171_ = v___y_4209_;
v___y_4172_ = v___y_4210_;
v___y_4173_ = v___y_4211_;
v___y_4174_ = v___y_4212_;
v___y_4175_ = v___y_4213_;
v___y_4176_ = v___y_4214_;
goto v___jp_4169_;
}
}
}
else
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
lean_dec_ref(v_k_4208_);
lean_dec_ref(v_decl_4158_);
lean_dec_ref(v_code_4157_);
v___x_4241_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4242_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4241_);
v_k_4170_ = v___x_4242_;
v___y_4171_ = v___y_4209_;
v___y_4172_ = v___y_4210_;
v___y_4173_ = v___y_4211_;
v___y_4174_ = v___y_4212_;
v___y_4175_ = v___y_4213_;
v___y_4176_ = v___y_4214_;
goto v___jp_4169_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_4157_ = stack[0].m_obj;
lean_object* v_decl_4158_ = stack[1].m_obj;
lean_object* v_k_4159_ = stack[2].m_obj;
lean_object* v_a_4160_ = stack[3].m_obj;
lean_object* v_a_4161_ = stack[4].m_obj;
lean_object* v_a_4162_ = stack[5].m_obj;
lean_object* v_a_4163_ = stack[6].m_obj;
lean_object* v_a_4164_ = stack[7].m_obj;
lean_object* v_a_4165_ = stack[8].m_obj;
lean_object* v_res_4659_;
v_res_4659_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(v_code_4157_, v_decl_4158_, v_k_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
stack->m_obj
 = v_res_4659_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___boxed(lean_object* v_code_4660_, lean_object* v_decl_4661_, lean_object* v_k_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_){
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(v_code_4660_, v_decl_4661_, v_k_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_);
lean_dec(v_a_4668_);
lean_dec_ref(v_a_4667_);
lean_dec(v_a_4666_);
lean_dec_ref(v_a_4665_);
lean_dec(v_a_4664_);
lean_dec_ref(v_a_4663_);
return v_res_4670_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0(void){
_start:
{
lean_object* v___x_4671_; 
v___x_4671_ = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___redArg();
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5(lean_object* v_msg_4672_){
_start:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4673_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0);
v___x_4674_ = lean_panic_fn_borrowed(v___x_4673_, v_msg_4672_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(lean_object* v_a_4675_, lean_object* v_b_4676_, lean_object* v_x_4677_){
_start:
{
if (lean_obj_tag(v_x_4677_) == 0)
{
lean_dec(v_b_4676_);
lean_dec(v_a_4675_);
return v_x_4677_;
}
else
{
lean_object* v_key_4678_; lean_object* v_value_4679_; lean_object* v_tail_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4692_; 
v_key_4678_ = lean_ctor_get(v_x_4677_, 0);
v_value_4679_ = lean_ctor_get(v_x_4677_, 1);
v_tail_4680_ = lean_ctor_get(v_x_4677_, 2);
v_isSharedCheck_4692_ = !lean_is_exclusive(v_x_4677_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4682_ = v_x_4677_;
v_isShared_4683_ = v_isSharedCheck_4692_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_tail_4680_);
lean_inc(v_value_4679_);
lean_inc(v_key_4678_);
lean_dec(v_x_4677_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4692_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
uint8_t v___x_4684_; 
v___x_4684_ = l_Lean_instBEqFVarId_beq(v_key_4678_, v_a_4675_);
if (v___x_4684_ == 0)
{
lean_object* v___x_4685_; lean_object* v___x_4687_; 
v___x_4685_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(v_a_4675_, v_b_4676_, v_tail_4680_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 2, v___x_4685_);
v___x_4687_ = v___x_4682_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_key_4678_);
lean_ctor_set(v_reuseFailAlloc_4688_, 1, v_value_4679_);
lean_ctor_set(v_reuseFailAlloc_4688_, 2, v___x_4685_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
else
{
lean_object* v___x_4690_; 
lean_dec(v_value_4679_);
lean_dec(v_key_4678_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 1, v_b_4676_);
lean_ctor_set(v___x_4682_, 0, v_a_4675_);
v___x_4690_ = v___x_4682_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_a_4675_);
lean_ctor_set(v_reuseFailAlloc_4691_, 1, v_b_4676_);
lean_ctor_set(v_reuseFailAlloc_4691_, 2, v_tail_4680_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(lean_object* v_m_4693_, lean_object* v_a_4694_, lean_object* v_b_4695_){
_start:
{
lean_object* v_size_4696_; lean_object* v_buckets_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4740_; 
v_size_4696_ = lean_ctor_get(v_m_4693_, 0);
v_buckets_4697_ = lean_ctor_get(v_m_4693_, 1);
v_isSharedCheck_4740_ = !lean_is_exclusive(v_m_4693_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4699_ = v_m_4693_;
v_isShared_4700_ = v_isSharedCheck_4740_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_buckets_4697_);
lean_inc(v_size_4696_);
lean_dec(v_m_4693_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4740_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4701_; uint64_t v___x_4702_; uint64_t v___x_4703_; uint64_t v___x_4704_; uint64_t v_fold_4705_; uint64_t v___x_4706_; uint64_t v___x_4707_; uint64_t v___x_4708_; size_t v___x_4709_; size_t v___x_4710_; size_t v___x_4711_; size_t v___x_4712_; size_t v___x_4713_; lean_object* v_bkt_4714_; uint8_t v___x_4715_; 
v___x_4701_ = lean_array_get_size(v_buckets_4697_);
v___x_4702_ = l_Lean_instHashableFVarId_hash(v_a_4694_);
v___x_4703_ = 32ULL;
v___x_4704_ = lean_uint64_shift_right(v___x_4702_, v___x_4703_);
v_fold_4705_ = lean_uint64_xor(v___x_4702_, v___x_4704_);
v___x_4706_ = 16ULL;
v___x_4707_ = lean_uint64_shift_right(v_fold_4705_, v___x_4706_);
v___x_4708_ = lean_uint64_xor(v_fold_4705_, v___x_4707_);
v___x_4709_ = lean_uint64_to_usize(v___x_4708_);
v___x_4710_ = lean_usize_of_nat(v___x_4701_);
v___x_4711_ = ((size_t)1ULL);
v___x_4712_ = lean_usize_sub(v___x_4710_, v___x_4711_);
v___x_4713_ = lean_usize_land(v___x_4709_, v___x_4712_);
v_bkt_4714_ = lean_array_uget_borrowed(v_buckets_4697_, v___x_4713_);
v___x_4715_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_4694_, v_bkt_4714_);
if (v___x_4715_ == 0)
{
lean_object* v___x_4716_; lean_object* v_size_x27_4717_; lean_object* v___x_4718_; lean_object* v_buckets_x27_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; uint8_t v___x_4725_; 
v___x_4716_ = lean_unsigned_to_nat(1u);
v_size_x27_4717_ = lean_nat_add(v_size_4696_, v___x_4716_);
lean_dec(v_size_4696_);
lean_inc(v_bkt_4714_);
v___x_4718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4718_, 0, v_a_4694_);
lean_ctor_set(v___x_4718_, 1, v_b_4695_);
lean_ctor_set(v___x_4718_, 2, v_bkt_4714_);
v_buckets_x27_4719_ = lean_array_uset(v_buckets_4697_, v___x_4713_, v___x_4718_);
v___x_4720_ = lean_unsigned_to_nat(4u);
v___x_4721_ = lean_nat_mul(v_size_x27_4717_, v___x_4720_);
v___x_4722_ = lean_unsigned_to_nat(3u);
v___x_4723_ = lean_nat_div(v___x_4721_, v___x_4722_);
lean_dec(v___x_4721_);
v___x_4724_ = lean_array_get_size(v_buckets_x27_4719_);
v___x_4725_ = lean_nat_dec_le(v___x_4723_, v___x_4724_);
lean_dec(v___x_4723_);
if (v___x_4725_ == 0)
{
lean_object* v_val_4726_; lean_object* v___x_4728_; 
v_val_4726_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(v_buckets_x27_4719_);
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 1, v_val_4726_);
lean_ctor_set(v___x_4699_, 0, v_size_x27_4717_);
v___x_4728_ = v___x_4699_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_size_x27_4717_);
lean_ctor_set(v_reuseFailAlloc_4729_, 1, v_val_4726_);
v___x_4728_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
return v___x_4728_;
}
}
else
{
lean_object* v___x_4731_; 
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 1, v_buckets_x27_4719_);
lean_ctor_set(v___x_4699_, 0, v_size_x27_4717_);
v___x_4731_ = v___x_4699_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_size_x27_4717_);
lean_ctor_set(v_reuseFailAlloc_4732_, 1, v_buckets_x27_4719_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
}
else
{
lean_object* v___x_4733_; lean_object* v_buckets_x27_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4738_; 
lean_inc(v_bkt_4714_);
v___x_4733_ = lean_box(0);
v_buckets_x27_4734_ = lean_array_uset(v_buckets_4697_, v___x_4713_, v___x_4733_);
v___x_4735_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(v_a_4694_, v_b_4695_, v_bkt_4714_);
v___x_4736_ = lean_array_uset(v_buckets_x27_4734_, v___x_4713_, v___x_4735_);
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 1, v___x_4736_);
v___x_4738_ = v___x_4699_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_size_4696_);
lean_ctor_set(v_reuseFailAlloc_4739_, 1, v___x_4736_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__2(lean_object* v_a_4741_, lean_object* v_a_4742_){
_start:
{
if (lean_obj_tag(v_a_4741_) == 0)
{
lean_object* v___x_4743_; 
v___x_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4743_, 0, v_a_4742_);
return v___x_4743_;
}
else
{
lean_object* v_key_4744_; lean_object* v_value_4745_; lean_object* v_tail_4746_; lean_object* v_r_4747_; 
v_key_4744_ = lean_ctor_get(v_a_4741_, 0);
lean_inc(v_key_4744_);
v_value_4745_ = lean_ctor_get(v_a_4741_, 1);
lean_inc(v_value_4745_);
v_tail_4746_ = lean_ctor_get(v_a_4741_, 2);
lean_inc(v_tail_4746_);
lean_dec_ref_known(v_a_4741_, 3);
v_r_4747_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(v_a_4742_, v_key_4744_, v_value_4745_);
v_a_4741_ = v_tail_4746_;
v_a_4742_ = v_r_4747_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(lean_object* v_as_4749_, size_t v_sz_4750_, size_t v_i_4751_, lean_object* v_b_4752_){
_start:
{
uint8_t v___x_4753_; 
v___x_4753_ = lean_usize_dec_lt(v_i_4751_, v_sz_4750_);
if (v___x_4753_ == 0)
{
return v_b_4752_;
}
else
{
lean_object* v_a_4754_; lean_object* v___x_4755_; 
v_a_4754_ = lean_array_uget_borrowed(v_as_4749_, v_i_4751_);
lean_inc(v_a_4754_);
v___x_4755_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__2(v_a_4754_, v_b_4752_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v_a_4756_; 
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
lean_inc(v_a_4756_);
lean_dec_ref_known(v___x_4755_, 1);
return v_a_4756_;
}
else
{
lean_object* v_a_4757_; size_t v___x_4758_; size_t v___x_4759_; 
v_a_4757_ = lean_ctor_get(v___x_4755_, 0);
lean_inc(v_a_4757_);
lean_dec_ref_known(v___x_4755_, 1);
v___x_4758_ = ((size_t)1ULL);
v___x_4759_ = lean_usize_add(v_i_4751_, v___x_4758_);
v_i_4751_ = v___x_4759_;
v_b_4752_ = v_a_4757_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4749_ = stack[0].m_obj;
size_t v_sz_4750_ = stack[1].m_num;
size_t v_i_4751_ = stack[2].m_num;
lean_object* v_b_4752_ = stack[3].m_obj;
lean_object* v_res_4761_;
v_res_4761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(v_as_4749_, v_sz_4750_, v_i_4751_, v_b_4752_);
stack->m_obj
 = v_res_4761_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3___boxed(lean_object* v_as_4762_, lean_object* v_sz_4763_, lean_object* v_i_4764_, lean_object* v_b_4765_){
_start:
{
size_t v_sz_boxed_4766_; size_t v_i_boxed_4767_; lean_object* v_res_4768_; 
v_sz_boxed_4766_ = lean_unbox_usize(v_sz_4763_);
lean_dec(v_sz_4763_);
v_i_boxed_4767_ = lean_unbox_usize(v_i_4764_);
lean_dec(v_i_4764_);
v_res_4768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(v_as_4762_, v_sz_boxed_4766_, v_i_boxed_4767_, v_b_4765_);
lean_dec_ref(v_as_4762_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(lean_object* v_m_4769_, lean_object* v_l_4770_){
_start:
{
lean_object* v_buckets_4771_; size_t v_sz_4772_; size_t v___x_4773_; lean_object* v___x_4774_; 
v_buckets_4771_ = lean_ctor_get(v_l_4770_, 1);
v_sz_4772_ = lean_array_size(v_buckets_4771_);
v___x_4773_ = ((size_t)0ULL);
v___x_4774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(v_buckets_4771_, v_sz_4772_, v___x_4773_, v_m_4769_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1___boxed(lean_object* v_m_4775_, lean_object* v_l_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_m_4775_, v_l_4776_);
lean_dec_ref(v_l_4776_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(lean_object* v_a_4778_, lean_object* v_a_4779_){
_start:
{
if (lean_obj_tag(v_a_4778_) == 0)
{
lean_object* v___x_4780_; 
v___x_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4780_, 0, v_a_4779_);
return v___x_4780_;
}
else
{
lean_object* v_key_4781_; lean_object* v_value_4782_; lean_object* v_tail_4783_; lean_object* v_r_4784_; 
v_key_4781_ = lean_ctor_get(v_a_4778_, 0);
lean_inc(v_key_4781_);
v_value_4782_ = lean_ctor_get(v_a_4778_, 1);
lean_inc(v_value_4782_);
v_tail_4783_ = lean_ctor_get(v_a_4778_, 2);
lean_inc(v_tail_4783_);
lean_dec_ref_known(v_a_4778_, 3);
v_r_4784_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_a_4779_, v_key_4781_, v_value_4782_);
v_a_4778_ = v_tail_4783_;
v_a_4779_ = v_r_4784_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(lean_object* v_as_4786_, size_t v_sz_4787_, size_t v_i_4788_, lean_object* v_b_4789_){
_start:
{
uint8_t v___x_4790_; 
v___x_4790_ = lean_usize_dec_lt(v_i_4788_, v_sz_4787_);
if (v___x_4790_ == 0)
{
return v_b_4789_;
}
else
{
lean_object* v_a_4791_; lean_object* v___x_4792_; 
v_a_4791_ = lean_array_uget_borrowed(v_as_4786_, v_i_4788_);
lean_inc(v_a_4791_);
v___x_4792_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(v_a_4791_, v_b_4789_);
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_object* v_a_4793_; 
v_a_4793_ = lean_ctor_get(v___x_4792_, 0);
lean_inc(v_a_4793_);
lean_dec_ref_known(v___x_4792_, 1);
return v_a_4793_;
}
else
{
lean_object* v_a_4794_; size_t v___x_4795_; size_t v___x_4796_; 
v_a_4794_ = lean_ctor_get(v___x_4792_, 0);
lean_inc(v_a_4794_);
lean_dec_ref_known(v___x_4792_, 1);
v___x_4795_ = ((size_t)1ULL);
v___x_4796_ = lean_usize_add(v_i_4788_, v___x_4795_);
v_i_4788_ = v___x_4796_;
v_b_4789_ = v_a_4794_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4786_ = stack[0].m_obj;
size_t v_sz_4787_ = stack[1].m_num;
size_t v_i_4788_ = stack[2].m_num;
lean_object* v_b_4789_ = stack[3].m_obj;
lean_object* v_res_4798_;
v_res_4798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_as_4786_, v_sz_4787_, v_i_4788_, v_b_4789_);
stack->m_obj
 = v_res_4798_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2___boxed(lean_object* v_as_4799_, lean_object* v_sz_4800_, lean_object* v_i_4801_, lean_object* v_b_4802_){
_start:
{
size_t v_sz_boxed_4803_; size_t v_i_boxed_4804_; lean_object* v_res_4805_; 
v_sz_boxed_4803_ = lean_unbox_usize(v_sz_4800_);
lean_dec(v_sz_4800_);
v_i_boxed_4804_ = lean_unbox_usize(v_i_4801_);
lean_dec(v_i_4801_);
v_res_4805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_as_4799_, v_sz_boxed_4803_, v_i_boxed_4804_, v_b_4802_);
lean_dec_ref(v_as_4799_);
return v_res_4805_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(lean_object* v_as_4806_, size_t v_i_4807_, size_t v_stop_4808_, lean_object* v_b_4809_){
_start:
{
lean_object* v___y_4811_; lean_object* v___y_4812_; uint8_t v___x_4817_; 
v___x_4817_ = lean_usize_dec_eq(v_i_4807_, v_stop_4808_);
if (v___x_4817_ == 0)
{
lean_object* v___x_4818_; lean_object* v_snd_4819_; lean_object* v_vars_4820_; lean_object* v_borrows_4821_; lean_object* v_vars_4822_; lean_object* v_borrows_4823_; lean_object* v___y_4825_; lean_object* v_size_4834_; lean_object* v_buckets_4835_; lean_object* v_size_4836_; uint8_t v___x_4837_; 
v___x_4818_ = lean_array_uget_borrowed(v_as_4806_, v_i_4807_);
v_snd_4819_ = lean_ctor_get(v___x_4818_, 1);
v_vars_4820_ = lean_ctor_get(v_b_4809_, 0);
lean_inc_ref(v_vars_4820_);
v_borrows_4821_ = lean_ctor_get(v_b_4809_, 1);
lean_inc_ref(v_borrows_4821_);
lean_dec_ref(v_b_4809_);
v_vars_4822_ = lean_ctor_get(v_snd_4819_, 0);
v_borrows_4823_ = lean_ctor_get(v_snd_4819_, 1);
v_size_4834_ = lean_ctor_get(v_vars_4820_, 0);
v_buckets_4835_ = lean_ctor_get(v_vars_4820_, 1);
v_size_4836_ = lean_ctor_get(v_vars_4822_, 0);
v___x_4837_ = lean_nat_dec_le(v_size_4834_, v_size_4836_);
if (v___x_4837_ == 0)
{
lean_object* v___x_4838_; 
v___x_4838_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_vars_4820_, v_vars_4822_);
v___y_4825_ = v___x_4838_;
goto v___jp_4824_;
}
else
{
size_t v_sz_4839_; size_t v___x_4840_; lean_object* v___x_4841_; 
lean_inc_ref(v_buckets_4835_);
lean_dec_ref(v_vars_4820_);
v_sz_4839_ = lean_array_size(v_buckets_4835_);
v___x_4840_ = ((size_t)0ULL);
lean_inc_ref(v_vars_4822_);
v___x_4841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_buckets_4835_, v_sz_4839_, v___x_4840_, v_vars_4822_);
lean_dec_ref(v_buckets_4835_);
v___y_4825_ = v___x_4841_;
goto v___jp_4824_;
}
v___jp_4824_:
{
lean_object* v_size_4826_; lean_object* v_buckets_4827_; lean_object* v_size_4828_; uint8_t v___x_4829_; 
v_size_4826_ = lean_ctor_get(v_borrows_4821_, 0);
v_buckets_4827_ = lean_ctor_get(v_borrows_4821_, 1);
v_size_4828_ = lean_ctor_get(v_borrows_4823_, 0);
v___x_4829_ = lean_nat_dec_le(v_size_4826_, v_size_4828_);
if (v___x_4829_ == 0)
{
lean_object* v___x_4830_; 
v___x_4830_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_borrows_4821_, v_borrows_4823_);
v___y_4811_ = v___y_4825_;
v___y_4812_ = v___x_4830_;
goto v___jp_4810_;
}
else
{
size_t v_sz_4831_; size_t v___x_4832_; lean_object* v___x_4833_; 
lean_inc_ref(v_buckets_4827_);
lean_dec_ref(v_borrows_4821_);
v_sz_4831_ = lean_array_size(v_buckets_4827_);
v___x_4832_ = ((size_t)0ULL);
lean_inc_ref(v_borrows_4823_);
v___x_4833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_buckets_4827_, v_sz_4831_, v___x_4832_, v_borrows_4823_);
lean_dec_ref(v_buckets_4827_);
v___y_4811_ = v___y_4825_;
v___y_4812_ = v___x_4833_;
goto v___jp_4810_;
}
}
}
else
{
return v_b_4809_;
}
v___jp_4810_:
{
lean_object* v___x_4813_; size_t v___x_4814_; size_t v___x_4815_; 
v___x_4813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4813_, 0, v___y_4811_);
lean_ctor_set(v___x_4813_, 1, v___y_4812_);
v___x_4814_ = ((size_t)1ULL);
v___x_4815_ = lean_usize_add(v_i_4807_, v___x_4814_);
v_i_4807_ = v___x_4815_;
v_b_4809_ = v___x_4813_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4806_ = stack[0].m_obj;
size_t v_i_4807_ = stack[1].m_num;
size_t v_stop_4808_ = stack[2].m_num;
lean_object* v_b_4809_ = stack[3].m_obj;
lean_object* v_res_4842_;
v_res_4842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_as_4806_, v_i_4807_, v_stop_4808_, v_b_4809_);
stack->m_obj
 = v_res_4842_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8___boxed(lean_object* v_as_4843_, lean_object* v_i_4844_, lean_object* v_stop_4845_, lean_object* v_b_4846_){
_start:
{
size_t v_i_boxed_4847_; size_t v_stop_boxed_4848_; lean_object* v_res_4849_; 
v_i_boxed_4847_ = lean_unbox_usize(v_i_4844_);
lean_dec(v_i_4844_);
v_stop_boxed_4848_ = lean_unbox_usize(v_stop_4845_);
lean_dec(v_stop_4845_);
v_res_4849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_as_4843_, v_i_boxed_4847_, v_stop_boxed_4848_, v_b_4846_);
lean_dec_ref(v_as_4843_);
return v_res_4849_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(lean_object* v_as_4850_, size_t v_i_4851_, size_t v_stop_4852_, lean_object* v_b_4853_){
_start:
{
lean_object* v___y_4855_; uint8_t v___x_4859_; 
v___x_4859_ = lean_usize_dec_eq(v_i_4851_, v_stop_4852_);
if (v___x_4859_ == 0)
{
lean_object* v_resetTargets_4860_; lean_object* v_unconditionalBorrows_4861_; lean_object* v_derivedValMap_4862_; lean_object* v_varMap_4863_; lean_object* v_jpLiveVarMap_4864_; lean_object* v_idx_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4886_; 
v_resetTargets_4860_ = lean_ctor_get(v_b_4853_, 0);
v_unconditionalBorrows_4861_ = lean_ctor_get(v_b_4853_, 1);
v_derivedValMap_4862_ = lean_ctor_get(v_b_4853_, 2);
v_varMap_4863_ = lean_ctor_get(v_b_4853_, 3);
v_jpLiveVarMap_4864_ = lean_ctor_get(v_b_4853_, 4);
v_idx_4865_ = lean_ctor_get(v_b_4853_, 5);
v_isSharedCheck_4886_ = !lean_is_exclusive(v_b_4853_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4867_ = v_b_4853_;
v_isShared_4868_ = v_isSharedCheck_4886_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_idx_4865_);
lean_inc(v_jpLiveVarMap_4864_);
lean_inc(v_varMap_4863_);
lean_inc(v_derivedValMap_4862_);
lean_inc(v_unconditionalBorrows_4861_);
lean_inc(v_resetTargets_4860_);
lean_dec(v_b_4853_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4886_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4869_; lean_object* v_fvarId_4870_; lean_object* v_type_4871_; uint8_t v_borrow_4872_; uint8_t v___x_4873_; uint8_t v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v_varMap_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v_ctx_4881_; 
v___x_4869_ = lean_array_uget_borrowed(v_as_4850_, v_i_4851_);
v_fvarId_4870_ = lean_ctor_get(v___x_4869_, 0);
v_type_4871_ = lean_ctor_get(v___x_4869_, 2);
v_borrow_4872_ = lean_ctor_get_uint8(v___x_4869_, sizeof(void*)*3);
v___x_4873_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_4871_);
v___x_4874_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_4871_);
v___x_4875_ = lean_box(0);
lean_inc(v_idx_4865_);
v___x_4876_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4876_, 0, v_idx_4865_);
lean_ctor_set(v___x_4876_, 1, v___x_4875_);
lean_ctor_set_uint8(v___x_4876_, sizeof(void*)*2, v___x_4873_);
lean_ctor_set_uint8(v___x_4876_, sizeof(void*)*2 + 1, v___x_4874_);
lean_ctor_set_uint8(v___x_4876_, sizeof(void*)*2 + 2, v___x_4859_);
lean_inc(v_fvarId_4870_);
v_varMap_4877_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_4870_, v___x_4876_, v_varMap_4863_);
v___x_4878_ = lean_unsigned_to_nat(1u);
v___x_4879_ = lean_nat_add(v_idx_4865_, v___x_4878_);
lean_dec(v_idx_4865_);
if (v_isShared_4868_ == 0)
{
lean_ctor_set(v___x_4867_, 5, v___x_4879_);
lean_ctor_set(v___x_4867_, 3, v_varMap_4877_);
v_ctx_4881_ = v___x_4867_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_resetTargets_4860_);
lean_ctor_set(v_reuseFailAlloc_4885_, 1, v_unconditionalBorrows_4861_);
lean_ctor_set(v_reuseFailAlloc_4885_, 2, v_derivedValMap_4862_);
lean_ctor_set(v_reuseFailAlloc_4885_, 3, v_varMap_4877_);
lean_ctor_set(v_reuseFailAlloc_4885_, 4, v_jpLiveVarMap_4864_);
lean_ctor_set(v_reuseFailAlloc_4885_, 5, v___x_4879_);
v_ctx_4881_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
lean_object* v___x_4882_; lean_object* v_ctx_4883_; 
v___x_4882_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
lean_inc(v_fvarId_4870_);
v_ctx_4883_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_4881_, v___x_4882_, v_fvarId_4870_);
if (v_borrow_4872_ == 0)
{
v___y_4855_ = v_ctx_4883_;
goto v___jp_4854_;
}
else
{
if (v___x_4873_ == 0)
{
v___y_4855_ = v_ctx_4883_;
goto v___jp_4854_;
}
else
{
lean_object* v___x_4884_; 
lean_inc(v_fvarId_4870_);
v___x_4884_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(v_ctx_4883_, v_fvarId_4870_);
v___y_4855_ = v___x_4884_;
goto v___jp_4854_;
}
}
}
}
}
else
{
return v_b_4853_;
}
v___jp_4854_:
{
size_t v___x_4856_; size_t v___x_4857_; 
v___x_4856_ = ((size_t)1ULL);
v___x_4857_ = lean_usize_add(v_i_4851_, v___x_4856_);
v_i_4851_ = v___x_4857_;
v_b_4853_ = v___y_4855_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4850_ = stack[0].m_obj;
size_t v_i_4851_ = stack[1].m_num;
size_t v_stop_4852_ = stack[2].m_num;
lean_object* v_b_4853_ = stack[3].m_obj;
lean_object* v_res_4887_;
v_res_4887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_as_4850_, v_i_4851_, v_stop_4852_, v_b_4853_);
stack->m_obj
 = v_res_4887_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3___boxed(lean_object* v_as_4888_, lean_object* v_i_4889_, lean_object* v_stop_4890_, lean_object* v_b_4891_){
_start:
{
size_t v_i_boxed_4892_; size_t v_stop_boxed_4893_; lean_object* v_res_4894_; 
v_i_boxed_4892_ = lean_unbox_usize(v_i_4889_);
lean_dec(v_i_4889_);
v_stop_boxed_4893_ = lean_unbox_usize(v_stop_4890_);
lean_dec(v_stop_4890_);
v_res_4894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_as_4888_, v_i_boxed_4892_, v_stop_boxed_4893_, v_b_4891_);
lean_dec_ref(v_as_4888_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4_spec__7(lean_object* v_msg_4895_){
_start:
{
lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4896_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
v___x_4897_ = lean_panic_fn_borrowed(v___x_4896_, v_msg_4895_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(lean_object* v_t_4898_, lean_object* v_k_4899_){
_start:
{
if (lean_obj_tag(v_t_4898_) == 0)
{
lean_object* v_k_4900_; lean_object* v_v_4901_; lean_object* v_l_4902_; lean_object* v_r_4903_; uint8_t v___x_4904_; 
v_k_4900_ = lean_ctor_get(v_t_4898_, 1);
v_v_4901_ = lean_ctor_get(v_t_4898_, 2);
v_l_4902_ = lean_ctor_get(v_t_4898_, 3);
v_r_4903_ = lean_ctor_get(v_t_4898_, 4);
v___x_4904_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4899_, v_k_4900_);
switch(v___x_4904_)
{
case 0:
{
v_t_4898_ = v_l_4902_;
goto _start;
}
case 1:
{
lean_inc(v_v_4901_);
return v_v_4901_;
}
default: 
{
v_t_4898_ = v_r_4903_;
goto _start;
}
}
}
else
{
lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4907_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3);
v___x_4908_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4_spec__7(v___x_4907_);
return v___x_4908_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4___boxed(lean_object* v_t_4909_, lean_object* v_k_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(v_t_4909_, v_k_4910_);
lean_dec(v_k_4910_);
lean_dec(v_t_4909_);
return v_res_4911_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(lean_object* v_discr_4912_, size_t v_sz_4913_, size_t v_i_4914_, lean_object* v_bs_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_){
_start:
{
uint8_t v___x_4923_; 
v___x_4923_ = lean_usize_dec_lt(v_i_4914_, v_sz_4913_);
if (v___x_4923_ == 0)
{
lean_object* v___x_4924_; 
lean_dec(v_discr_4912_);
v___x_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4924_, 0, v_bs_4915_);
return v___x_4924_;
}
else
{
lean_object* v_v_4925_; lean_object* v_fst_4926_; lean_object* v_snd_4927_; lean_object* v___x_4928_; lean_object* v_bs_x27_4929_; lean_object* v_a_4931_; 
v_v_4925_ = lean_array_uget_borrowed(v_bs_4915_, v_i_4914_);
v_fst_4926_ = lean_ctor_get(v_v_4925_, 0);
lean_inc(v_fst_4926_);
v_snd_4927_ = lean_ctor_get(v_v_4925_, 1);
lean_inc(v_snd_4927_);
v___x_4928_ = lean_unsigned_to_nat(0u);
v_bs_x27_4929_ = lean_array_uset(v_bs_4915_, v_i_4914_, v___x_4928_);
if (lean_obj_tag(v_fst_4926_) == 1)
{
lean_object* v_info_4936_; lean_object* v_code_4937_; lean_object* v_resetTargets_4938_; lean_object* v_unconditionalBorrows_4939_; lean_object* v_derivedValMap_4940_; lean_object* v_varMap_4941_; lean_object* v_jpLiveVarMap_4942_; lean_object* v_idx_4943_; lean_object* v___y_4945_; lean_object* v___x_4960_; 
v_info_4936_ = lean_ctor_get(v_fst_4926_, 0);
v_code_4937_ = lean_ctor_get(v_fst_4926_, 1);
v_resetTargets_4938_ = lean_ctor_get(v___y_4916_, 0);
v_unconditionalBorrows_4939_ = lean_ctor_get(v___y_4916_, 1);
v_derivedValMap_4940_ = lean_ctor_get(v___y_4916_, 2);
v_varMap_4941_ = lean_ctor_get(v___y_4916_, 3);
v_jpLiveVarMap_4942_ = lean_ctor_get(v___y_4916_, 4);
v_idx_4943_ = lean_ctor_get(v___y_4916_, 5);
v___x_4960_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_varMap_4941_, v_discr_4912_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_inc(v_varMap_4941_);
v___y_4945_ = v_varMap_4941_;
goto v___jp_4944_;
}
else
{
lean_object* v_val_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4982_; 
v_val_4961_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4963_ = v___x_4960_;
v_isShared_4964_ = v_isSharedCheck_4982_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_val_4961_);
lean_dec(v___x_4960_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4982_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
uint8_t v_persistent_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4979_; 
v_persistent_4965_ = lean_ctor_get_uint8(v_val_4961_, sizeof(void*)*2 + 2);
v_isSharedCheck_4979_ = !lean_is_exclusive(v_val_4961_);
if (v_isSharedCheck_4979_ == 0)
{
lean_object* v_unused_4980_; lean_object* v_unused_4981_; 
v_unused_4980_ = lean_ctor_get(v_val_4961_, 1);
lean_dec(v_unused_4980_);
v_unused_4981_ = lean_ctor_get(v_val_4961_, 0);
lean_dec(v_unused_4981_);
v___x_4967_ = v_val_4961_;
v_isShared_4968_ = v_isSharedCheck_4979_;
goto v_resetjp_4966_;
}
else
{
lean_dec(v_val_4961_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4979_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
uint8_t v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4973_; 
v___x_4969_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_info_4936_);
v___x_4970_ = lean_unsigned_to_nat(1u);
v___x_4971_ = lean_nat_add(v_idx_4943_, v___x_4970_);
lean_inc_ref(v_info_4936_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 0, v_info_4936_);
v___x_4973_ = v___x_4963_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_info_4936_);
v___x_4973_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
lean_object* v___x_4975_; 
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 1, v___x_4973_);
lean_ctor_set(v___x_4967_, 0, v___x_4971_);
v___x_4975_ = v___x_4967_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v___x_4971_);
lean_ctor_set(v_reuseFailAlloc_4977_, 1, v___x_4973_);
lean_ctor_set_uint8(v_reuseFailAlloc_4977_, sizeof(void*)*2 + 2, v_persistent_4965_);
v___x_4975_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
lean_object* v___x_4976_; 
lean_ctor_set_uint8(v___x_4975_, sizeof(void*)*2, v___x_4969_);
lean_ctor_set_uint8(v___x_4975_, sizeof(void*)*2 + 1, v___x_4969_);
lean_inc(v_varMap_4941_);
lean_inc(v_discr_4912_);
v___x_4976_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_4912_, v___x_4975_, v_varMap_4941_);
v___y_4945_ = v___x_4976_;
goto v___jp_4944_;
}
}
}
}
}
v___jp_4944_:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; 
v___x_4946_ = lean_unsigned_to_nat(1u);
v___x_4947_ = lean_nat_add(v_idx_4943_, v___x_4946_);
lean_inc(v_jpLiveVarMap_4942_);
lean_inc(v_derivedValMap_4940_);
lean_inc(v_unconditionalBorrows_4939_);
lean_inc_ref(v_resetTargets_4938_);
v___x_4948_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4948_, 0, v_resetTargets_4938_);
lean_ctor_set(v___x_4948_, 1, v_unconditionalBorrows_4939_);
lean_ctor_set(v___x_4948_, 2, v_derivedValMap_4940_);
lean_ctor_set(v___x_4948_, 3, v___y_4945_);
lean_ctor_set(v___x_4948_, 4, v_jpLiveVarMap_4942_);
lean_ctor_set(v___x_4948_, 5, v___x_4947_);
lean_inc_ref(v_code_4937_);
v___x_4949_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_snd_4927_, v_code_4937_, v___x_4948_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_);
lean_dec_ref_known(v___x_4948_, 6);
lean_dec(v_snd_4927_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v_a_4950_; lean_object* v___x_4951_; 
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
lean_inc(v_a_4950_);
lean_dec_ref_known(v___x_4949_, 1);
v___x_4951_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_fst_4926_, v_a_4950_);
v_a_4931_ = v___x_4951_;
goto v___jp_4930_;
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
lean_dec_ref_known(v_fst_4926_, 2);
lean_dec_ref(v_bs_x27_4929_);
lean_dec(v_discr_4912_);
v_a_4952_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4949_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4949_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4955_ == 0)
{
v___x_4957_ = v___x_4954_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
}
}
else
{
lean_object* v_code_4983_; lean_object* v___x_4984_; 
v_code_4983_ = lean_ctor_get(v_fst_4926_, 0);
lean_inc_ref(v_code_4983_);
v___x_4984_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_snd_4927_, v_code_4983_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_);
lean_dec(v_snd_4927_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v_a_4985_; lean_object* v___x_4986_; 
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
lean_inc(v_a_4985_);
lean_dec_ref_known(v___x_4984_, 1);
v___x_4986_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_fst_4926_, v_a_4985_);
v_a_4931_ = v___x_4986_;
goto v___jp_4930_;
}
else
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4994_; 
lean_dec_ref_known(v_fst_4926_, 1);
lean_dec_ref(v_bs_x27_4929_);
lean_dec(v_discr_4912_);
v_a_4987_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4989_ = v___x_4984_;
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4984_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4992_; 
if (v_isShared_4990_ == 0)
{
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4987_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
}
v___jp_4930_:
{
size_t v___x_4932_; size_t v___x_4933_; lean_object* v___x_4934_; 
v___x_4932_ = ((size_t)1ULL);
v___x_4933_ = lean_usize_add(v_i_4914_, v___x_4932_);
v___x_4934_ = lean_array_uset(v_bs_x27_4929_, v_i_4914_, v_a_4931_);
v_i_4914_ = v___x_4933_;
v_bs_4915_ = v___x_4934_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_4912_ = stack[0].m_obj;
size_t v_sz_4913_ = stack[1].m_num;
size_t v_i_4914_ = stack[2].m_num;
lean_object* v_bs_4915_ = stack[3].m_obj;
lean_object* v___y_4916_ = stack[4].m_obj;
lean_object* v___y_4917_ = stack[5].m_obj;
lean_object* v___y_4918_ = stack[6].m_obj;
lean_object* v___y_4919_ = stack[7].m_obj;
lean_object* v___y_4920_ = stack[8].m_obj;
lean_object* v___y_4921_ = stack[9].m_obj;
lean_object* v_res_4995_;
v_res_4995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(v_discr_4912_, v_sz_4913_, v_i_4914_, v_bs_4915_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_);
stack->m_obj
 = v_res_4995_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7___boxed(lean_object* v_discr_4996_, lean_object* v_sz_4997_, lean_object* v_i_4998_, lean_object* v_bs_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
size_t v_sz_boxed_5007_; size_t v_i_boxed_5008_; lean_object* v_res_5009_; 
v_sz_boxed_5007_ = lean_unbox_usize(v_sz_4997_);
lean_dec(v_sz_4997_);
v_i_boxed_5008_ = lean_unbox_usize(v_i_4998_);
lean_dec(v_i_4998_);
v_res_5009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(v_discr_4996_, v_sz_boxed_5007_, v_i_boxed_5008_, v_bs_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_);
lean_dec(v___y_5005_);
lean_dec_ref(v___y_5004_);
lean_dec(v___y_5003_);
lean_dec_ref(v___y_5002_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
return v_res_5009_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1(void){
_start:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v___x_5011_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_5012_ = lean_unsigned_to_nat(59u);
v___x_5013_ = lean_unsigned_to_nat(655u);
v___x_5014_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__0));
v___x_5015_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_5016_ = l_mkPanicMessageWithDecl(v___x_5015_, v___x_5014_, v___x_5013_, v___x_5012_, v___x_5011_);
return v___x_5016_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(lean_object* v_code_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_){
_start:
{
switch(lean_obj_tag(v_code_5017_))
{
case 0:
{
lean_object* v_decl_5025_; lean_object* v_k_5026_; lean_object* v_fvarId_5027_; lean_object* v_type_5028_; lean_object* v_value_5029_; lean_object* v___y_5031_; 
v_decl_5025_ = lean_ctor_get(v_code_5017_, 0);
lean_inc_ref(v_decl_5025_);
v_k_5026_ = lean_ctor_get(v_code_5017_, 1);
v_fvarId_5027_ = lean_ctor_get(v_decl_5025_, 0);
v_type_5028_ = lean_ctor_get(v_decl_5025_, 2);
v_value_5029_ = lean_ctor_get(v_decl_5025_, 3);
if (lean_obj_tag(v_value_5029_) == 5)
{
lean_object* v_i_5050_; lean_object* v___x_5051_; 
v_i_5050_ = lean_ctor_get(v_value_5029_, 0);
lean_inc_ref(v_i_5050_);
v___x_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5051_, 0, v_i_5050_);
v___y_5031_ = v___x_5051_;
goto v___jp_5030_;
}
else
{
lean_object* v___x_5052_; 
v___x_5052_ = lean_box(0);
v___y_5031_ = v___x_5052_;
goto v___jp_5030_;
}
v___jp_5030_:
{
lean_object* v_resetTargets_5032_; lean_object* v_unconditionalBorrows_5033_; lean_object* v_derivedValMap_5034_; lean_object* v_varMap_5035_; lean_object* v_jpLiveVarMap_5036_; lean_object* v_idx_5037_; uint8_t v___x_5038_; uint8_t v___x_5039_; uint8_t v___x_5040_; lean_object* v_varInfo_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v_ctx_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
v_resetTargets_5032_ = lean_ctor_get(v_a_5018_, 0);
v_unconditionalBorrows_5033_ = lean_ctor_get(v_a_5018_, 1);
v_derivedValMap_5034_ = lean_ctor_get(v_a_5018_, 2);
v_varMap_5035_ = lean_ctor_get(v_a_5018_, 3);
v_jpLiveVarMap_5036_ = lean_ctor_get(v_a_5018_, 4);
v_idx_5037_ = lean_ctor_get(v_a_5018_, 5);
v___x_5038_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_5028_);
v___x_5039_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_5028_);
v___x_5040_ = l_Lean_Compiler_LCNF_LetValue_isPersistent(v_value_5029_);
lean_inc(v_idx_5037_);
v_varInfo_5041_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_varInfo_5041_, 0, v_idx_5037_);
lean_ctor_set(v_varInfo_5041_, 1, v___y_5031_);
lean_ctor_set_uint8(v_varInfo_5041_, sizeof(void*)*2, v___x_5038_);
lean_ctor_set_uint8(v_varInfo_5041_, sizeof(void*)*2 + 1, v___x_5039_);
lean_ctor_set_uint8(v_varInfo_5041_, sizeof(void*)*2 + 2, v___x_5040_);
lean_inc(v_varMap_5035_);
lean_inc(v_fvarId_5027_);
v___x_5042_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_5027_, v_varInfo_5041_, v_varMap_5035_);
v___x_5043_ = lean_unsigned_to_nat(1u);
v___x_5044_ = lean_nat_add(v_idx_5037_, v___x_5043_);
lean_inc(v_jpLiveVarMap_5036_);
lean_inc(v_derivedValMap_5034_);
lean_inc(v_unconditionalBorrows_5033_);
lean_inc_ref(v_resetTargets_5032_);
v_ctx_5045_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_ctx_5045_, 0, v_resetTargets_5032_);
lean_ctor_set(v_ctx_5045_, 1, v_unconditionalBorrows_5033_);
lean_ctor_set(v_ctx_5045_, 2, v_derivedValMap_5034_);
lean_ctor_set(v_ctx_5045_, 3, v___x_5042_);
lean_ctor_set(v_ctx_5045_, 4, v_jpLiveVarMap_5036_);
lean_ctor_set(v_ctx_5045_, 5, v___x_5044_);
lean_inc_ref(v_decl_5025_);
v___x_5046_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(v_ctx_5045_, v_decl_5025_);
lean_inc_ref(v_k_5026_);
v___x_5047_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5026_, v___x_5046_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; lean_object* v___x_5049_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
lean_inc(v_a_5048_);
lean_dec_ref_known(v___x_5047_, 1);
v___x_5049_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(v_code_5017_, v_decl_5025_, v_a_5048_, v___x_5046_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
lean_dec_ref(v___x_5046_);
return v___x_5049_;
}
else
{
lean_dec_ref(v___x_5046_);
lean_dec_ref(v_decl_5025_);
lean_dec_ref_known(v_code_5017_, 2);
return v___x_5047_;
}
}
}
case 2:
{
lean_object* v_decl_5053_; lean_object* v_k_5054_; lean_object* v_fst_5056_; lean_object* v_snd_5057_; lean_object* v_params_5106_; lean_object* v_type_5107_; lean_object* v_value_5108_; uint8_t v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; uint8_t v___x_5112_; 
v_decl_5053_ = lean_ctor_get(v_code_5017_, 0);
v_k_5054_ = lean_ctor_get(v_code_5017_, 1);
v_params_5106_ = lean_ctor_get(v_decl_5053_, 2);
v_type_5107_ = lean_ctor_get(v_decl_5053_, 3);
v_value_5108_ = lean_ctor_get(v_decl_5053_, 4);
v___x_5109_ = 1;
v___x_5110_ = lean_unsigned_to_nat(0u);
v___x_5111_ = lean_array_get_size(v_params_5106_);
v___x_5112_ = lean_nat_dec_lt(v___x_5110_, v___x_5111_);
if (v___x_5112_ == 0)
{
lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; 
v___x_5113_ = lean_st_ref_get(v_a_5019_);
v___x_5114_ = lean_st_ref_take(v_a_5019_);
lean_dec(v___x_5114_);
v___x_5115_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5116_ = lean_st_ref_put(v_a_5019_, v___x_5115_);
lean_inc_ref(v_value_5108_);
v___x_5117_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_value_5108_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v_a_5118_; lean_object* v___x_5119_; 
v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
lean_inc(v_a_5118_);
lean_dec_ref_known(v___x_5117_, 1);
v___x_5119_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5106_, v_a_5118_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v_a_5120_; lean_object* v___x_5121_; 
v_a_5120_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_a_5120_);
lean_dec_ref_known(v___x_5119_, 1);
lean_inc_ref(v_params_5106_);
lean_inc_ref(v_type_5107_);
lean_inc_ref(v_decl_5053_);
v___x_5121_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5109_, v_decl_5053_, v_type_5107_, v_params_5106_, v_a_5120_, v_a_5021_);
if (lean_obj_tag(v___x_5121_) == 0)
{
lean_object* v_a_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
v_a_5122_ = lean_ctor_get(v___x_5121_, 0);
lean_inc(v_a_5122_);
lean_dec_ref_known(v___x_5121_, 1);
v___x_5123_ = lean_st_ref_get(v_a_5019_);
v___x_5124_ = lean_st_ref_take(v_a_5019_);
lean_dec(v___x_5124_);
v___x_5125_ = lean_st_ref_put(v_a_5019_, v___x_5113_);
v_fst_5056_ = v_a_5122_;
v_snd_5057_ = v___x_5123_;
goto v___jp_5055_;
}
else
{
lean_object* v_a_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5133_; 
lean_dec(v___x_5113_);
lean_dec_ref_known(v_code_5017_, 2);
v_a_5126_ = lean_ctor_get(v___x_5121_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5121_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5128_ = v___x_5121_;
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_a_5126_);
lean_dec(v___x_5121_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5131_; 
if (v_isShared_5129_ == 0)
{
v___x_5131_ = v___x_5128_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5126_);
v___x_5131_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
return v___x_5131_;
}
}
}
}
else
{
lean_dec(v___x_5113_);
lean_dec_ref_known(v_code_5017_, 2);
return v___x_5119_;
}
}
else
{
lean_dec(v___x_5113_);
lean_dec_ref_known(v_code_5017_, 2);
return v___x_5117_;
}
}
else
{
size_t v___x_5134_; size_t v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; 
v___x_5134_ = ((size_t)0ULL);
v___x_5135_ = lean_usize_of_nat(v___x_5111_);
lean_inc_ref(v_a_5018_);
v___x_5136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_params_5106_, v___x_5134_, v___x_5135_, v_a_5018_);
v___x_5137_ = lean_st_ref_get(v_a_5019_);
v___x_5138_ = lean_st_ref_take(v_a_5019_);
lean_dec(v___x_5138_);
v___x_5139_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5140_ = lean_st_ref_put(v_a_5019_, v___x_5139_);
lean_inc_ref(v_value_5108_);
v___x_5141_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_value_5108_, v___x_5136_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_object* v_a_5142_; lean_object* v___x_5143_; 
v_a_5142_ = lean_ctor_get(v___x_5141_, 0);
lean_inc(v_a_5142_);
lean_dec_ref_known(v___x_5141_, 1);
v___x_5143_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5106_, v_a_5142_, v___x_5136_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
lean_dec_ref(v___x_5136_);
if (lean_obj_tag(v___x_5143_) == 0)
{
lean_object* v_a_5144_; lean_object* v___x_5145_; 
v_a_5144_ = lean_ctor_get(v___x_5143_, 0);
lean_inc(v_a_5144_);
lean_dec_ref_known(v___x_5143_, 1);
lean_inc_ref(v_params_5106_);
lean_inc_ref(v_type_5107_);
lean_inc_ref(v_decl_5053_);
v___x_5145_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_5109_, v_decl_5053_, v_type_5107_, v_params_5106_, v_a_5144_, v_a_5021_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; 
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5146_);
lean_dec_ref_known(v___x_5145_, 1);
v___x_5147_ = lean_st_ref_get(v_a_5019_);
v___x_5148_ = lean_st_ref_take(v_a_5019_);
lean_dec(v___x_5148_);
v___x_5149_ = lean_st_ref_put(v_a_5019_, v___x_5137_);
v_fst_5056_ = v_a_5146_;
v_snd_5057_ = v___x_5147_;
goto v___jp_5055_;
}
else
{
lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5157_; 
lean_dec(v___x_5137_);
lean_dec_ref_known(v_code_5017_, 2);
v_a_5150_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5152_ = v___x_5145_;
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v___x_5145_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5155_; 
if (v_isShared_5153_ == 0)
{
v___x_5155_ = v___x_5152_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v_a_5150_);
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
lean_dec(v___x_5137_);
lean_dec_ref_known(v_code_5017_, 2);
return v___x_5143_;
}
}
else
{
lean_dec(v___x_5137_);
lean_dec_ref(v___x_5136_);
lean_dec_ref_known(v_code_5017_, 2);
return v___x_5141_;
}
}
v___jp_5055_:
{
lean_object* v_fvarId_5058_; lean_object* v_resetTargets_5059_; lean_object* v_unconditionalBorrows_5060_; lean_object* v_derivedValMap_5061_; lean_object* v_varMap_5062_; lean_object* v_jpLiveVarMap_5063_; lean_object* v_idx_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v_fvarId_5058_ = lean_ctor_get(v_fst_5056_, 0);
v_resetTargets_5059_ = lean_ctor_get(v_a_5018_, 0);
v_unconditionalBorrows_5060_ = lean_ctor_get(v_a_5018_, 1);
v_derivedValMap_5061_ = lean_ctor_get(v_a_5018_, 2);
v_varMap_5062_ = lean_ctor_get(v_a_5018_, 3);
v_jpLiveVarMap_5063_ = lean_ctor_get(v_a_5018_, 4);
v_idx_5064_ = lean_ctor_get(v_a_5018_, 5);
lean_inc(v_jpLiveVarMap_5063_);
lean_inc(v_fvarId_5058_);
v___x_5065_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_5058_, v_snd_5057_, v_jpLiveVarMap_5063_);
lean_inc(v_idx_5064_);
lean_inc(v_varMap_5062_);
lean_inc(v_derivedValMap_5061_);
lean_inc(v_unconditionalBorrows_5060_);
lean_inc_ref(v_resetTargets_5059_);
v___x_5066_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5066_, 0, v_resetTargets_5059_);
lean_ctor_set(v___x_5066_, 1, v_unconditionalBorrows_5060_);
lean_ctor_set(v___x_5066_, 2, v_derivedValMap_5061_);
lean_ctor_set(v___x_5066_, 3, v_varMap_5062_);
lean_ctor_set(v___x_5066_, 4, v___x_5065_);
lean_ctor_set(v___x_5066_, 5, v_idx_5064_);
lean_inc_ref(v_k_5054_);
v___x_5067_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5054_, v___x_5066_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
lean_dec_ref_known(v___x_5066_, 6);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5105_; 
v_a_5068_ = lean_ctor_get(v___x_5067_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5067_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5070_ = v___x_5067_;
v_isShared_5071_ = v_isSharedCheck_5105_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5067_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5105_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
size_t v___x_5072_; size_t v___x_5073_; uint8_t v___x_5074_; 
v___x_5072_ = lean_ptr_addr(v_k_5054_);
v___x_5073_ = lean_ptr_addr(v_a_5068_);
v___x_5074_ = lean_usize_dec_eq(v___x_5072_, v___x_5073_);
if (v___x_5074_ == 0)
{
lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5084_; 
v_isSharedCheck_5084_ = !lean_is_exclusive(v_code_5017_);
if (v_isSharedCheck_5084_ == 0)
{
lean_object* v_unused_5085_; lean_object* v_unused_5086_; 
v_unused_5085_ = lean_ctor_get(v_code_5017_, 1);
lean_dec(v_unused_5085_);
v_unused_5086_ = lean_ctor_get(v_code_5017_, 0);
lean_dec(v_unused_5086_);
v___x_5076_ = v_code_5017_;
v_isShared_5077_ = v_isSharedCheck_5084_;
goto v_resetjp_5075_;
}
else
{
lean_dec(v_code_5017_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5084_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5079_; 
if (v_isShared_5077_ == 0)
{
lean_ctor_set(v___x_5076_, 1, v_a_5068_);
lean_ctor_set(v___x_5076_, 0, v_fst_5056_);
v___x_5079_ = v___x_5076_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_fst_5056_);
lean_ctor_set(v_reuseFailAlloc_5083_, 1, v_a_5068_);
v___x_5079_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
lean_object* v___x_5081_; 
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 0, v___x_5079_);
v___x_5081_ = v___x_5070_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v___x_5079_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
return v___x_5081_;
}
}
}
}
else
{
size_t v___x_5087_; size_t v___x_5088_; uint8_t v___x_5089_; 
v___x_5087_ = lean_ptr_addr(v_decl_5053_);
v___x_5088_ = lean_ptr_addr(v_fst_5056_);
v___x_5089_ = lean_usize_dec_eq(v___x_5087_, v___x_5088_);
if (v___x_5089_ == 0)
{
lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5099_; 
v_isSharedCheck_5099_ = !lean_is_exclusive(v_code_5017_);
if (v_isSharedCheck_5099_ == 0)
{
lean_object* v_unused_5100_; lean_object* v_unused_5101_; 
v_unused_5100_ = lean_ctor_get(v_code_5017_, 1);
lean_dec(v_unused_5100_);
v_unused_5101_ = lean_ctor_get(v_code_5017_, 0);
lean_dec(v_unused_5101_);
v___x_5091_ = v_code_5017_;
v_isShared_5092_ = v_isSharedCheck_5099_;
goto v_resetjp_5090_;
}
else
{
lean_dec(v_code_5017_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5099_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5094_; 
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 1, v_a_5068_);
lean_ctor_set(v___x_5091_, 0, v_fst_5056_);
v___x_5094_ = v___x_5091_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_fst_5056_);
lean_ctor_set(v_reuseFailAlloc_5098_, 1, v_a_5068_);
v___x_5094_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
lean_object* v___x_5096_; 
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 0, v___x_5094_);
v___x_5096_ = v___x_5070_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v___x_5094_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
}
}
else
{
lean_object* v___x_5103_; 
lean_dec(v_a_5068_);
lean_dec_ref(v_fst_5056_);
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 0, v_code_5017_);
v___x_5103_ = v___x_5070_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_code_5017_);
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
}
else
{
lean_dec_ref(v_fst_5056_);
lean_dec_ref_known(v_code_5017_, 2);
return v___x_5067_;
}
}
}
case 3:
{
lean_object* v_fvarId_5158_; lean_object* v_args_5159_; lean_object* v_jpLiveVarMap_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
v_fvarId_5158_ = lean_ctor_get(v_code_5017_, 0);
v_args_5159_ = lean_ctor_get(v_code_5017_, 1);
lean_inc_ref(v_args_5159_);
v_jpLiveVarMap_5160_ = lean_ctor_get(v_a_5018_, 4);
v___x_5161_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(v_jpLiveVarMap_5160_, v_fvarId_5158_);
v___x_5162_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_5161_, v_a_5018_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v_a_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; uint8_t v___x_5166_; lean_object* v___x_5167_; 
v_a_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_a_5163_);
lean_dec_ref_known(v___x_5162_, 1);
v___x_5164_ = lean_st_ref_take(v_a_5019_);
lean_dec(v___x_5164_);
v___x_5165_ = lean_st_ref_put(v_a_5019_, v_a_5163_);
v___x_5166_ = 1;
v___x_5167_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_5166_, v_fvarId_5158_, v_a_5021_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; lean_object* v___y_5170_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___x_5167_, 1);
if (lean_obj_tag(v_a_5168_) == 0)
{
lean_object* v___x_5191_; lean_object* v___x_5192_; 
v___x_5191_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10);
v___x_5192_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5(v___x_5191_);
v___y_5170_ = v___x_5192_;
goto v___jp_5169_;
}
else
{
lean_object* v_val_5193_; 
v_val_5193_ = lean_ctor_get(v_a_5168_, 0);
lean_inc(v_val_5193_);
lean_dec_ref_known(v_a_5168_, 1);
v___y_5170_ = v_val_5193_;
goto v___jp_5169_;
}
v___jp_5169_:
{
lean_object* v_params_5171_; lean_object* v___x_5172_; 
v_params_5171_ = lean_ctor_get(v___y_5170_, 2);
lean_inc_ref(v_params_5171_);
lean_dec_ref(v___y_5170_);
v___x_5172_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_5159_, v_params_5171_, v_code_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; lean_object* v___x_5174_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
lean_inc(v_a_5173_);
lean_dec_ref_known(v___x_5172_, 1);
v___x_5174_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_5159_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
lean_dec_ref(v_args_5159_);
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v___x_5176_; uint8_t v_isShared_5177_; uint8_t v_isSharedCheck_5181_; 
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5181_ == 0)
{
lean_object* v_unused_5182_; 
v_unused_5182_ = lean_ctor_get(v___x_5174_, 0);
lean_dec(v_unused_5182_);
v___x_5176_ = v___x_5174_;
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
else
{
lean_dec(v___x_5174_);
v___x_5176_ = lean_box(0);
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
v_resetjp_5175_:
{
lean_object* v___x_5179_; 
if (v_isShared_5177_ == 0)
{
lean_ctor_set(v___x_5176_, 0, v_a_5173_);
v___x_5179_ = v___x_5176_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_a_5173_);
v___x_5179_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
return v___x_5179_;
}
}
}
else
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5190_; 
lean_dec(v_a_5173_);
v_a_5183_ = lean_ctor_get(v___x_5174_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5185_ = v___x_5174_;
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5174_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5188_; 
if (v_isShared_5186_ == 0)
{
v___x_5188_ = v___x_5185_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_a_5183_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
return v___x_5188_;
}
}
}
}
else
{
lean_dec_ref(v_args_5159_);
return v___x_5172_;
}
}
}
else
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5201_; 
lean_dec_ref(v_args_5159_);
lean_dec_ref_known(v_code_5017_, 2);
v_a_5194_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5196_ = v___x_5167_;
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5167_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5199_; 
if (v_isShared_5197_ == 0)
{
v___x_5199_ = v___x_5196_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
v___x_5199_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
return v___x_5199_;
}
}
}
}
else
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5209_; 
lean_dec_ref(v_args_5159_);
lean_dec_ref_known(v_code_5017_, 2);
v_a_5202_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5204_ = v___x_5162_;
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5162_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5207_; 
if (v_isShared_5205_ == 0)
{
v___x_5207_ = v___x_5204_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
}
case 4:
{
lean_object* v_cases_5210_; lean_object* v_typeName_5211_; lean_object* v_resultType_5212_; lean_object* v_discr_5213_; lean_object* v_alts_5214_; size_t v_sz_5215_; size_t v___x_5216_; lean_object* v___x_5217_; 
v_cases_5210_ = lean_ctor_get(v_code_5017_, 0);
v_typeName_5211_ = lean_ctor_get(v_cases_5210_, 0);
v_resultType_5212_ = lean_ctor_get(v_cases_5210_, 1);
v_discr_5213_ = lean_ctor_get(v_cases_5210_, 2);
v_alts_5214_ = lean_ctor_get(v_cases_5210_, 3);
v_sz_5215_ = lean_array_size(v_alts_5214_);
v___x_5216_ = ((size_t)0ULL);
lean_inc_ref(v_alts_5214_);
lean_inc_ref(v_cases_5210_);
v___x_5217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(v_cases_5210_, v_sz_5215_, v___x_5216_, v_alts_5214_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5217_) == 0)
{
lean_object* v_a_5218_; lean_object* v___y_5220_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; uint8_t v___x_5268_; 
v_a_5218_ = lean_ctor_get(v___x_5217_, 0);
lean_inc(v_a_5218_);
lean_dec_ref_known(v___x_5217_, 1);
v___x_5265_ = lean_unsigned_to_nat(0u);
v___x_5266_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5267_ = lean_array_get_size(v_a_5218_);
v___x_5268_ = lean_nat_dec_lt(v___x_5265_, v___x_5267_);
if (v___x_5268_ == 0)
{
v___y_5220_ = v___x_5266_;
goto v___jp_5219_;
}
else
{
uint8_t v___x_5269_; 
v___x_5269_ = lean_nat_dec_le(v___x_5267_, v___x_5267_);
if (v___x_5269_ == 0)
{
if (v___x_5268_ == 0)
{
v___y_5220_ = v___x_5266_;
goto v___jp_5219_;
}
else
{
size_t v___x_5270_; lean_object* v___x_5271_; 
v___x_5270_ = lean_usize_of_nat(v___x_5267_);
v___x_5271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_a_5218_, v___x_5216_, v___x_5270_, v___x_5266_);
v___y_5220_ = v___x_5271_;
goto v___jp_5219_;
}
}
else
{
size_t v___x_5272_; lean_object* v___x_5273_; 
v___x_5272_ = lean_usize_of_nat(v___x_5267_);
v___x_5273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_a_5218_, v___x_5216_, v___x_5272_, v___x_5266_);
v___y_5220_ = v___x_5273_;
goto v___jp_5219_;
}
}
v___jp_5219_:
{
lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; 
v___x_5221_ = lean_st_ref_take(v_a_5019_);
lean_dec(v___x_5221_);
v___x_5222_ = lean_st_ref_put(v_a_5019_, v___y_5220_);
lean_inc(v_discr_5213_);
v___x_5223_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_discr_5213_, v_a_5018_, v_a_5019_);
if (lean_obj_tag(v___x_5223_) == 0)
{
size_t v_sz_5224_; lean_object* v___x_5225_; 
lean_dec_ref_known(v___x_5223_, 1);
v_sz_5224_ = lean_array_size(v_a_5218_);
lean_inc(v_discr_5213_);
v___x_5225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(v_discr_5213_, v_sz_5224_, v___x_5216_, v_a_5218_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5248_; 
v_a_5226_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5248_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5248_ == 0)
{
v___x_5228_ = v___x_5225_;
v_isShared_5229_ = v_isSharedCheck_5248_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___x_5225_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5248_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
size_t v___x_5230_; size_t v___x_5231_; uint8_t v___x_5232_; 
v___x_5230_ = lean_ptr_addr(v_alts_5214_);
v___x_5231_ = lean_ptr_addr(v_a_5226_);
v___x_5232_ = lean_usize_dec_eq(v___x_5230_, v___x_5231_);
if (v___x_5232_ == 0)
{
lean_object* v___x_5234_; uint8_t v_isShared_5235_; uint8_t v_isSharedCheck_5243_; 
lean_inc(v_discr_5213_);
lean_inc_ref(v_resultType_5212_);
lean_inc(v_typeName_5211_);
v_isSharedCheck_5243_ = !lean_is_exclusive(v_code_5017_);
if (v_isSharedCheck_5243_ == 0)
{
lean_object* v_unused_5244_; 
v_unused_5244_ = lean_ctor_get(v_code_5017_, 0);
lean_dec(v_unused_5244_);
v___x_5234_ = v_code_5017_;
v_isShared_5235_ = v_isSharedCheck_5243_;
goto v_resetjp_5233_;
}
else
{
lean_dec(v_code_5017_);
v___x_5234_ = lean_box(0);
v_isShared_5235_ = v_isSharedCheck_5243_;
goto v_resetjp_5233_;
}
v_resetjp_5233_:
{
lean_object* v___x_5236_; lean_object* v___x_5238_; 
v___x_5236_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5236_, 0, v_typeName_5211_);
lean_ctor_set(v___x_5236_, 1, v_resultType_5212_);
lean_ctor_set(v___x_5236_, 2, v_discr_5213_);
lean_ctor_set(v___x_5236_, 3, v_a_5226_);
if (v_isShared_5235_ == 0)
{
lean_ctor_set(v___x_5234_, 0, v___x_5236_);
v___x_5238_ = v___x_5234_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v___x_5236_);
v___x_5238_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
lean_object* v___x_5240_; 
if (v_isShared_5229_ == 0)
{
lean_ctor_set(v___x_5228_, 0, v___x_5238_);
v___x_5240_ = v___x_5228_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v___x_5238_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
}
}
else
{
lean_object* v___x_5246_; 
lean_dec(v_a_5226_);
if (v_isShared_5229_ == 0)
{
lean_ctor_set(v___x_5228_, 0, v_code_5017_);
v___x_5246_ = v___x_5228_;
goto v_reusejp_5245_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v_code_5017_);
v___x_5246_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5245_;
}
v_reusejp_5245_:
{
return v___x_5246_;
}
}
}
}
else
{
lean_object* v_a_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5256_; 
lean_dec_ref_known(v_code_5017_, 1);
v_a_5249_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5251_ = v___x_5225_;
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5225_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v___x_5254_; 
if (v_isShared_5252_ == 0)
{
v___x_5254_ = v___x_5251_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_a_5249_);
v___x_5254_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
return v___x_5254_;
}
}
}
}
else
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5264_; 
lean_dec(v_a_5218_);
lean_dec_ref_known(v_code_5017_, 1);
v_a_5257_ = lean_ctor_get(v___x_5223_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5223_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5259_ = v___x_5223_;
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v___x_5223_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5262_; 
if (v_isShared_5260_ == 0)
{
v___x_5262_ = v___x_5259_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_a_5257_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
}
}
}
else
{
lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5281_; 
lean_dec_ref_known(v_code_5017_, 1);
v_a_5274_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5276_ = v___x_5217_;
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___x_5217_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5279_; 
if (v_isShared_5277_ == 0)
{
v___x_5279_ = v___x_5276_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5274_);
v___x_5279_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
return v___x_5279_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
v_fvarId_5282_ = lean_ctor_get(v_code_5017_, 0);
v___x_5283_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5284_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_5283_, v_a_5018_);
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v_a_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v_varMap_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; 
v_a_5285_ = lean_ctor_get(v___x_5284_, 0);
lean_inc(v_a_5285_);
lean_dec_ref_known(v___x_5284_, 1);
v___x_5286_ = lean_st_ref_take(v_a_5019_);
lean_dec(v___x_5286_);
v___x_5287_ = lean_st_ref_put(v_a_5019_, v_a_5285_);
v_varMap_5288_ = lean_ctor_get(v_a_5018_, 3);
v___x_5289_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_5288_, v_fvarId_5282_);
lean_inc(v_fvarId_5282_);
v___x_5290_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_5282_, v_a_5018_, v_a_5019_);
if (lean_obj_tag(v___x_5290_) == 0)
{
lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5314_; 
v_isSharedCheck_5314_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5314_ == 0)
{
lean_object* v_unused_5315_; 
v_unused_5315_ = lean_ctor_get(v___x_5290_, 0);
lean_dec(v_unused_5315_);
v___x_5292_ = v___x_5290_;
v_isShared_5293_ = v_isSharedCheck_5314_;
goto v_resetjp_5291_;
}
else
{
lean_dec(v___x_5290_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5314_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v___x_5294_; uint8_t v_isPossibleRef_5295_; 
v___x_5294_ = lean_st_ref_get(v_a_5019_);
v_isPossibleRef_5295_ = lean_ctor_get_uint8(v___x_5289_, sizeof(void*)*2);
if (v_isPossibleRef_5295_ == 0)
{
lean_object* v___x_5297_; 
lean_dec(v___x_5294_);
lean_dec_ref(v___x_5289_);
if (v_isShared_5293_ == 0)
{
lean_ctor_set(v___x_5292_, 0, v_code_5017_);
v___x_5297_ = v___x_5292_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_code_5017_);
v___x_5297_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
return v___x_5297_;
}
}
else
{
uint8_t v_isDefiniteRef_5299_; uint8_t v_persistent_5300_; lean_object* v_borrows_5301_; uint8_t v___x_5302_; 
v_isDefiniteRef_5299_ = lean_ctor_get_uint8(v___x_5289_, sizeof(void*)*2 + 1);
v_persistent_5300_ = lean_ctor_get_uint8(v___x_5289_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_5289_);
v_borrows_5301_ = lean_ctor_get(v___x_5294_, 1);
lean_inc_ref(v_borrows_5301_);
lean_dec(v___x_5294_);
v___x_5302_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_5301_, v_fvarId_5282_);
lean_dec_ref(v_borrows_5301_);
if (v___x_5302_ == 0)
{
lean_object* v___x_5304_; 
if (v_isShared_5293_ == 0)
{
lean_ctor_set(v___x_5292_, 0, v_code_5017_);
v___x_5304_ = v___x_5292_;
goto v_reusejp_5303_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_code_5017_);
v___x_5304_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5303_;
}
v_reusejp_5303_:
{
return v___x_5304_;
}
}
else
{
lean_object* v___x_5306_; uint8_t v___y_5308_; 
lean_inc(v_fvarId_5282_);
v___x_5306_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_5299_ == 0)
{
v___y_5308_ = v___x_5302_;
goto v___jp_5307_;
}
else
{
uint8_t v___x_5313_; 
v___x_5313_ = 0;
v___y_5308_ = v___x_5313_;
goto v___jp_5307_;
}
v___jp_5307_:
{
lean_object* v___x_5309_; lean_object* v___x_5311_; 
v___x_5309_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_5309_, 0, v_fvarId_5282_);
lean_ctor_set(v___x_5309_, 1, v___x_5306_);
lean_ctor_set(v___x_5309_, 2, v_code_5017_);
lean_ctor_set_uint8(v___x_5309_, sizeof(void*)*3, v___y_5308_);
lean_ctor_set_uint8(v___x_5309_, sizeof(void*)*3 + 1, v_persistent_5300_);
if (v_isShared_5293_ == 0)
{
lean_ctor_set(v___x_5292_, 0, v___x_5309_);
v___x_5311_ = v___x_5292_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v___x_5309_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
return v___x_5311_;
}
}
}
}
}
}
else
{
lean_object* v_a_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5323_; 
lean_dec_ref(v___x_5289_);
lean_dec_ref_known(v_code_5017_, 1);
v_a_5316_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5318_ = v___x_5290_;
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_a_5316_);
lean_dec(v___x_5290_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5321_; 
if (v_isShared_5319_ == 0)
{
v___x_5321_ = v___x_5318_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5316_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
}
else
{
lean_object* v_a_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5331_; 
lean_dec_ref_known(v_code_5017_, 1);
v_a_5324_ = lean_ctor_get(v___x_5284_, 0);
v_isSharedCheck_5331_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5331_ == 0)
{
v___x_5326_ = v___x_5284_;
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_a_5324_);
lean_dec(v___x_5284_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5329_; 
if (v_isShared_5327_ == 0)
{
v___x_5329_ = v___x_5326_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_a_5324_);
v___x_5329_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
return v___x_5329_;
}
}
}
}
case 6:
{
lean_object* v___x_5332_; lean_object* v___x_5333_; 
v___x_5332_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5333_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_5332_, v_a_5018_);
if (lean_obj_tag(v___x_5333_) == 0)
{
lean_object* v_a_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5343_; 
v_a_5334_ = lean_ctor_get(v___x_5333_, 0);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5333_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5336_ = v___x_5333_;
v_isShared_5337_ = v_isSharedCheck_5343_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_a_5334_);
lean_dec(v___x_5333_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5343_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5341_; 
v___x_5338_ = lean_st_ref_take(v_a_5019_);
lean_dec(v___x_5338_);
v___x_5339_ = lean_st_ref_put(v_a_5019_, v_a_5334_);
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 0, v_code_5017_);
v___x_5341_ = v___x_5336_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_code_5017_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
return v___x_5341_;
}
}
}
else
{
lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5351_; 
lean_dec_ref_known(v_code_5017_, 1);
v_a_5344_ = lean_ctor_get(v___x_5333_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5333_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5346_ = v___x_5333_;
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_dec(v___x_5333_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v___x_5349_; 
if (v_isShared_5347_ == 0)
{
v___x_5349_ = v___x_5346_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
}
case 8:
{
lean_object* v_fvarId_5352_; lean_object* v_i_5353_; lean_object* v_y_5354_; lean_object* v_k_5355_; lean_object* v___x_5356_; 
v_fvarId_5352_ = lean_ctor_get(v_code_5017_, 0);
v_i_5353_ = lean_ctor_get(v_code_5017_, 1);
v_y_5354_ = lean_ctor_get(v_code_5017_, 2);
v_k_5355_ = lean_ctor_get(v_code_5017_, 3);
lean_inc_ref(v_k_5355_);
v___x_5356_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5355_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_a_5357_; lean_object* v___x_5358_; 
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_a_5357_);
lean_dec_ref_known(v___x_5356_, 1);
lean_inc(v_fvarId_5352_);
v___x_5358_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_5352_, v_a_5018_, v_a_5019_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5382_; 
v_isSharedCheck_5382_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5382_ == 0)
{
lean_object* v_unused_5383_; 
v_unused_5383_ = lean_ctor_get(v___x_5358_, 0);
lean_dec(v_unused_5383_);
v___x_5360_ = v___x_5358_;
v_isShared_5361_ = v_isSharedCheck_5382_;
goto v_resetjp_5359_;
}
else
{
lean_dec(v___x_5358_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5382_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
size_t v___x_5362_; size_t v___x_5363_; uint8_t v___x_5364_; 
v___x_5362_ = lean_ptr_addr(v_k_5355_);
v___x_5363_ = lean_ptr_addr(v_a_5357_);
v___x_5364_ = lean_usize_dec_eq(v___x_5362_, v___x_5363_);
if (v___x_5364_ == 0)
{
lean_object* v___x_5366_; uint8_t v_isShared_5367_; uint8_t v_isSharedCheck_5374_; 
lean_inc(v_y_5354_);
lean_inc(v_i_5353_);
lean_inc(v_fvarId_5352_);
v_isSharedCheck_5374_ = !lean_is_exclusive(v_code_5017_);
if (v_isSharedCheck_5374_ == 0)
{
lean_object* v_unused_5375_; lean_object* v_unused_5376_; lean_object* v_unused_5377_; lean_object* v_unused_5378_; 
v_unused_5375_ = lean_ctor_get(v_code_5017_, 3);
lean_dec(v_unused_5375_);
v_unused_5376_ = lean_ctor_get(v_code_5017_, 2);
lean_dec(v_unused_5376_);
v_unused_5377_ = lean_ctor_get(v_code_5017_, 1);
lean_dec(v_unused_5377_);
v_unused_5378_ = lean_ctor_get(v_code_5017_, 0);
lean_dec(v_unused_5378_);
v___x_5366_ = v_code_5017_;
v_isShared_5367_ = v_isSharedCheck_5374_;
goto v_resetjp_5365_;
}
else
{
lean_dec(v_code_5017_);
v___x_5366_ = lean_box(0);
v_isShared_5367_ = v_isSharedCheck_5374_;
goto v_resetjp_5365_;
}
v_resetjp_5365_:
{
lean_object* v___x_5369_; 
if (v_isShared_5367_ == 0)
{
lean_ctor_set(v___x_5366_, 3, v_a_5357_);
v___x_5369_ = v___x_5366_;
goto v_reusejp_5368_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_fvarId_5352_);
lean_ctor_set(v_reuseFailAlloc_5373_, 1, v_i_5353_);
lean_ctor_set(v_reuseFailAlloc_5373_, 2, v_y_5354_);
lean_ctor_set(v_reuseFailAlloc_5373_, 3, v_a_5357_);
v___x_5369_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5368_;
}
v_reusejp_5368_:
{
lean_object* v___x_5371_; 
if (v_isShared_5361_ == 0)
{
lean_ctor_set(v___x_5360_, 0, v___x_5369_);
v___x_5371_ = v___x_5360_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5369_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
else
{
lean_object* v___x_5380_; 
lean_dec(v_a_5357_);
if (v_isShared_5361_ == 0)
{
lean_ctor_set(v___x_5360_, 0, v_code_5017_);
v___x_5380_ = v___x_5360_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v_code_5017_);
v___x_5380_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
return v___x_5380_;
}
}
}
}
else
{
lean_object* v_a_5384_; lean_object* v___x_5386_; uint8_t v_isShared_5387_; uint8_t v_isSharedCheck_5391_; 
lean_dec(v_a_5357_);
lean_dec_ref_known(v_code_5017_, 4);
v_a_5384_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5391_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5391_ == 0)
{
v___x_5386_ = v___x_5358_;
v_isShared_5387_ = v_isSharedCheck_5391_;
goto v_resetjp_5385_;
}
else
{
lean_inc(v_a_5384_);
lean_dec(v___x_5358_);
v___x_5386_ = lean_box(0);
v_isShared_5387_ = v_isSharedCheck_5391_;
goto v_resetjp_5385_;
}
v_resetjp_5385_:
{
lean_object* v___x_5389_; 
if (v_isShared_5387_ == 0)
{
v___x_5389_ = v___x_5386_;
goto v_reusejp_5388_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v_a_5384_);
v___x_5389_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5388_;
}
v_reusejp_5388_:
{
return v___x_5389_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_5017_, 4);
return v___x_5356_;
}
}
case 9:
{
lean_object* v_fvarId_5392_; lean_object* v_i_5393_; lean_object* v_offset_5394_; lean_object* v_y_5395_; lean_object* v_ty_5396_; lean_object* v_k_5397_; lean_object* v___x_5398_; 
v_fvarId_5392_ = lean_ctor_get(v_code_5017_, 0);
v_i_5393_ = lean_ctor_get(v_code_5017_, 1);
v_offset_5394_ = lean_ctor_get(v_code_5017_, 2);
v_y_5395_ = lean_ctor_get(v_code_5017_, 3);
v_ty_5396_ = lean_ctor_get(v_code_5017_, 4);
v_k_5397_ = lean_ctor_get(v_code_5017_, 5);
lean_inc_ref(v_k_5397_);
v___x_5398_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5397_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5398_) == 0)
{
lean_object* v_a_5399_; lean_object* v___x_5400_; 
v_a_5399_ = lean_ctor_get(v___x_5398_, 0);
lean_inc(v_a_5399_);
lean_dec_ref_known(v___x_5398_, 1);
lean_inc(v_fvarId_5392_);
v___x_5400_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_5392_, v_a_5018_, v_a_5019_);
if (lean_obj_tag(v___x_5400_) == 0)
{
lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5426_; 
v_isSharedCheck_5426_ = !lean_is_exclusive(v___x_5400_);
if (v_isSharedCheck_5426_ == 0)
{
lean_object* v_unused_5427_; 
v_unused_5427_ = lean_ctor_get(v___x_5400_, 0);
lean_dec(v_unused_5427_);
v___x_5402_ = v___x_5400_;
v_isShared_5403_ = v_isSharedCheck_5426_;
goto v_resetjp_5401_;
}
else
{
lean_dec(v___x_5400_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5426_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
size_t v___x_5404_; size_t v___x_5405_; uint8_t v___x_5406_; 
v___x_5404_ = lean_ptr_addr(v_k_5397_);
v___x_5405_ = lean_ptr_addr(v_a_5399_);
v___x_5406_ = lean_usize_dec_eq(v___x_5404_, v___x_5405_);
if (v___x_5406_ == 0)
{
lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5416_; 
lean_inc_ref(v_ty_5396_);
lean_inc(v_y_5395_);
lean_inc(v_offset_5394_);
lean_inc(v_i_5393_);
lean_inc(v_fvarId_5392_);
v_isSharedCheck_5416_ = !lean_is_exclusive(v_code_5017_);
if (v_isSharedCheck_5416_ == 0)
{
lean_object* v_unused_5417_; lean_object* v_unused_5418_; lean_object* v_unused_5419_; lean_object* v_unused_5420_; lean_object* v_unused_5421_; lean_object* v_unused_5422_; 
v_unused_5417_ = lean_ctor_get(v_code_5017_, 5);
lean_dec(v_unused_5417_);
v_unused_5418_ = lean_ctor_get(v_code_5017_, 4);
lean_dec(v_unused_5418_);
v_unused_5419_ = lean_ctor_get(v_code_5017_, 3);
lean_dec(v_unused_5419_);
v_unused_5420_ = lean_ctor_get(v_code_5017_, 2);
lean_dec(v_unused_5420_);
v_unused_5421_ = lean_ctor_get(v_code_5017_, 1);
lean_dec(v_unused_5421_);
v_unused_5422_ = lean_ctor_get(v_code_5017_, 0);
lean_dec(v_unused_5422_);
v___x_5408_ = v_code_5017_;
v_isShared_5409_ = v_isSharedCheck_5416_;
goto v_resetjp_5407_;
}
else
{
lean_dec(v_code_5017_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5416_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
lean_object* v___x_5411_; 
if (v_isShared_5409_ == 0)
{
lean_ctor_set(v___x_5408_, 5, v_a_5399_);
v___x_5411_ = v___x_5408_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_fvarId_5392_);
lean_ctor_set(v_reuseFailAlloc_5415_, 1, v_i_5393_);
lean_ctor_set(v_reuseFailAlloc_5415_, 2, v_offset_5394_);
lean_ctor_set(v_reuseFailAlloc_5415_, 3, v_y_5395_);
lean_ctor_set(v_reuseFailAlloc_5415_, 4, v_ty_5396_);
lean_ctor_set(v_reuseFailAlloc_5415_, 5, v_a_5399_);
v___x_5411_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
lean_object* v___x_5413_; 
if (v_isShared_5403_ == 0)
{
lean_ctor_set(v___x_5402_, 0, v___x_5411_);
v___x_5413_ = v___x_5402_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v___x_5411_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
}
else
{
lean_object* v___x_5424_; 
lean_dec(v_a_5399_);
if (v_isShared_5403_ == 0)
{
lean_ctor_set(v___x_5402_, 0, v_code_5017_);
v___x_5424_ = v___x_5402_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_code_5017_);
v___x_5424_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
return v___x_5424_;
}
}
}
}
else
{
lean_object* v_a_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5435_; 
lean_dec(v_a_5399_);
lean_dec_ref_known(v_code_5017_, 6);
v_a_5428_ = lean_ctor_get(v___x_5400_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v___x_5400_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5430_ = v___x_5400_;
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_a_5428_);
lean_dec(v___x_5400_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___x_5433_; 
if (v_isShared_5431_ == 0)
{
v___x_5433_ = v___x_5430_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_a_5428_);
v___x_5433_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
return v___x_5433_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_5017_, 6);
return v___x_5398_;
}
}
default: 
{
lean_object* v___x_5436_; lean_object* v___x_5437_; 
lean_dec_ref(v_code_5017_);
v___x_5436_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1);
v___x_5437_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v___x_5436_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
return v___x_5437_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_5017_ = stack[0].m_obj;
lean_object* v_a_5018_ = stack[1].m_obj;
lean_object* v_a_5019_ = stack[2].m_obj;
lean_object* v_a_5020_ = stack[3].m_obj;
lean_object* v_a_5021_ = stack[4].m_obj;
lean_object* v_a_5022_ = stack[5].m_obj;
lean_object* v_a_5023_ = stack[6].m_obj;
lean_object* v_res_5438_;
v_res_5438_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
stack->m_obj
 = v_res_5438_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(lean_object* v_cases_5439_, size_t v_sz_5440_, size_t v_i_5441_, lean_object* v_bs_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_){
_start:
{
uint8_t v___x_5450_; 
v___x_5450_ = lean_usize_dec_lt(v_i_5441_, v_sz_5440_);
if (v___x_5450_ == 0)
{
lean_object* v___x_5451_; 
lean_dec_ref(v_cases_5439_);
v___x_5451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5451_, 0, v_bs_5442_);
return v___x_5451_;
}
else
{
lean_object* v_v_5452_; lean_object* v___x_5453_; lean_object* v_bs_x27_5454_; lean_object* v___x_5455_; lean_object* v_a_5457_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; 
v_v_5452_ = lean_array_uget(v_bs_5442_, v_i_5441_);
v___x_5453_ = lean_unsigned_to_nat(0u);
v_bs_x27_5454_ = lean_array_uset(v_bs_5442_, v_i_5441_, v___x_5453_);
v___x_5455_ = lean_st_ref_get(v___y_5444_);
v___x_5466_ = lean_st_ref_take(v___y_5444_);
lean_dec(v___x_5466_);
v___x_5467_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5468_ = lean_st_ref_put(v___y_5444_, v___x_5467_);
if (lean_obj_tag(v_v_5452_) == 1)
{
lean_object* v_info_5469_; lean_object* v_code_5470_; lean_object* v_discr_5471_; lean_object* v_resetTargets_5472_; lean_object* v_unconditionalBorrows_5473_; lean_object* v_derivedValMap_5474_; lean_object* v_varMap_5475_; lean_object* v_jpLiveVarMap_5476_; lean_object* v_idx_5477_; lean_object* v___y_5479_; lean_object* v___x_5494_; 
v_info_5469_ = lean_ctor_get(v_v_5452_, 0);
v_code_5470_ = lean_ctor_get(v_v_5452_, 1);
v_discr_5471_ = lean_ctor_get(v_cases_5439_, 2);
v_resetTargets_5472_ = lean_ctor_get(v___y_5443_, 0);
v_unconditionalBorrows_5473_ = lean_ctor_get(v___y_5443_, 1);
v_derivedValMap_5474_ = lean_ctor_get(v___y_5443_, 2);
v_varMap_5475_ = lean_ctor_get(v___y_5443_, 3);
v_jpLiveVarMap_5476_ = lean_ctor_get(v___y_5443_, 4);
v_idx_5477_ = lean_ctor_get(v___y_5443_, 5);
v___x_5494_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_varMap_5475_, v_discr_5471_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_inc(v_varMap_5475_);
v___y_5479_ = v_varMap_5475_;
goto v___jp_5478_;
}
else
{
lean_object* v_val_5495_; lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5516_; 
v_val_5495_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5516_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5516_ == 0)
{
v___x_5497_ = v___x_5494_;
v_isShared_5498_ = v_isSharedCheck_5516_;
goto v_resetjp_5496_;
}
else
{
lean_inc(v_val_5495_);
lean_dec(v___x_5494_);
v___x_5497_ = lean_box(0);
v_isShared_5498_ = v_isSharedCheck_5516_;
goto v_resetjp_5496_;
}
v_resetjp_5496_:
{
uint8_t v_persistent_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5513_; 
v_persistent_5499_ = lean_ctor_get_uint8(v_val_5495_, sizeof(void*)*2 + 2);
v_isSharedCheck_5513_ = !lean_is_exclusive(v_val_5495_);
if (v_isSharedCheck_5513_ == 0)
{
lean_object* v_unused_5514_; lean_object* v_unused_5515_; 
v_unused_5514_ = lean_ctor_get(v_val_5495_, 1);
lean_dec(v_unused_5514_);
v_unused_5515_ = lean_ctor_get(v_val_5495_, 0);
lean_dec(v_unused_5515_);
v___x_5501_ = v_val_5495_;
v_isShared_5502_ = v_isSharedCheck_5513_;
goto v_resetjp_5500_;
}
else
{
lean_dec(v_val_5495_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5513_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
uint8_t v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5507_; 
v___x_5503_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_info_5469_);
v___x_5504_ = lean_unsigned_to_nat(1u);
v___x_5505_ = lean_nat_add(v_idx_5477_, v___x_5504_);
lean_inc_ref(v_info_5469_);
if (v_isShared_5498_ == 0)
{
lean_ctor_set(v___x_5497_, 0, v_info_5469_);
v___x_5507_ = v___x_5497_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_info_5469_);
v___x_5507_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
lean_object* v___x_5509_; 
if (v_isShared_5502_ == 0)
{
lean_ctor_set(v___x_5501_, 1, v___x_5507_);
lean_ctor_set(v___x_5501_, 0, v___x_5505_);
v___x_5509_ = v___x_5501_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v___x_5505_);
lean_ctor_set(v_reuseFailAlloc_5511_, 1, v___x_5507_);
lean_ctor_set_uint8(v_reuseFailAlloc_5511_, sizeof(void*)*2 + 2, v_persistent_5499_);
v___x_5509_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
lean_object* v___x_5510_; 
lean_ctor_set_uint8(v___x_5509_, sizeof(void*)*2, v___x_5503_);
lean_ctor_set_uint8(v___x_5509_, sizeof(void*)*2 + 1, v___x_5503_);
lean_inc(v_varMap_5475_);
lean_inc(v_discr_5471_);
v___x_5510_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_5471_, v___x_5509_, v_varMap_5475_);
v___y_5479_ = v___x_5510_;
goto v___jp_5478_;
}
}
}
}
}
v___jp_5478_:
{
lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; 
v___x_5480_ = lean_unsigned_to_nat(1u);
v___x_5481_ = lean_nat_add(v_idx_5477_, v___x_5480_);
lean_inc(v_jpLiveVarMap_5476_);
lean_inc(v_derivedValMap_5474_);
lean_inc(v_unconditionalBorrows_5473_);
lean_inc_ref(v_resetTargets_5472_);
v___x_5482_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5482_, 0, v_resetTargets_5472_);
lean_ctor_set(v___x_5482_, 1, v_unconditionalBorrows_5473_);
lean_ctor_set(v___x_5482_, 2, v_derivedValMap_5474_);
lean_ctor_set(v___x_5482_, 3, v___y_5479_);
lean_ctor_set(v___x_5482_, 4, v_jpLiveVarMap_5476_);
lean_ctor_set(v___x_5482_, 5, v___x_5481_);
lean_inc_ref(v_code_5470_);
v___x_5483_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5470_, v___x_5482_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_);
lean_dec_ref_known(v___x_5482_, 6);
if (lean_obj_tag(v___x_5483_) == 0)
{
lean_object* v_a_5484_; lean_object* v___x_5485_; 
v_a_5484_ = lean_ctor_get(v___x_5483_, 0);
lean_inc(v_a_5484_);
lean_dec_ref_known(v___x_5483_, 1);
v___x_5485_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_5452_, v_a_5484_);
v_a_5457_ = v___x_5485_;
goto v___jp_5456_;
}
else
{
lean_object* v_a_5486_; lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5493_; 
lean_dec_ref_known(v_v_5452_, 2);
lean_dec(v___x_5455_);
lean_dec_ref(v_bs_x27_5454_);
lean_dec_ref(v_cases_5439_);
v_a_5486_ = lean_ctor_get(v___x_5483_, 0);
v_isSharedCheck_5493_ = !lean_is_exclusive(v___x_5483_);
if (v_isSharedCheck_5493_ == 0)
{
v___x_5488_ = v___x_5483_;
v_isShared_5489_ = v_isSharedCheck_5493_;
goto v_resetjp_5487_;
}
else
{
lean_inc(v_a_5486_);
lean_dec(v___x_5483_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5493_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
lean_object* v___x_5491_; 
if (v_isShared_5489_ == 0)
{
v___x_5491_ = v___x_5488_;
goto v_reusejp_5490_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_a_5486_);
v___x_5491_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5490_;
}
v_reusejp_5490_:
{
return v___x_5491_;
}
}
}
}
}
else
{
lean_object* v_code_5517_; lean_object* v___x_5518_; 
v_code_5517_ = lean_ctor_get(v_v_5452_, 0);
lean_inc_ref(v_code_5517_);
v___x_5518_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5517_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_);
if (lean_obj_tag(v___x_5518_) == 0)
{
lean_object* v_a_5519_; lean_object* v___x_5520_; 
v_a_5519_ = lean_ctor_get(v___x_5518_, 0);
lean_inc(v_a_5519_);
lean_dec_ref_known(v___x_5518_, 1);
v___x_5520_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_5452_, v_a_5519_);
v_a_5457_ = v___x_5520_;
goto v___jp_5456_;
}
else
{
lean_object* v_a_5521_; lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5528_; 
lean_dec_ref_known(v_v_5452_, 1);
lean_dec(v___x_5455_);
lean_dec_ref(v_bs_x27_5454_);
lean_dec_ref(v_cases_5439_);
v_a_5521_ = lean_ctor_get(v___x_5518_, 0);
v_isSharedCheck_5528_ = !lean_is_exclusive(v___x_5518_);
if (v_isSharedCheck_5528_ == 0)
{
v___x_5523_ = v___x_5518_;
v_isShared_5524_ = v_isSharedCheck_5528_;
goto v_resetjp_5522_;
}
else
{
lean_inc(v_a_5521_);
lean_dec(v___x_5518_);
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
v___jp_5456_:
{
lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; size_t v___x_5462_; size_t v___x_5463_; lean_object* v___x_5464_; 
v___x_5458_ = lean_st_ref_get(v___y_5444_);
v___x_5459_ = lean_st_ref_take(v___y_5444_);
lean_dec(v___x_5459_);
v___x_5460_ = lean_st_ref_put(v___y_5444_, v___x_5455_);
v___x_5461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5461_, 0, v_a_5457_);
lean_ctor_set(v___x_5461_, 1, v___x_5458_);
v___x_5462_ = ((size_t)1ULL);
v___x_5463_ = lean_usize_add(v_i_5441_, v___x_5462_);
v___x_5464_ = lean_array_uset(v_bs_x27_5454_, v_i_5441_, v___x_5461_);
v_i_5441_ = v___x_5463_;
v_bs_5442_ = v___x_5464_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_cases_5439_ = stack[0].m_obj;
size_t v_sz_5440_ = stack[1].m_num;
size_t v_i_5441_ = stack[2].m_num;
lean_object* v_bs_5442_ = stack[3].m_obj;
lean_object* v___y_5443_ = stack[4].m_obj;
lean_object* v___y_5444_ = stack[5].m_obj;
lean_object* v___y_5445_ = stack[6].m_obj;
lean_object* v___y_5446_ = stack[7].m_obj;
lean_object* v___y_5447_ = stack[8].m_obj;
lean_object* v___y_5448_ = stack[9].m_obj;
lean_object* v_res_5529_;
v_res_5529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(v_cases_5439_, v_sz_5440_, v_i_5441_, v_bs_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_);
stack->m_obj
 = v_res_5529_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6___boxed(lean_object* v_cases_5530_, lean_object* v_sz_5531_, lean_object* v_i_5532_, lean_object* v_bs_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_){
_start:
{
size_t v_sz_boxed_5541_; size_t v_i_boxed_5542_; lean_object* v_res_5543_; 
v_sz_boxed_5541_ = lean_unbox_usize(v_sz_5531_);
lean_dec(v_sz_5531_);
v_i_boxed_5542_ = lean_unbox_usize(v_i_5532_);
lean_dec(v_i_5532_);
v_res_5543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(v_cases_5530_, v_sz_boxed_5541_, v_i_boxed_5542_, v_bs_5533_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_);
lean_dec(v___y_5539_);
lean_dec_ref(v___y_5538_);
lean_dec(v___y_5537_);
lean_dec_ref(v___y_5536_);
lean_dec(v___y_5535_);
lean_dec_ref(v___y_5534_);
return v_res_5543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___boxed(lean_object* v_code_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_){
_start:
{
lean_object* v_res_5552_; 
v_res_5552_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5544_, v_a_5545_, v_a_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_);
lean_dec(v_a_5550_);
lean_dec_ref(v_a_5549_);
lean_dec(v_a_5548_);
lean_dec_ref(v_a_5547_);
lean_dec(v_a_5546_);
lean_dec_ref(v_a_5545_);
return v_res_5552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1(lean_object* v_00_u03b2_5553_, lean_object* v_m_5554_, lean_object* v_a_5555_, lean_object* v_b_5556_){
_start:
{
lean_object* v___x_5557_; 
v___x_5557_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(v_m_5554_, v_a_5555_, v_b_5556_);
return v___x_5557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_5558_, lean_object* v_a_5559_, lean_object* v_b_5560_, lean_object* v_x_5561_){
_start:
{
lean_object* v___x_5562_; 
v___x_5562_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(v_a_5559_, v_b_5560_, v_x_5561_);
return v___x_5562_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(lean_object* v_decl_5563_, lean_object* v_code_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_){
_start:
{
lean_object* v_toSignature_5572_; lean_object* v_params_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; uint8_t v___x_5576_; 
v_toSignature_5572_ = lean_ctor_get(v_decl_5563_, 0);
v_params_5573_ = lean_ctor_get(v_toSignature_5572_, 3);
v___x_5574_ = lean_unsigned_to_nat(0u);
v___x_5575_ = lean_array_get_size(v_params_5573_);
v___x_5576_ = lean_nat_dec_lt(v___x_5574_, v___x_5575_);
if (v___x_5576_ == 0)
{
lean_object* v___x_5577_; 
v___x_5577_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v_a_5578_; lean_object* v___x_5579_; 
v_a_5578_ = lean_ctor_get(v___x_5577_, 0);
lean_inc(v_a_5578_);
lean_dec_ref_known(v___x_5577_, 1);
v___x_5579_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5573_, v_a_5578_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_);
return v___x_5579_;
}
else
{
return v___x_5577_;
}
}
else
{
size_t v___x_5580_; size_t v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; 
v___x_5580_ = ((size_t)0ULL);
v___x_5581_ = lean_usize_of_nat(v___x_5575_);
lean_inc_ref(v_a_5565_);
v___x_5582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_params_5573_, v___x_5580_, v___x_5581_, v_a_5565_);
v___x_5583_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5564_, v___x_5582_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_);
if (lean_obj_tag(v___x_5583_) == 0)
{
lean_object* v_a_5584_; lean_object* v___x_5585_; 
v_a_5584_ = lean_ctor_get(v___x_5583_, 0);
lean_inc(v_a_5584_);
lean_dec_ref_known(v___x_5583_, 1);
v___x_5585_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5573_, v_a_5584_, v___x_5582_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_);
lean_dec_ref(v___x_5582_);
return v___x_5585_;
}
else
{
lean_dec_ref(v___x_5582_);
return v___x_5583_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_5563_ = stack[0].m_obj;
lean_object* v_code_5564_ = stack[1].m_obj;
lean_object* v_a_5565_ = stack[2].m_obj;
lean_object* v_a_5566_ = stack[3].m_obj;
lean_object* v_a_5567_ = stack[4].m_obj;
lean_object* v_a_5568_ = stack[5].m_obj;
lean_object* v_a_5569_ = stack[6].m_obj;
lean_object* v_a_5570_ = stack[7].m_obj;
lean_object* v_res_5586_;
v_res_5586_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(v_decl_5563_, v_code_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_);
stack->m_obj
 = v_res_5586_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go___boxed(lean_object* v_decl_5587_, lean_object* v_code_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_){
_start:
{
lean_object* v_res_5596_; 
v_res_5596_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(v_decl_5587_, v_code_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_);
lean_dec(v_a_5594_);
lean_dec_ref(v_a_5593_);
lean_dec(v_a_5592_);
lean_dec_ref(v_a_5591_);
lean_dec(v_a_5590_);
lean_dec_ref(v_a_5589_);
lean_dec_ref(v_decl_5587_);
return v_res_5596_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(lean_object* v_f_5597_, lean_object* v_v_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_){
_start:
{
if (lean_obj_tag(v_v_5598_) == 0)
{
lean_object* v_code_5604_; lean_object* v___x_5606_; uint8_t v_isShared_5607_; uint8_t v_isSharedCheck_5628_; 
v_code_5604_ = lean_ctor_get(v_v_5598_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v_v_5598_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5606_ = v_v_5598_;
v_isShared_5607_ = v_isSharedCheck_5628_;
goto v_resetjp_5605_;
}
else
{
lean_inc(v_code_5604_);
lean_dec(v_v_5598_);
v___x_5606_ = lean_box(0);
v_isShared_5607_ = v_isSharedCheck_5628_;
goto v_resetjp_5605_;
}
v_resetjp_5605_:
{
lean_object* v___x_5608_; 
lean_inc(v___y_5602_);
lean_inc_ref(v___y_5601_);
lean_inc(v___y_5600_);
lean_inc_ref(v___y_5599_);
v___x_5608_ = lean_apply_6(v_f_5597_, v_code_5604_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, lean_box(0));
if (lean_obj_tag(v___x_5608_) == 0)
{
lean_object* v_a_5609_; lean_object* v___x_5611_; uint8_t v_isShared_5612_; uint8_t v_isSharedCheck_5619_; 
v_a_5609_ = lean_ctor_get(v___x_5608_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5608_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5611_ = v___x_5608_;
v_isShared_5612_ = v_isSharedCheck_5619_;
goto v_resetjp_5610_;
}
else
{
lean_inc(v_a_5609_);
lean_dec(v___x_5608_);
v___x_5611_ = lean_box(0);
v_isShared_5612_ = v_isSharedCheck_5619_;
goto v_resetjp_5610_;
}
v_resetjp_5610_:
{
lean_object* v___x_5614_; 
if (v_isShared_5607_ == 0)
{
lean_ctor_set(v___x_5606_, 0, v_a_5609_);
v___x_5614_ = v___x_5606_;
goto v_reusejp_5613_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_a_5609_);
v___x_5614_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5613_;
}
v_reusejp_5613_:
{
lean_object* v___x_5616_; 
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 0, v___x_5614_);
v___x_5616_ = v___x_5611_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5617_; 
v_reuseFailAlloc_5617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5617_, 0, v___x_5614_);
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
else
{
lean_object* v_a_5620_; lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5627_; 
lean_del_object(v___x_5606_);
v_a_5620_ = lean_ctor_get(v___x_5608_, 0);
v_isSharedCheck_5627_ = !lean_is_exclusive(v___x_5608_);
if (v_isSharedCheck_5627_ == 0)
{
v___x_5622_ = v___x_5608_;
v_isShared_5623_ = v_isSharedCheck_5627_;
goto v_resetjp_5621_;
}
else
{
lean_inc(v_a_5620_);
lean_dec(v___x_5608_);
v___x_5622_ = lean_box(0);
v_isShared_5623_ = v_isSharedCheck_5627_;
goto v_resetjp_5621_;
}
v_resetjp_5621_:
{
lean_object* v___x_5625_; 
if (v_isShared_5623_ == 0)
{
v___x_5625_ = v___x_5622_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5626_; 
v_reuseFailAlloc_5626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5626_, 0, v_a_5620_);
v___x_5625_ = v_reuseFailAlloc_5626_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
return v___x_5625_;
}
}
}
}
}
else
{
lean_object* v___x_5629_; 
lean_dec_ref(v_f_5597_);
v___x_5629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5629_, 0, v_v_5598_);
return v___x_5629_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_5597_ = stack[0].m_obj;
lean_object* v_v_5598_ = stack[1].m_obj;
lean_object* v___y_5599_ = stack[2].m_obj;
lean_object* v___y_5600_ = stack[3].m_obj;
lean_object* v___y_5601_ = stack[4].m_obj;
lean_object* v___y_5602_ = stack[5].m_obj;
lean_object* v_res_5630_;
v_res_5630_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v_f_5597_, v_v_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_);
stack->m_obj
 = v_res_5630_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg___boxed(lean_object* v_f_5631_, lean_object* v_v_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_){
_start:
{
lean_object* v_res_5638_; 
v_res_5638_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v_f_5631_, v_v_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_);
lean_dec(v___y_5636_);
lean_dec_ref(v___y_5635_);
lean_dec(v___y_5634_);
lean_dec_ref(v___y_5633_);
return v_res_5638_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(uint8_t v_pu_5639_, lean_object* v_f_5640_, lean_object* v_v_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_){
_start:
{
lean_object* v___x_5647_; 
v___x_5647_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v_f_5640_, v_v_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_);
return v___x_5647_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_5639_ = stack[0].m_num;
lean_object* v_f_5640_ = stack[1].m_obj;
lean_object* v_v_5641_ = stack[2].m_obj;
lean_object* v___y_5642_ = stack[3].m_obj;
lean_object* v___y_5643_ = stack[4].m_obj;
lean_object* v___y_5644_ = stack[5].m_obj;
lean_object* v___y_5645_ = stack[6].m_obj;
lean_object* v_res_5648_;
v_res_5648_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(v_pu_5639_, v_f_5640_, v_v_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_);
stack->m_obj
 = v_res_5648_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___boxed(lean_object* v_pu_5649_, lean_object* v_f_5650_, lean_object* v_v_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_){
_start:
{
uint8_t v_pu_boxed_5657_; lean_object* v_res_5658_; 
v_pu_boxed_5657_ = lean_unbox(v_pu_5649_);
v_res_5658_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(v_pu_boxed_5657_, v_f_5650_, v_v_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_);
lean_dec(v___y_5655_);
lean_dec_ref(v___y_5654_);
lean_dec(v___y_5653_);
lean_dec_ref(v___y_5652_);
return v_res_5658_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(lean_object* v_decl_5659_, lean_object* v_code_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_){
_start:
{
lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; 
lean_inc_ref(v_code_5660_);
v___x_5666_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets(v_code_5660_);
v___x_5667_ = lean_box(0);
v___x_5668_ = lean_box(1);
v___x_5669_ = lean_unsigned_to_nat(0u);
v___x_5670_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5670_, 0, v___x_5666_);
lean_ctor_set(v___x_5670_, 1, v___x_5667_);
lean_ctor_set(v___x_5670_, 2, v___x_5668_);
lean_ctor_set(v___x_5670_, 3, v___x_5668_);
lean_ctor_set(v___x_5670_, 4, v___x_5668_);
lean_ctor_set(v___x_5670_, 5, v___x_5669_);
v___x_5671_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5672_ = lean_st_mk_ref(v___x_5671_);
v___x_5673_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(v_decl_5659_, v_code_5660_, v___x_5670_, v___x_5672_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
lean_dec_ref_known(v___x_5670_, 6);
if (lean_obj_tag(v___x_5673_) == 0)
{
lean_object* v_a_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5682_; 
v_a_5674_ = lean_ctor_get(v___x_5673_, 0);
v_isSharedCheck_5682_ = !lean_is_exclusive(v___x_5673_);
if (v_isSharedCheck_5682_ == 0)
{
v___x_5676_ = v___x_5673_;
v_isShared_5677_ = v_isSharedCheck_5682_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_a_5674_);
lean_dec(v___x_5673_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5682_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5678_; lean_object* v___x_5680_; 
v___x_5678_ = lean_st_ref_get(v___x_5672_);
lean_dec(v___x_5672_);
lean_dec(v___x_5678_);
if (v_isShared_5677_ == 0)
{
v___x_5680_ = v___x_5676_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v_a_5674_);
v___x_5680_ = v_reuseFailAlloc_5681_;
goto v_reusejp_5679_;
}
v_reusejp_5679_:
{
return v___x_5680_;
}
}
}
else
{
lean_dec(v___x_5672_);
return v___x_5673_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_5659_ = stack[0].m_obj;
lean_object* v_code_5660_ = stack[1].m_obj;
lean_object* v___y_5661_ = stack[2].m_obj;
lean_object* v___y_5662_ = stack[3].m_obj;
lean_object* v___y_5663_ = stack[4].m_obj;
lean_object* v___y_5664_ = stack[5].m_obj;
lean_object* v_res_5683_;
v_res_5683_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(v_decl_5659_, v_code_5660_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
stack->m_obj
 = v_res_5683_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0___boxed(lean_object* v_decl_5684_, lean_object* v_code_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_){
_start:
{
lean_object* v_res_5691_; 
v_res_5691_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(v_decl_5684_, v_code_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_);
lean_dec(v___y_5689_);
lean_dec_ref(v___y_5688_);
lean_dec(v___y_5687_);
lean_dec_ref(v___y_5686_);
lean_dec_ref(v_decl_5684_);
return v_res_5691_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(lean_object* v_decl_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_){
_start:
{
lean_object* v_toSignature_5698_; lean_object* v_value_5699_; uint8_t v_recursive_5700_; lean_object* v_inlineAttr_x3f_5701_; lean_object* v___f_5702_; lean_object* v___x_5703_; 
v_toSignature_5698_ = lean_ctor_get(v_decl_5692_, 0);
lean_inc_ref(v_toSignature_5698_);
v_value_5699_ = lean_ctor_get(v_decl_5692_, 1);
lean_inc_ref(v_value_5699_);
v_recursive_5700_ = lean_ctor_get_uint8(v_decl_5692_, sizeof(void*)*3);
v_inlineAttr_x3f_5701_ = lean_ctor_get(v_decl_5692_, 2);
lean_inc(v_inlineAttr_x3f_5701_);
v___f_5702_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5702_, 0, v_decl_5692_);
v___x_5703_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v___f_5702_, v_value_5699_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_);
if (lean_obj_tag(v___x_5703_) == 0)
{
lean_object* v_a_5704_; lean_object* v___x_5706_; uint8_t v_isShared_5707_; uint8_t v_isSharedCheck_5712_; 
v_a_5704_ = lean_ctor_get(v___x_5703_, 0);
v_isSharedCheck_5712_ = !lean_is_exclusive(v___x_5703_);
if (v_isSharedCheck_5712_ == 0)
{
v___x_5706_ = v___x_5703_;
v_isShared_5707_ = v_isSharedCheck_5712_;
goto v_resetjp_5705_;
}
else
{
lean_inc(v_a_5704_);
lean_dec(v___x_5703_);
v___x_5706_ = lean_box(0);
v_isShared_5707_ = v_isSharedCheck_5712_;
goto v_resetjp_5705_;
}
v_resetjp_5705_:
{
lean_object* v___x_5708_; lean_object* v___x_5710_; 
v___x_5708_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_5708_, 0, v_toSignature_5698_);
lean_ctor_set(v___x_5708_, 1, v_a_5704_);
lean_ctor_set(v___x_5708_, 2, v_inlineAttr_x3f_5701_);
lean_ctor_set_uint8(v___x_5708_, sizeof(void*)*3, v_recursive_5700_);
if (v_isShared_5707_ == 0)
{
lean_ctor_set(v___x_5706_, 0, v___x_5708_);
v___x_5710_ = v___x_5706_;
goto v_reusejp_5709_;
}
else
{
lean_object* v_reuseFailAlloc_5711_; 
v_reuseFailAlloc_5711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5711_, 0, v___x_5708_);
v___x_5710_ = v_reuseFailAlloc_5711_;
goto v_reusejp_5709_;
}
v_reusejp_5709_:
{
return v___x_5710_;
}
}
}
else
{
lean_object* v_a_5713_; lean_object* v___x_5715_; uint8_t v_isShared_5716_; uint8_t v_isSharedCheck_5720_; 
lean_dec(v_inlineAttr_x3f_5701_);
lean_dec_ref(v_toSignature_5698_);
v_a_5713_ = lean_ctor_get(v___x_5703_, 0);
v_isSharedCheck_5720_ = !lean_is_exclusive(v___x_5703_);
if (v_isSharedCheck_5720_ == 0)
{
v___x_5715_ = v___x_5703_;
v_isShared_5716_ = v_isSharedCheck_5720_;
goto v_resetjp_5714_;
}
else
{
lean_inc(v_a_5713_);
lean_dec(v___x_5703_);
v___x_5715_ = lean_box(0);
v_isShared_5716_ = v_isSharedCheck_5720_;
goto v_resetjp_5714_;
}
v_resetjp_5714_:
{
lean_object* v___x_5718_; 
if (v_isShared_5716_ == 0)
{
v___x_5718_ = v___x_5715_;
goto v_reusejp_5717_;
}
else
{
lean_object* v_reuseFailAlloc_5719_; 
v_reuseFailAlloc_5719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5719_, 0, v_a_5713_);
v___x_5718_ = v_reuseFailAlloc_5719_;
goto v_reusejp_5717_;
}
v_reusejp_5717_:
{
return v___x_5718_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_5692_ = stack[0].m_obj;
lean_object* v_a_5693_ = stack[1].m_obj;
lean_object* v_a_5694_ = stack[2].m_obj;
lean_object* v_a_5695_ = stack[3].m_obj;
lean_object* v_a_5696_ = stack[4].m_obj;
lean_object* v_res_5721_;
v_res_5721_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(v_decl_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_);
stack->m_obj
 = v_res_5721_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___boxed(lean_object* v_decl_5722_, lean_object* v_a_5723_, lean_object* v_a_5724_, lean_object* v_a_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_){
_start:
{
lean_object* v_res_5728_; 
v_res_5728_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(v_decl_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_);
lean_dec(v_a_5726_);
lean_dec_ref(v_a_5725_);
lean_dec(v_a_5724_);
lean_dec_ref(v_a_5723_);
return v_res_5728_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(size_t v_sz_5729_, size_t v_i_5730_, lean_object* v_bs_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_){
_start:
{
uint8_t v___x_5737_; 
v___x_5737_ = lean_usize_dec_lt(v_i_5730_, v_sz_5729_);
if (v___x_5737_ == 0)
{
lean_object* v___x_5738_; 
v___x_5738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5738_, 0, v_bs_5731_);
return v___x_5738_;
}
else
{
lean_object* v_v_5739_; lean_object* v___x_5740_; lean_object* v_bs_x27_5741_; lean_object* v___x_5742_; 
v_v_5739_ = lean_array_uget(v_bs_5731_, v_i_5730_);
v___x_5740_ = lean_unsigned_to_nat(0u);
v_bs_x27_5741_ = lean_array_uset(v_bs_5731_, v_i_5730_, v___x_5740_);
v___x_5742_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(v_v_5739_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_);
if (lean_obj_tag(v___x_5742_) == 0)
{
lean_object* v_a_5743_; size_t v___x_5744_; size_t v___x_5745_; lean_object* v___x_5746_; 
v_a_5743_ = lean_ctor_get(v___x_5742_, 0);
lean_inc(v_a_5743_);
lean_dec_ref_known(v___x_5742_, 1);
v___x_5744_ = ((size_t)1ULL);
v___x_5745_ = lean_usize_add(v_i_5730_, v___x_5744_);
v___x_5746_ = lean_array_uset(v_bs_x27_5741_, v_i_5730_, v_a_5743_);
v_i_5730_ = v___x_5745_;
v_bs_5731_ = v___x_5746_;
goto _start;
}
else
{
lean_object* v_a_5748_; lean_object* v___x_5750_; uint8_t v_isShared_5751_; uint8_t v_isSharedCheck_5755_; 
lean_dec_ref(v_bs_x27_5741_);
v_a_5748_ = lean_ctor_get(v___x_5742_, 0);
v_isSharedCheck_5755_ = !lean_is_exclusive(v___x_5742_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5750_ = v___x_5742_;
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
else
{
lean_inc(v_a_5748_);
lean_dec(v___x_5742_);
v___x_5750_ = lean_box(0);
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
v_resetjp_5749_:
{
lean_object* v___x_5753_; 
if (v_isShared_5751_ == 0)
{
v___x_5753_ = v___x_5750_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_a_5748_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_5729_ = stack[0].m_num;
size_t v_i_5730_ = stack[1].m_num;
lean_object* v_bs_5731_ = stack[2].m_obj;
lean_object* v___y_5732_ = stack[3].m_obj;
lean_object* v___y_5733_ = stack[4].m_obj;
lean_object* v___y_5734_ = stack[5].m_obj;
lean_object* v___y_5735_ = stack[6].m_obj;
lean_object* v_res_5756_;
v_res_5756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(v_sz_5729_, v_i_5730_, v_bs_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_);
stack->m_obj
 = v_res_5756_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0___boxed(lean_object* v_sz_5757_, lean_object* v_i_5758_, lean_object* v_bs_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_){
_start:
{
size_t v_sz_boxed_5765_; size_t v_i_boxed_5766_; lean_object* v_res_5767_; 
v_sz_boxed_5765_ = lean_unbox_usize(v_sz_5757_);
lean_dec(v_sz_5757_);
v_i_boxed_5766_ = lean_unbox_usize(v_i_5758_);
lean_dec(v_i_5758_);
v_res_5767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(v_sz_boxed_5765_, v_i_boxed_5766_, v_bs_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_);
lean_dec(v___y_5763_);
lean_dec_ref(v___y_5762_);
lean_dec(v___y_5761_);
lean_dec_ref(v___y_5760_);
return v_res_5767_;
}
}
lean_object* l_Lean_Compiler_LCNF_runExplicitRc(lean_object* v_decls_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_){
_start:
{
size_t v_sz_5774_; size_t v___x_5775_; lean_object* v___x_5776_; 
v_sz_5774_ = lean_array_size(v_decls_5768_);
v___x_5775_ = ((size_t)0ULL);
v___x_5776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(v_sz_5774_, v___x_5775_, v_decls_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_);
return v___x_5776_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_runExplicitRc_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_5768_ = stack[0].m_obj;
lean_object* v_a_5769_ = stack[1].m_obj;
lean_object* v_a_5770_ = stack[2].m_obj;
lean_object* v_a_5771_ = stack[3].m_obj;
lean_object* v_a_5772_ = stack[4].m_obj;
lean_object* v_res_5777_;
v_res_5777_ = l_Lean_Compiler_LCNF_runExplicitRc(v_decls_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_);
stack->m_obj
 = v_res_5777_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc___boxed(lean_object* v_decls_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_){
_start:
{
lean_object* v_res_5784_; 
v_res_5784_ = l_Lean_Compiler_LCNF_runExplicitRc(v_decls_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_);
lean_dec(v_a_5782_);
lean_dec_ref(v_a_5781_);
lean_dec(v_a_5780_);
lean_dec_ref(v_a_5779_);
return v_res_5784_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_explicitRc___closed__3(void){
_start:
{
lean_object* v___x_5789_; lean_object* v___x_5790_; uint8_t v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; 
v___x_5789_ = lean_unsigned_to_nat(0u);
v___x_5790_ = ((lean_object*)(l_Lean_Compiler_LCNF_explicitRc___closed__2));
v___x_5791_ = 2;
v___x_5792_ = ((lean_object*)(l_Lean_Compiler_LCNF_explicitRc___closed__1));
v___x_5793_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_5792_, v___x_5791_, v___x_5790_, v___x_5789_);
return v___x_5793_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_explicitRc(void){
_start:
{
lean_object* v___x_5794_; 
v___x_5794_ = lean_obj_once(&l_Lean_Compiler_LCNF_explicitRc___closed__3, &l_Lean_Compiler_LCNF_explicitRc___closed__3_once, _init_l_Lean_Compiler_LCNF_explicitRc___closed__3);
return v___x_5794_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5850_ = lean_unsigned_to_nat(3791338971u);
v___x_5851_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5852_ = l_Lean_Name_num___override(v___x_5851_, v___x_5850_);
return v___x_5852_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; 
v___x_5854_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5855_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5856_ = l_Lean_Name_str___override(v___x_5855_, v___x_5854_);
return v___x_5856_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; 
v___x_5858_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5859_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5860_ = l_Lean_Name_str___override(v___x_5859_, v___x_5858_);
return v___x_5860_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; 
v___x_5861_ = lean_unsigned_to_nat(2u);
v___x_5862_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5863_ = l_Lean_Name_num___override(v___x_5862_, v___x_5861_);
return v___x_5863_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5865_; uint8_t v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; 
v___x_5865_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5866_ = 1;
v___x_5867_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5868_ = l_Lean_registerTraceClass(v___x_5865_, v___x_5866_, v___x_5867_);
return v___x_5868_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5869_;
v_res_5869_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5869_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2____boxed(lean_object* v_a_5870_){
_start:
{
lean_object* v_res_5871_; 
v_res_5871_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_();
return v_res_5871_;
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
