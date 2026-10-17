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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 205, 20, 178, 155, 84, 168)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "getInternalBorrowed"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__6_value),LEAN_SCALAR_PTR_LITERAL(109, 149, 133, 58, 23, 222, 178, 51)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Compiler.LCNF.ExplicitRC.0.Lean.Compiler.LCNF.LetDecl.explicitRc"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__13;
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
size_t v___x_137_; size_t v___x_138_; lean_object* v___x_139_; 
v___x_137_ = ((size_t)0ULL);
v___x_138_ = lean_usize_of_nat(v___x_135_);
v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(v_alts_133_, v___x_137_, v___x_138_, v_s_117_);
lean_dec_ref(v_alts_133_);
return v___x_139_;
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
lean_object* v_k_140_; 
v_k_140_ = lean_ctor_get(v_code_116_, 3);
lean_inc_ref(v_k_140_);
lean_dec_ref_known(v_code_116_, 4);
v_code_116_ = v_k_140_;
goto _start;
}
case 9:
{
lean_object* v_k_142_; 
v_k_142_ = lean_ctor_get(v_code_116_, 5);
lean_inc_ref(v_k_142_);
lean_dec_ref_known(v_code_116_, 6);
v_code_116_ = v_k_142_;
goto _start;
}
default: 
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec_ref(v_s_117_);
lean_dec_ref(v_code_116_);
v___x_144_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__3);
v___x_145_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__2(v___x_144_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(lean_object* v_as_146_, size_t v_i_147_, size_t v_stop_148_, lean_object* v_b_149_){
_start:
{
lean_object* v___y_151_; uint8_t v___x_156_; 
v___x_156_ = lean_usize_dec_eq(v_i_147_, v_stop_148_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
v___x_157_ = lean_array_uget_borrowed(v_as_146_, v_i_147_);
switch(lean_obj_tag(v___x_157_))
{
case 0:
{
lean_object* v_code_158_; 
v_code_158_ = lean_ctor_get(v___x_157_, 2);
lean_inc_ref(v_code_158_);
v___y_151_ = v_code_158_;
goto v___jp_150_;
}
case 1:
{
lean_object* v_code_159_; 
v_code_159_ = lean_ctor_get(v___x_157_, 1);
lean_inc_ref(v_code_159_);
v___y_151_ = v_code_159_;
goto v___jp_150_;
}
default: 
{
lean_object* v_code_160_; 
v_code_160_ = lean_ctor_get(v___x_157_, 0);
lean_inc_ref(v_code_160_);
v___y_151_ = v_code_160_;
goto v___jp_150_;
}
}
}
else
{
return v_b_149_;
}
v___jp_150_:
{
lean_object* v___x_152_; size_t v___x_153_; size_t v___x_154_; 
v___x_152_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(v___y_151_, v_b_149_);
v___x_153_ = ((size_t)1ULL);
v___x_154_ = lean_usize_add(v_i_147_, v___x_153_);
v_i_147_ = v___x_154_;
v_b_149_ = v___x_152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1___boxed(lean_object* v_as_161_, lean_object* v_i_162_, lean_object* v_stop_163_, lean_object* v_b_164_){
_start:
{
size_t v_i_boxed_165_; size_t v_stop_boxed_166_; lean_object* v_res_167_; 
v_i_boxed_165_ = lean_unbox_usize(v_i_162_);
lean_dec(v_i_162_);
v_stop_boxed_166_ = lean_unbox_usize(v_stop_163_);
lean_dec(v_stop_163_);
v_res_167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__1(v_as_161_, v_i_boxed_165_, v_stop_boxed_166_, v_b_164_);
lean_dec_ref(v_as_161_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0(lean_object* v_00_u03b2_168_, lean_object* v_m_169_, lean_object* v_a_170_, lean_object* v_b_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_m_169_, v_a_170_, v_b_171_);
return v___x_172_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0(lean_object* v_00_u03b2_173_, lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_174_, v_x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_177_, lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0(v_00_u03b2_177_, v_a_178_, v_x_179_);
lean_dec(v_x_179_);
lean_dec(v_a_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1(lean_object* v_00_u03b2_182_, lean_object* v_data_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(v_data_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_185_, lean_object* v_i_186_, lean_object* v_source_187_, lean_object* v_target_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3___redArg(v_i_186_, v_source_187_, v_target_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1_spec__3_spec__5___redArg(v_x_191_, v_x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets(lean_object* v_code_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_196_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go(v_code_194_, v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_box(0);
v___x_204_ = lean_unsigned_to_nat(16u);
v___x_205_ = lean_mk_array(v___x_204_, v___x_203_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__0);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_206_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__1);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
return v___x_211_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_instInhabitedLiveVars(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__0(lean_object* v___x_213_, lean_object* v___x_214_, lean_object* v_a_215_, lean_object* v_b_216_, lean_object* v_acc_217_){
_start:
{
lean_object* v_r_218_; lean_object* v___x_219_; 
v_r_218_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_213_, v___x_214_, v_acc_217_, v_a_215_, v_b_216_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v_r_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___lam__1(lean_object* v___x_220_, lean_object* v___f_221_, lean_object* v_a_222_, lean_object* v_x_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_220_, v___f_221_, v_a_222_, v___y_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union(lean_object* v_liveVars1_255_, lean_object* v_liveVars2_256_){
_start:
{
lean_object* v_vars_257_; lean_object* v_borrows_258_; lean_object* v_vars_259_; lean_object* v_borrows_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_295_; 
v_vars_257_ = lean_ctor_get(v_liveVars1_255_, 0);
lean_inc_ref(v_vars_257_);
v_borrows_258_ = lean_ctor_get(v_liveVars1_255_, 1);
lean_inc_ref(v_borrows_258_);
lean_dec_ref(v_liveVars1_255_);
v_vars_259_ = lean_ctor_get(v_liveVars2_256_, 0);
v_borrows_260_ = lean_ctor_get(v_liveVars2_256_, 1);
v_isSharedCheck_295_ = !lean_is_exclusive(v_liveVars2_256_);
if (v_isSharedCheck_295_ == 0)
{
v___x_262_ = v_liveVars2_256_;
v_isShared_263_ = v_isSharedCheck_295_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_borrows_260_);
lean_inc(v_vars_259_);
lean_dec(v_liveVars2_256_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_295_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v_size_265_; lean_object* v_buckets_266_; lean_object* v_size_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___y_271_; uint8_t v___x_288_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v_size_265_ = lean_ctor_get(v_vars_257_, 0);
v_buckets_266_ = lean_ctor_get(v_vars_257_, 1);
v_size_267_ = lean_ctor_get(v_vars_259_, 0);
v___x_268_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_269_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_288_ = lean_nat_dec_le(v_size_265_, v_size_267_);
if (v___x_288_ == 0)
{
lean_object* v___f_289_; lean_object* v___x_290_; 
v___f_289_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__13));
v___x_290_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_289_, v___x_268_, v___x_269_, v_vars_257_, v_vars_259_);
v___y_271_ = v___x_290_;
goto v___jp_270_;
}
else
{
lean_object* v___f_291_; size_t v_sz_292_; size_t v___x_293_; lean_object* v___x_294_; 
lean_inc_ref(v_buckets_266_);
lean_dec_ref(v_vars_257_);
v___f_291_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__14));
v_sz_292_ = lean_array_size(v_buckets_266_);
v___x_293_ = ((size_t)0ULL);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_264_, v_buckets_266_, v___f_291_, v_sz_292_, v___x_293_, v_vars_259_);
v___y_271_ = v___x_294_;
goto v___jp_270_;
}
v___jp_270_:
{
lean_object* v_size_272_; lean_object* v_buckets_273_; lean_object* v_size_274_; uint8_t v___x_275_; 
v_size_272_ = lean_ctor_get(v_borrows_258_, 0);
v_buckets_273_ = lean_ctor_get(v_borrows_258_, 1);
v_size_274_ = lean_ctor_get(v_borrows_260_, 0);
v___x_275_ = lean_nat_dec_le(v_size_272_, v_size_274_);
if (v___x_275_ == 0)
{
lean_object* v___f_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___f_276_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__13));
v___x_277_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_276_, v___x_268_, v___x_269_, v_borrows_258_, v_borrows_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_277_);
lean_ctor_set(v___x_262_, 0, v___y_271_);
v___x_279_ = v___x_262_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___y_271_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
else
{
lean_object* v___f_281_; size_t v_sz_282_; size_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
lean_inc_ref(v_buckets_273_);
lean_dec_ref(v_borrows_258_);
v___f_281_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__14));
v_sz_282_ = lean_array_size(v_buckets_273_);
v___x_283_ = ((size_t)0ULL);
v___x_284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_264_, v_buckets_273_, v___f_281_, v_sz_282_, v___x_283_, v_borrows_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_284_);
lean_ctor_set(v___x_262_, 0, v___y_271_);
v___x_286_ = v___x_262_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___y_271_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_erase(lean_object* v_liveVars_296_, lean_object* v_fvarId_297_){
_start:
{
lean_object* v_vars_298_; lean_object* v_borrows_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_310_; 
v_vars_298_ = lean_ctor_get(v_liveVars_296_, 0);
v_borrows_299_ = lean_ctor_get(v_liveVars_296_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_liveVars_296_);
if (v_isSharedCheck_310_ == 0)
{
v___x_301_ = v_liveVars_296_;
v_isShared_302_ = v_isSharedCheck_310_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_borrows_299_);
lean_inc(v_vars_298_);
lean_dec(v_liveVars_296_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_310_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_vars_305_; lean_object* v_borrows_306_; lean_object* v___x_308_; 
v___x_303_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_304_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
lean_inc(v_fvarId_297_);
v_vars_305_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_303_, v___x_304_, v_vars_298_, v_fvarId_297_);
v_borrows_306_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_303_, v___x_304_, v_borrows_299_, v_fvarId_297_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v_borrows_306_);
lean_ctor_set(v___x_301_, 0, v_vars_305_);
v___x_308_ = v___x_301_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_vars_305_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_borrows_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_insertBorrow(lean_object* v_liveVars_311_, lean_object* v_fvarId_312_){
_start:
{
lean_object* v_vars_313_; lean_object* v_borrows_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_325_; 
v_vars_313_ = lean_ctor_get(v_liveVars_311_, 0);
v_borrows_314_ = lean_ctor_get(v_liveVars_311_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_liveVars_311_);
if (v_isSharedCheck_325_ == 0)
{
v___x_316_ = v_liveVars_311_;
v_isShared_317_ = v_isSharedCheck_325_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_borrows_314_);
lean_inc(v_vars_313_);
lean_dec(v_liveVars_311_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_325_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_318_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_319_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_320_ = lean_box(0);
v___x_321_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_318_, v___x_319_, v_borrows_314_, v_fvarId_312_, v___x_320_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 1, v___x_321_);
v___x_323_ = v___x_316_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_vars_313_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_insertLive(lean_object* v_liveVars_326_, lean_object* v_fvarId_327_){
_start:
{
lean_object* v_vars_328_; lean_object* v_borrows_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_340_; 
v_vars_328_ = lean_ctor_get(v_liveVars_326_, 0);
v_borrows_329_ = lean_ctor_get(v_liveVars_326_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_liveVars_326_);
if (v_isSharedCheck_340_ == 0)
{
v___x_331_ = v_liveVars_326_;
v_isShared_332_ = v_isSharedCheck_340_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_borrows_329_);
lean_inc(v_vars_328_);
lean_dec(v_liveVars_326_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_340_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_333_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_334_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_335_ = lean_box(0);
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_333_, v___x_334_, v_vars_328_, v_fvarId_327_, v___x_335_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_336_);
v___x_338_ = v___x_331_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_borrows_329_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(lean_object* v_fvarId_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_varMap_352_; lean_object* v___f_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_varMap_352_ = lean_ctor_get(v_a_350_, 3);
v___f_353_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_354_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_varMap_352_);
v___x_355_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_353_, v___x_354_, v_varMap_352_, v_fvarId_349_);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___boxed(lean_object* v_fvarId_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg(v_fvarId_357_, v_a_358_);
lean_dec_ref(v_a_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(lean_object* v_fvarId_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_varMap_369_; lean_object* v___f_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_varMap_369_ = lean_ctor_get(v_a_362_, 3);
v___f_370_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_371_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_varMap_369_);
v___x_372_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_370_, v___x_371_, v_varMap_369_, v_fvarId_361_);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___boxed(lean_object* v_fvarId_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo(v_fvarId_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(lean_object* v_fvarId_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_jpLiveVarMap_386_; lean_object* v___f_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_jpLiveVarMap_386_ = lean_ctor_get(v_a_384_, 4);
v___f_387_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_388_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
lean_inc(v_jpLiveVarMap_386_);
v___x_389_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_387_, v___x_388_, v_jpLiveVarMap_386_, v_fvarId_383_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg___boxed(lean_object* v_fvarId_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___redArg(v_fvarId_391_, v_a_392_);
lean_dec_ref(v_a_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(lean_object* v_fvarId_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_jpLiveVarMap_403_; lean_object* v___f_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_jpLiveVarMap_403_ = lean_ctor_get(v_a_396_, 4);
v___f_404_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_405_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
lean_inc(v_jpLiveVarMap_403_);
v___x_406_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_404_, v___x_405_, v_jpLiveVarMap_403_, v_fvarId_395_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars___boxed(lean_object* v_fvarId_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getJpLiveVars(v_fvarId_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg(lean_object* v_fvarId_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_vars_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_420_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_421_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_422_ = lean_st_ref_get(v_a_418_);
v_vars_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_ref(v_vars_423_);
lean_dec(v___x_422_);
v___x_424_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_420_, v___x_421_, v_vars_423_, v_fvarId_417_);
lean_dec_ref(v_vars_423_);
v___x_425_ = lean_box(v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg___boxed(lean_object* v_fvarId_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___redArg(v_fvarId_427_, v_a_428_);
lean_dec(v_a_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(lean_object* v_fvarId_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_vars_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_439_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_440_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_441_ = lean_st_ref_get(v_a_433_);
v_vars_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc_ref(v_vars_442_);
lean_dec(v___x_441_);
v___x_443_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_439_, v___x_440_, v_vars_442_, v_fvarId_431_);
lean_dec_ref(v_vars_442_);
v___x_444_ = lean_box(v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive___boxed(lean_object* v_fvarId_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isLive(v_fvarId_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(lean_object* v_fvarId_455_, lean_object* v_a_456_){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v_borrows_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_458_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_459_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_460_ = lean_st_ref_get(v_a_456_);
v_borrows_461_ = lean_ctor_get(v___x_460_, 1);
lean_inc_ref(v_borrows_461_);
lean_dec(v___x_460_);
v___x_462_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_458_, v___x_459_, v_borrows_461_, v_fvarId_455_);
lean_dec_ref(v_borrows_461_);
v___x_463_ = lean_box(v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg___boxed(lean_object* v_fvarId_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___redArg(v_fvarId_465_, v_a_466_);
lean_dec(v_a_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(lean_object* v_fvarId_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_borrows_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_478_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_479_ = lean_st_ref_get(v_a_471_);
v_borrows_480_ = lean_ctor_get(v___x_479_, 1);
lean_inc_ref(v_borrows_480_);
lean_dec(v___x_479_);
v___x_481_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_477_, v___x_478_, v_borrows_480_, v_fvarId_469_);
lean_dec_ref(v_borrows_480_);
v___x_482_ = lean_box(v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed___boxed(lean_object* v_fvarId_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowed(v_fvarId_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(lean_object* v_f_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_496_ = lean_st_ref_take(v_a_494_);
v___x_497_ = lean_box(0);
v___x_498_ = lean_apply_1(v_f_493_, v___x_496_);
v___x_499_ = lean_st_ref_put(v_a_494_, v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_497_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg___boxed(lean_object* v_f_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___redArg(v_f_501_, v_a_502_);
lean_dec(v_a_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(lean_object* v_f_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_513_ = lean_st_ref_take(v_a_507_);
v___x_514_ = lean_box(0);
v___x_515_ = lean_apply_1(v_f_505_, v___x_513_);
v___x_516_ = lean_st_ref_put(v_a_507_, v___x_515_);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_514_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive___boxed(lean_object* v_f_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_modifyLive(v_f_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(lean_object* v_child_527_, lean_object* v_k_528_, lean_object* v_t_529_){
_start:
{
if (lean_obj_tag(v_t_529_) == 0)
{
lean_object* v_size_530_; lean_object* v_k_531_; lean_object* v_v_532_; lean_object* v_l_533_; lean_object* v_r_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_560_; 
v_size_530_ = lean_ctor_get(v_t_529_, 0);
v_k_531_ = lean_ctor_get(v_t_529_, 1);
v_v_532_ = lean_ctor_get(v_t_529_, 2);
v_l_533_ = lean_ctor_get(v_t_529_, 3);
v_r_534_ = lean_ctor_get(v_t_529_, 4);
v_isSharedCheck_560_ = !lean_is_exclusive(v_t_529_);
if (v_isSharedCheck_560_ == 0)
{
v___x_536_ = v_t_529_;
v_isShared_537_ = v_isSharedCheck_560_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_r_534_);
lean_inc(v_l_533_);
lean_inc(v_v_532_);
lean_inc(v_k_531_);
lean_inc(v_size_530_);
lean_dec(v_t_529_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_560_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
uint8_t v___x_538_; 
v___x_538_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_528_, v_k_531_);
switch(v___x_538_)
{
case 0:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(v_child_527_, v_k_528_, v_l_533_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 3, v___x_539_);
v___x_541_ = v___x_536_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_size_530_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_k_531_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_v_532_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_r_534_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
case 1:
{
lean_object* v_parents_543_; lean_object* v_children_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_555_; 
lean_dec(v_k_531_);
v_parents_543_ = lean_ctor_get(v_v_532_, 0);
v_children_544_ = lean_ctor_get(v_v_532_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_v_532_);
if (v_isSharedCheck_555_ == 0)
{
v___x_546_ = v_v_532_;
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_children_544_);
lean_inc(v_parents_543_);
lean_dec(v_v_532_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_548_, 0, v_child_527_);
lean_ctor_set(v___x_548_, 1, v_children_544_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___x_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_parents_543_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_548_);
v___x_550_ = v_reuseFailAlloc_554_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 2, v___x_550_);
lean_ctor_set(v___x_536_, 1, v_k_528_);
v___x_552_ = v___x_536_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_size_530_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_l_533_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_r_534_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
default: 
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(v_child_527_, v_k_528_, v_r_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 4, v___x_556_);
v___x_558_ = v___x_536_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_size_530_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_k_531_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_v_532_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_l_533_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
else
{
lean_dec(v_k_528_);
lean_dec(v_child_527_);
return v_t_529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(lean_object* v_child_561_, lean_object* v_as_562_, size_t v_i_563_, size_t v_stop_564_, lean_object* v_b_565_){
_start:
{
uint8_t v___x_566_; 
v___x_566_ = lean_usize_dec_eq(v_i_563_, v_stop_564_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; size_t v___x_569_; size_t v___x_570_; 
v___x_567_ = lean_array_uget_borrowed(v_as_562_, v_i_563_);
lean_inc(v___x_567_);
lean_inc(v_child_561_);
v___x_568_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__0(v_child_561_, v___x_567_, v_b_565_);
v___x_569_ = ((size_t)1ULL);
v___x_570_ = lean_usize_add(v_i_563_, v___x_569_);
v_i_563_ = v___x_570_;
v_b_565_ = v___x_568_;
goto _start;
}
else
{
lean_dec(v_child_561_);
return v_b_565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3___boxed(lean_object* v_child_572_, lean_object* v_as_573_, lean_object* v_i_574_, lean_object* v_stop_575_, lean_object* v_b_576_){
_start:
{
size_t v_i_boxed_577_; size_t v_stop_boxed_578_; lean_object* v_res_579_; 
v_i_boxed_577_ = lean_unbox_usize(v_i_574_);
lean_dec(v_i_574_);
v_stop_boxed_578_ = lean_unbox_usize(v_stop_575_);
lean_dec(v_stop_575_);
v_res_579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(v_child_572_, v_as_573_, v_i_boxed_577_, v_stop_boxed_578_, v_b_576_);
lean_dec_ref(v_as_573_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(lean_object* v_k_580_, lean_object* v_v_581_, lean_object* v_t_582_){
_start:
{
if (lean_obj_tag(v_t_582_) == 0)
{
lean_object* v_size_583_; lean_object* v_k_584_; lean_object* v_v_585_; lean_object* v_l_586_; lean_object* v_r_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_867_; 
v_size_583_ = lean_ctor_get(v_t_582_, 0);
v_k_584_ = lean_ctor_get(v_t_582_, 1);
v_v_585_ = lean_ctor_get(v_t_582_, 2);
v_l_586_ = lean_ctor_get(v_t_582_, 3);
v_r_587_ = lean_ctor_get(v_t_582_, 4);
v_isSharedCheck_867_ = !lean_is_exclusive(v_t_582_);
if (v_isSharedCheck_867_ == 0)
{
v___x_589_ = v_t_582_;
v_isShared_590_ = v_isSharedCheck_867_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_r_587_);
lean_inc(v_l_586_);
lean_inc(v_v_585_);
lean_inc(v_k_584_);
lean_inc(v_size_583_);
lean_dec(v_t_582_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_867_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
uint8_t v___x_591_; 
v___x_591_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_580_, v_k_584_);
switch(v___x_591_)
{
case 0:
{
lean_object* v_impl_592_; lean_object* v___x_593_; 
lean_dec(v_size_583_);
v_impl_592_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_k_580_, v_v_581_, v_l_586_);
v___x_593_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_587_) == 0)
{
lean_object* v_size_594_; lean_object* v_size_595_; lean_object* v_k_596_; lean_object* v_v_597_; lean_object* v_l_598_; lean_object* v_r_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_size_594_ = lean_ctor_get(v_r_587_, 0);
v_size_595_ = lean_ctor_get(v_impl_592_, 0);
v_k_596_ = lean_ctor_get(v_impl_592_, 1);
v_v_597_ = lean_ctor_get(v_impl_592_, 2);
v_l_598_ = lean_ctor_get(v_impl_592_, 3);
v_r_599_ = lean_ctor_get(v_impl_592_, 4);
lean_inc(v_r_599_);
v___x_600_ = lean_unsigned_to_nat(3u);
v___x_601_ = lean_nat_mul(v___x_600_, v_size_594_);
v___x_602_ = lean_nat_dec_lt(v___x_601_, v_size_595_);
lean_dec(v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
lean_dec(v_r_599_);
v___x_603_ = lean_nat_add(v___x_593_, v_size_595_);
v___x_604_ = lean_nat_add(v___x_603_, v_size_594_);
lean_dec(v___x_603_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 3, v_impl_592_);
lean_ctor_set(v___x_589_, 0, v___x_604_);
v___x_606_ = v___x_589_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v_impl_592_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v_r_587_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
else
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_673_; 
lean_inc(v_l_598_);
lean_inc(v_v_597_);
lean_inc(v_k_596_);
lean_inc(v_size_595_);
v_isSharedCheck_673_ = !lean_is_exclusive(v_impl_592_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; lean_object* v_unused_675_; lean_object* v_unused_676_; lean_object* v_unused_677_; lean_object* v_unused_678_; 
v_unused_674_ = lean_ctor_get(v_impl_592_, 4);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v_impl_592_, 3);
lean_dec(v_unused_675_);
v_unused_676_ = lean_ctor_get(v_impl_592_, 2);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v_impl_592_, 1);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_impl_592_, 0);
lean_dec(v_unused_678_);
v___x_609_ = v_impl_592_;
v_isShared_610_ = v_isSharedCheck_673_;
goto v_resetjp_608_;
}
else
{
lean_dec(v_impl_592_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_673_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v_size_611_; lean_object* v_size_612_; lean_object* v_k_613_; lean_object* v_v_614_; lean_object* v_l_615_; lean_object* v_r_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_size_611_ = lean_ctor_get(v_l_598_, 0);
v_size_612_ = lean_ctor_get(v_r_599_, 0);
v_k_613_ = lean_ctor_get(v_r_599_, 1);
v_v_614_ = lean_ctor_get(v_r_599_, 2);
v_l_615_ = lean_ctor_get(v_r_599_, 3);
v_r_616_ = lean_ctor_get(v_r_599_, 4);
v___x_617_ = lean_unsigned_to_nat(2u);
v___x_618_ = lean_nat_mul(v___x_617_, v_size_611_);
v___x_619_ = lean_nat_dec_lt(v_size_612_, v___x_618_);
lean_dec(v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_648_; 
lean_inc(v_r_616_);
lean_inc(v_l_615_);
lean_inc(v_v_614_);
lean_inc(v_k_613_);
v_isSharedCheck_648_ = !lean_is_exclusive(v_r_599_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; lean_object* v_unused_653_; 
v_unused_649_ = lean_ctor_get(v_r_599_, 4);
lean_dec(v_unused_649_);
v_unused_650_ = lean_ctor_get(v_r_599_, 3);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_r_599_, 2);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_r_599_, 1);
lean_dec(v_unused_652_);
v_unused_653_ = lean_ctor_get(v_r_599_, 0);
lean_dec(v_unused_653_);
v___x_621_ = v_r_599_;
v_isShared_622_ = v_isSharedCheck_648_;
goto v_resetjp_620_;
}
else
{
lean_dec(v_r_599_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_648_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___x_636_; lean_object* v___y_638_; 
v___x_623_ = lean_nat_add(v___x_593_, v_size_595_);
lean_dec(v_size_595_);
v___x_624_ = lean_nat_add(v___x_623_, v_size_594_);
lean_dec(v___x_623_);
v___x_636_ = lean_nat_add(v___x_593_, v_size_611_);
if (lean_obj_tag(v_l_615_) == 0)
{
lean_object* v_size_646_; 
v_size_646_ = lean_ctor_get(v_l_615_, 0);
lean_inc(v_size_646_);
v___y_638_ = v_size_646_;
goto v___jp_637_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___y_638_ = v___x_647_;
goto v___jp_637_;
}
v___jp_625_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = lean_nat_add(v___y_626_, v___y_628_);
lean_dec(v___y_628_);
lean_dec(v___y_626_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v_r_587_);
lean_ctor_set(v___x_621_, 3, v_r_616_);
lean_ctor_set(v___x_621_, 2, v_v_585_);
lean_ctor_set(v___x_621_, 1, v_k_584_);
lean_ctor_set(v___x_621_, 0, v___x_629_);
v___x_631_ = v___x_621_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_r_616_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v_r_587_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 4, v___x_631_);
lean_ctor_set(v___x_609_, 3, v___y_627_);
lean_ctor_set(v___x_609_, 2, v_v_614_);
lean_ctor_set(v___x_609_, 1, v_k_613_);
lean_ctor_set(v___x_609_, 0, v___x_624_);
v___x_633_ = v___x_609_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_k_613_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_v_614_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v___y_627_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
v___jp_637_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = lean_nat_add(v___x_636_, v___y_638_);
lean_dec(v___y_638_);
lean_dec(v___x_636_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 4, v_l_615_);
lean_ctor_set(v___x_589_, 3, v_l_598_);
lean_ctor_set(v___x_589_, 2, v_v_597_);
lean_ctor_set(v___x_589_, 1, v_k_596_);
lean_ctor_set(v___x_589_, 0, v___x_639_);
v___x_641_ = v___x_589_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_645_, 3, v_l_598_);
lean_ctor_set(v_reuseFailAlloc_645_, 4, v_l_615_);
v___x_641_ = v_reuseFailAlloc_645_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; 
v___x_642_ = lean_nat_add(v___x_593_, v_size_594_);
if (lean_obj_tag(v_r_616_) == 0)
{
lean_object* v_size_643_; 
v_size_643_ = lean_ctor_get(v_r_616_, 0);
lean_inc(v_size_643_);
v___y_626_ = v___x_642_;
v___y_627_ = v___x_641_;
v___y_628_ = v_size_643_;
goto v___jp_625_;
}
else
{
lean_object* v___x_644_; 
v___x_644_ = lean_unsigned_to_nat(0u);
v___y_626_ = v___x_642_;
v___y_627_ = v___x_641_;
v___y_628_ = v___x_644_;
goto v___jp_625_;
}
}
}
}
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
lean_del_object(v___x_589_);
v___x_654_ = lean_nat_add(v___x_593_, v_size_595_);
lean_dec(v_size_595_);
v___x_655_ = lean_nat_add(v___x_654_, v_size_594_);
lean_dec(v___x_654_);
v___x_656_ = lean_nat_add(v___x_593_, v_size_594_);
v___x_657_ = lean_nat_add(v___x_656_, v_size_612_);
lean_dec(v___x_656_);
lean_inc_ref(v_r_587_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 4, v_r_587_);
lean_ctor_set(v___x_609_, 3, v_r_599_);
lean_ctor_set(v___x_609_, 2, v_v_585_);
lean_ctor_set(v___x_609_, 1, v_k_584_);
lean_ctor_set(v___x_609_, 0, v___x_657_);
v___x_659_ = v___x_609_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_r_599_);
lean_ctor_set(v_reuseFailAlloc_672_, 4, v_r_587_);
v___x_659_ = v_reuseFailAlloc_672_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v_isSharedCheck_666_ = !lean_is_exclusive(v_r_587_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; lean_object* v_unused_668_; lean_object* v_unused_669_; lean_object* v_unused_670_; lean_object* v_unused_671_; 
v_unused_667_ = lean_ctor_get(v_r_587_, 4);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_r_587_, 3);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v_r_587_, 2);
lean_dec(v_unused_669_);
v_unused_670_ = lean_ctor_get(v_r_587_, 1);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_r_587_, 0);
lean_dec(v_unused_671_);
v___x_661_ = v_r_587_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_dec(v_r_587_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 4, v___x_659_);
lean_ctor_set(v___x_661_, 3, v_l_598_);
lean_ctor_set(v___x_661_, 2, v_v_597_);
lean_ctor_set(v___x_661_, 1, v_k_596_);
lean_ctor_set(v___x_661_, 0, v___x_655_);
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_k_596_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_v_597_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v_l_598_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v___x_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_679_; 
v_l_679_ = lean_ctor_get(v_impl_592_, 3);
if (lean_obj_tag(v_l_679_) == 0)
{
lean_object* v_r_680_; lean_object* v_k_681_; lean_object* v_v_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_693_; 
lean_inc_ref(v_l_679_);
v_r_680_ = lean_ctor_get(v_impl_592_, 4);
v_k_681_ = lean_ctor_get(v_impl_592_, 1);
v_v_682_ = lean_ctor_get(v_impl_592_, 2);
v_isSharedCheck_693_ = !lean_is_exclusive(v_impl_592_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; lean_object* v_unused_695_; 
v_unused_694_ = lean_ctor_get(v_impl_592_, 3);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_impl_592_, 0);
lean_dec(v_unused_695_);
v___x_684_ = v_impl_592_;
v_isShared_685_ = v_isSharedCheck_693_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_r_680_);
lean_inc(v_v_682_);
lean_inc(v_k_681_);
lean_dec(v_impl_592_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_693_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_680_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 3, v_r_680_);
lean_ctor_set(v___x_684_, 2, v_v_585_);
lean_ctor_set(v___x_684_, 1, v_k_584_);
lean_ctor_set(v___x_684_, 0, v___x_593_);
v___x_688_ = v___x_684_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_r_680_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_r_680_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_690_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 4, v___x_688_);
lean_ctor_set(v___x_589_, 3, v_l_679_);
lean_ctor_set(v___x_589_, 2, v_v_682_);
lean_ctor_set(v___x_589_, 1, v_k_681_);
lean_ctor_set(v___x_589_, 0, v___x_686_);
v___x_690_ = v___x_589_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_k_681_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_v_682_);
lean_ctor_set(v_reuseFailAlloc_691_, 3, v_l_679_);
lean_ctor_set(v_reuseFailAlloc_691_, 4, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_object* v_r_696_; 
v_r_696_ = lean_ctor_get(v_impl_592_, 4);
lean_inc(v_r_696_);
if (lean_obj_tag(v_r_696_) == 0)
{
lean_object* v_k_697_; lean_object* v_v_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_721_; 
lean_inc(v_l_679_);
v_k_697_ = lean_ctor_get(v_impl_592_, 1);
v_v_698_ = lean_ctor_get(v_impl_592_, 2);
v_isSharedCheck_721_ = !lean_is_exclusive(v_impl_592_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; 
v_unused_722_ = lean_ctor_get(v_impl_592_, 4);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_impl_592_, 3);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_impl_592_, 0);
lean_dec(v_unused_724_);
v___x_700_ = v_impl_592_;
v_isShared_701_ = v_isSharedCheck_721_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_v_698_);
lean_inc(v_k_697_);
lean_dec(v_impl_592_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_721_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v_k_702_; lean_object* v_v_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_717_; 
v_k_702_ = lean_ctor_get(v_r_696_, 1);
v_v_703_ = lean_ctor_get(v_r_696_, 2);
v_isSharedCheck_717_ = !lean_is_exclusive(v_r_696_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; lean_object* v_unused_719_; lean_object* v_unused_720_; 
v_unused_718_ = lean_ctor_get(v_r_696_, 4);
lean_dec(v_unused_718_);
v_unused_719_ = lean_ctor_get(v_r_696_, 3);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_r_696_, 0);
lean_dec(v_unused_720_);
v___x_705_ = v_r_696_;
v_isShared_706_ = v_isSharedCheck_717_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_v_703_);
lean_inc(v_k_702_);
lean_dec(v_r_696_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_717_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = lean_unsigned_to_nat(3u);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v_l_679_);
lean_ctor_set(v___x_705_, 3, v_l_679_);
lean_ctor_set(v___x_705_, 2, v_v_698_);
lean_ctor_set(v___x_705_, 1, v_k_697_);
lean_ctor_set(v___x_705_, 0, v___x_593_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_k_697_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_v_698_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_l_679_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v_l_679_);
v___x_709_ = v_reuseFailAlloc_716_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 4, v_l_679_);
lean_ctor_set(v___x_700_, 2, v_v_585_);
lean_ctor_set(v___x_700_, 1, v_k_584_);
lean_ctor_set(v___x_700_, 0, v___x_593_);
v___x_711_ = v___x_700_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_l_679_);
lean_ctor_set(v_reuseFailAlloc_715_, 4, v_l_679_);
v___x_711_ = v_reuseFailAlloc_715_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 4, v___x_711_);
lean_ctor_set(v___x_589_, 3, v___x_709_);
lean_ctor_set(v___x_589_, 2, v_v_703_);
lean_ctor_set(v___x_589_, 1, v_k_702_);
lean_ctor_set(v___x_589_, 0, v___x_707_);
v___x_713_ = v___x_589_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_k_702_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v_v_703_);
lean_ctor_set(v_reuseFailAlloc_714_, 3, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_714_, 4, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = lean_unsigned_to_nat(2u);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 4, v_r_696_);
lean_ctor_set(v___x_589_, 3, v_impl_592_);
lean_ctor_set(v___x_589_, 0, v___x_725_);
v___x_727_ = v___x_589_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_impl_592_);
lean_ctor_set(v_reuseFailAlloc_728_, 4, v_r_696_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
case 1:
{
lean_object* v___x_730_; 
lean_dec(v_v_585_);
lean_dec(v_k_584_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 2, v_v_581_);
lean_ctor_set(v___x_589_, 1, v_k_580_);
v___x_730_ = v___x_589_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_size_583_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_k_580_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_v_581_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v_l_586_);
lean_ctor_set(v_reuseFailAlloc_731_, 4, v_r_587_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
default: 
{
lean_object* v_impl_732_; lean_object* v___x_733_; 
lean_dec(v_size_583_);
v_impl_732_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_k_580_, v_v_581_, v_r_587_);
v___x_733_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_586_) == 0)
{
lean_object* v_size_734_; lean_object* v_size_735_; lean_object* v_k_736_; lean_object* v_v_737_; lean_object* v_l_738_; lean_object* v_r_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_size_734_ = lean_ctor_get(v_l_586_, 0);
v_size_735_ = lean_ctor_get(v_impl_732_, 0);
v_k_736_ = lean_ctor_get(v_impl_732_, 1);
v_v_737_ = lean_ctor_get(v_impl_732_, 2);
v_l_738_ = lean_ctor_get(v_impl_732_, 3);
lean_inc(v_l_738_);
v_r_739_ = lean_ctor_get(v_impl_732_, 4);
v___x_740_ = lean_unsigned_to_nat(3u);
v___x_741_ = lean_nat_mul(v___x_740_, v_size_734_);
v___x_742_ = lean_nat_dec_lt(v___x_741_, v_size_735_);
lean_dec(v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
lean_dec(v_l_738_);
v___x_743_ = lean_nat_add(v___x_733_, v_size_734_);
v___x_744_ = lean_nat_add(v___x_743_, v_size_735_);
lean_dec(v___x_743_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 4, v_impl_732_);
lean_ctor_set(v___x_589_, 0, v___x_744_);
v___x_746_ = v___x_589_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_l_586_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_impl_732_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_811_; 
lean_inc(v_r_739_);
lean_inc(v_v_737_);
lean_inc(v_k_736_);
lean_inc(v_size_735_);
v_isSharedCheck_811_ = !lean_is_exclusive(v_impl_732_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; lean_object* v_unused_813_; lean_object* v_unused_814_; lean_object* v_unused_815_; lean_object* v_unused_816_; 
v_unused_812_ = lean_ctor_get(v_impl_732_, 4);
lean_dec(v_unused_812_);
v_unused_813_ = lean_ctor_get(v_impl_732_, 3);
lean_dec(v_unused_813_);
v_unused_814_ = lean_ctor_get(v_impl_732_, 2);
lean_dec(v_unused_814_);
v_unused_815_ = lean_ctor_get(v_impl_732_, 1);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v_impl_732_, 0);
lean_dec(v_unused_816_);
v___x_749_ = v_impl_732_;
v_isShared_750_ = v_isSharedCheck_811_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_impl_732_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_811_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_size_751_; lean_object* v_k_752_; lean_object* v_v_753_; lean_object* v_l_754_; lean_object* v_r_755_; lean_object* v_size_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_size_751_ = lean_ctor_get(v_l_738_, 0);
v_k_752_ = lean_ctor_get(v_l_738_, 1);
v_v_753_ = lean_ctor_get(v_l_738_, 2);
v_l_754_ = lean_ctor_get(v_l_738_, 3);
v_r_755_ = lean_ctor_get(v_l_738_, 4);
v_size_756_ = lean_ctor_get(v_r_739_, 0);
v___x_757_ = lean_unsigned_to_nat(2u);
v___x_758_ = lean_nat_mul(v___x_757_, v_size_756_);
v___x_759_ = lean_nat_dec_lt(v_size_751_, v___x_758_);
lean_dec(v___x_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_787_; 
lean_inc(v_r_755_);
lean_inc(v_l_754_);
lean_inc(v_v_753_);
lean_inc(v_k_752_);
v_isSharedCheck_787_ = !lean_is_exclusive(v_l_738_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; lean_object* v_unused_789_; lean_object* v_unused_790_; lean_object* v_unused_791_; lean_object* v_unused_792_; 
v_unused_788_ = lean_ctor_get(v_l_738_, 4);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_l_738_, 3);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_l_738_, 2);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v_l_738_, 1);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_l_738_, 0);
lean_dec(v_unused_792_);
v___x_761_ = v_l_738_;
v_isShared_762_ = v_isSharedCheck_787_;
goto v_resetjp_760_;
}
else
{
lean_dec(v_l_738_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_787_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_777_; 
v___x_763_ = lean_nat_add(v___x_733_, v_size_734_);
v___x_764_ = lean_nat_add(v___x_763_, v_size_735_);
lean_dec(v_size_735_);
if (lean_obj_tag(v_l_754_) == 0)
{
lean_object* v_size_785_; 
v_size_785_ = lean_ctor_get(v_l_754_, 0);
lean_inc(v_size_785_);
v___y_777_ = v_size_785_;
goto v___jp_776_;
}
else
{
lean_object* v___x_786_; 
v___x_786_ = lean_unsigned_to_nat(0u);
v___y_777_ = v___x_786_;
goto v___jp_776_;
}
v___jp_765_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_nat_add(v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec(v___y_767_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 4, v_r_739_);
lean_ctor_set(v___x_761_, 3, v_r_755_);
lean_ctor_set(v___x_761_, 2, v_v_737_);
lean_ctor_set(v___x_761_, 1, v_k_736_);
lean_ctor_set(v___x_761_, 0, v___x_769_);
v___x_771_ = v___x_761_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_k_736_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_v_737_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_r_755_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_r_739_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 4, v___x_771_);
lean_ctor_set(v___x_749_, 3, v___y_766_);
lean_ctor_set(v___x_749_, 2, v_v_753_);
lean_ctor_set(v___x_749_, 1, v_k_752_);
lean_ctor_set(v___x_749_, 0, v___x_764_);
v___x_773_ = v___x_749_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_k_752_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_v_753_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v___y_766_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
v___jp_776_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_nat_add(v___x_763_, v___y_777_);
lean_dec(v___y_777_);
lean_dec(v___x_763_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 4, v_l_754_);
lean_ctor_set(v___x_589_, 0, v___x_778_);
v___x_780_ = v___x_589_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_l_586_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_l_754_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; 
v___x_781_ = lean_nat_add(v___x_733_, v_size_756_);
if (lean_obj_tag(v_r_755_) == 0)
{
lean_object* v_size_782_; 
v_size_782_ = lean_ctor_get(v_r_755_, 0);
lean_inc(v_size_782_);
v___y_766_ = v___x_780_;
v___y_767_ = v___x_781_;
v___y_768_ = v_size_782_;
goto v___jp_765_;
}
else
{
lean_object* v___x_783_; 
v___x_783_ = lean_unsigned_to_nat(0u);
v___y_766_ = v___x_780_;
v___y_767_ = v___x_781_;
v___y_768_ = v___x_783_;
goto v___jp_765_;
}
}
}
}
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
lean_del_object(v___x_589_);
v___x_793_ = lean_nat_add(v___x_733_, v_size_734_);
v___x_794_ = lean_nat_add(v___x_793_, v_size_735_);
lean_dec(v_size_735_);
v___x_795_ = lean_nat_add(v___x_793_, v_size_751_);
lean_dec(v___x_793_);
lean_inc_ref(v_l_586_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 4, v_l_738_);
lean_ctor_set(v___x_749_, 3, v_l_586_);
lean_ctor_set(v___x_749_, 2, v_v_585_);
lean_ctor_set(v___x_749_, 1, v_k_584_);
lean_ctor_set(v___x_749_, 0, v___x_795_);
v___x_797_ = v___x_749_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_810_, 3, v_l_586_);
lean_ctor_set(v_reuseFailAlloc_810_, 4, v_l_738_);
v___x_797_ = v_reuseFailAlloc_810_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_isSharedCheck_804_ = !lean_is_exclusive(v_l_586_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; lean_object* v_unused_806_; lean_object* v_unused_807_; lean_object* v_unused_808_; lean_object* v_unused_809_; 
v_unused_805_ = lean_ctor_get(v_l_586_, 4);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_l_586_, 3);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_l_586_, 2);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_l_586_, 1);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_l_586_, 0);
lean_dec(v_unused_809_);
v___x_799_ = v_l_586_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_dec(v_l_586_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 4, v_r_739_);
lean_ctor_set(v___x_799_, 3, v___x_797_);
lean_ctor_set(v___x_799_, 2, v_v_737_);
lean_ctor_set(v___x_799_, 1, v_k_736_);
lean_ctor_set(v___x_799_, 0, v___x_794_);
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_k_736_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v_v_737_);
lean_ctor_set(v_reuseFailAlloc_803_, 3, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_803_, 4, v_r_739_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_817_; 
v_l_817_ = lean_ctor_get(v_impl_732_, 3);
lean_inc(v_l_817_);
if (lean_obj_tag(v_l_817_) == 0)
{
lean_object* v_r_818_; lean_object* v_k_819_; lean_object* v_v_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_843_; 
v_r_818_ = lean_ctor_get(v_impl_732_, 4);
v_k_819_ = lean_ctor_get(v_impl_732_, 1);
v_v_820_ = lean_ctor_get(v_impl_732_, 2);
v_isSharedCheck_843_ = !lean_is_exclusive(v_impl_732_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; lean_object* v_unused_845_; 
v_unused_844_ = lean_ctor_get(v_impl_732_, 3);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_impl_732_, 0);
lean_dec(v_unused_845_);
v___x_822_ = v_impl_732_;
v_isShared_823_ = v_isSharedCheck_843_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_r_818_);
lean_inc(v_v_820_);
lean_inc(v_k_819_);
lean_dec(v_impl_732_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_843_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_k_824_; lean_object* v_v_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_839_; 
v_k_824_ = lean_ctor_get(v_l_817_, 1);
v_v_825_ = lean_ctor_get(v_l_817_, 2);
v_isSharedCheck_839_ = !lean_is_exclusive(v_l_817_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; 
v_unused_840_ = lean_ctor_get(v_l_817_, 4);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_l_817_, 3);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_l_817_, 0);
lean_dec(v_unused_842_);
v___x_827_ = v_l_817_;
v_isShared_828_ = v_isSharedCheck_839_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_v_825_);
lean_inc(v_k_824_);
lean_dec(v_l_817_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_839_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_829_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_818_, 2);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 4, v_r_818_);
lean_ctor_set(v___x_827_, 3, v_r_818_);
lean_ctor_set(v___x_827_, 2, v_v_585_);
lean_ctor_set(v___x_827_, 1, v_k_584_);
lean_ctor_set(v___x_827_, 0, v___x_733_);
v___x_831_ = v___x_827_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_838_, 3, v_r_818_);
lean_ctor_set(v_reuseFailAlloc_838_, 4, v_r_818_);
v___x_831_ = v_reuseFailAlloc_838_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_833_; 
lean_inc(v_r_818_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 3, v_r_818_);
lean_ctor_set(v___x_822_, 0, v___x_733_);
v___x_833_ = v___x_822_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_837_, 3, v_r_818_);
lean_ctor_set(v_reuseFailAlloc_837_, 4, v_r_818_);
v___x_833_ = v_reuseFailAlloc_837_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_835_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 4, v___x_833_);
lean_ctor_set(v___x_589_, 3, v___x_831_);
lean_ctor_set(v___x_589_, 2, v_v_825_);
lean_ctor_set(v___x_589_, 1, v_k_824_);
lean_ctor_set(v___x_589_, 0, v___x_829_);
v___x_835_ = v___x_589_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_k_824_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_v_825_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
else
{
lean_object* v_r_846_; 
v_r_846_ = lean_ctor_get(v_impl_732_, 4);
lean_inc(v_r_846_);
if (lean_obj_tag(v_r_846_) == 0)
{
lean_object* v_k_847_; lean_object* v_v_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_859_; 
v_k_847_ = lean_ctor_get(v_impl_732_, 1);
v_v_848_ = lean_ctor_get(v_impl_732_, 2);
v_isSharedCheck_859_ = !lean_is_exclusive(v_impl_732_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; lean_object* v_unused_861_; lean_object* v_unused_862_; 
v_unused_860_ = lean_ctor_get(v_impl_732_, 4);
lean_dec(v_unused_860_);
v_unused_861_ = lean_ctor_get(v_impl_732_, 3);
lean_dec(v_unused_861_);
v_unused_862_ = lean_ctor_get(v_impl_732_, 0);
lean_dec(v_unused_862_);
v___x_850_ = v_impl_732_;
v_isShared_851_ = v_isSharedCheck_859_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_v_848_);
lean_inc(v_k_847_);
lean_dec(v_impl_732_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_859_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_852_ = lean_unsigned_to_nat(3u);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 4, v_l_817_);
lean_ctor_set(v___x_850_, 2, v_v_585_);
lean_ctor_set(v___x_850_, 1, v_k_584_);
lean_ctor_set(v___x_850_, 0, v___x_733_);
v___x_854_ = v___x_850_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_858_, 3, v_l_817_);
lean_ctor_set(v_reuseFailAlloc_858_, 4, v_l_817_);
v___x_854_ = v_reuseFailAlloc_858_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_856_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 4, v_r_846_);
lean_ctor_set(v___x_589_, 3, v___x_854_);
lean_ctor_set(v___x_589_, 2, v_v_848_);
lean_ctor_set(v___x_589_, 1, v_k_847_);
lean_ctor_set(v___x_589_, 0, v___x_852_);
v___x_856_ = v___x_589_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_k_847_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_v_848_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_857_, 4, v_r_846_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_863_ = lean_unsigned_to_nat(2u);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 4, v_impl_732_);
lean_ctor_set(v___x_589_, 3, v_r_846_);
lean_ctor_set(v___x_589_, 0, v___x_863_);
v___x_865_ = v___x_589_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v_r_846_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v_impl_732_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
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
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v_k_580_);
lean_ctor_set(v___x_869_, 2, v_v_581_);
lean_ctor_set(v___x_869_, 3, v_t_582_);
lean_ctor_set(v___x_869_, 4, v_t_582_);
return v___x_869_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(lean_object* v_m_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_buckets_872_; lean_object* v___x_873_; uint64_t v___x_874_; uint64_t v___x_875_; uint64_t v___x_876_; uint64_t v_fold_877_; uint64_t v___x_878_; uint64_t v___x_879_; uint64_t v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_buckets_872_ = lean_ctor_get(v_m_870_, 1);
v___x_873_ = lean_array_get_size(v_buckets_872_);
v___x_874_ = l_Lean_instHashableFVarId_hash(v_a_871_);
v___x_875_ = 32ULL;
v___x_876_ = lean_uint64_shift_right(v___x_874_, v___x_875_);
v_fold_877_ = lean_uint64_xor(v___x_874_, v___x_876_);
v___x_878_ = 16ULL;
v___x_879_ = lean_uint64_shift_right(v_fold_877_, v___x_878_);
v___x_880_ = lean_uint64_xor(v_fold_877_, v___x_879_);
v___x_881_ = lean_uint64_to_usize(v___x_880_);
v___x_882_ = lean_usize_of_nat(v___x_873_);
v___x_883_ = ((size_t)1ULL);
v___x_884_ = lean_usize_sub(v___x_882_, v___x_883_);
v___x_885_ = lean_usize_land(v___x_881_, v___x_884_);
v___x_886_ = lean_array_uget_borrowed(v_buckets_872_, v___x_885_);
v___x_887_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_871_, v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg___boxed(lean_object* v_m_888_, lean_object* v_a_889_){
_start:
{
uint8_t v_res_890_; lean_object* v_r_891_; 
v_res_890_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_m_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_m_888_);
v_r_891_ = lean_box(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(lean_object* v_ctx_892_, lean_object* v_parents_893_, lean_object* v_child_894_){
_start:
{
lean_object* v_resetTargets_895_; lean_object* v_unconditionalBorrows_896_; lean_object* v_derivedValMap_897_; lean_object* v_varMap_898_; lean_object* v_jpLiveVarMap_899_; lean_object* v_idx_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_923_; 
v_resetTargets_895_ = lean_ctor_get(v_ctx_892_, 0);
v_unconditionalBorrows_896_ = lean_ctor_get(v_ctx_892_, 1);
v_derivedValMap_897_ = lean_ctor_get(v_ctx_892_, 2);
v_varMap_898_ = lean_ctor_get(v_ctx_892_, 3);
v_jpLiveVarMap_899_ = lean_ctor_get(v_ctx_892_, 4);
v_idx_900_ = lean_ctor_get(v_ctx_892_, 5);
v_isSharedCheck_923_ = !lean_is_exclusive(v_ctx_892_);
if (v_isSharedCheck_923_ == 0)
{
v___x_902_ = v_ctx_892_;
v_isShared_903_ = v_isSharedCheck_923_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_idx_900_);
lean_inc(v_jpLiveVarMap_899_);
lean_inc(v_varMap_898_);
lean_inc(v_derivedValMap_897_);
lean_inc(v_unconditionalBorrows_896_);
lean_inc(v_resetTargets_895_);
lean_dec(v_ctx_892_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_923_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v_derivedValMap_906_; uint8_t v___x_907_; 
v___x_904_ = lean_box(0);
lean_inc_ref(v_parents_893_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v_parents_893_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
lean_inc(v_child_894_);
v_derivedValMap_906_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_child_894_, v___x_905_, v_derivedValMap_897_);
v___x_907_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_resetTargets_895_, v_child_894_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_array_get_size(v_parents_893_);
v___x_910_ = lean_nat_dec_lt(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_912_; 
lean_dec(v_child_894_);
lean_dec_ref(v_parents_893_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 2, v_derivedValMap_906_);
v___x_912_ = v___x_902_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_resetTargets_895_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_unconditionalBorrows_896_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_derivedValMap_906_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_varMap_898_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_jpLiveVarMap_899_);
lean_ctor_set(v_reuseFailAlloc_913_, 5, v_idx_900_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
else
{
size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_914_ = ((size_t)0ULL);
v___x_915_ = lean_usize_of_nat(v___x_909_);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__3(v_child_894_, v_parents_893_, v___x_914_, v___x_915_, v_derivedValMap_906_);
lean_dec_ref(v_parents_893_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 2, v___x_916_);
v___x_918_ = v___x_902_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_resetTargets_895_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_unconditionalBorrows_896_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_varMap_898_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_jpLiveVarMap_899_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v_idx_900_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
else
{
lean_object* v___x_921_; 
lean_dec(v_child_894_);
lean_dec_ref(v_parents_893_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 2, v_derivedValMap_906_);
v___x_921_ = v___x_902_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_resetTargets_895_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_unconditionalBorrows_896_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_derivedValMap_906_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_varMap_898_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_jpLiveVarMap_899_);
lean_ctor_set(v_reuseFailAlloc_922_, 5, v_idx_900_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1(lean_object* v_00_u03b2_924_, lean_object* v_k_925_, lean_object* v_v_926_, lean_object* v_t_927_, lean_object* v_hl_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__1___redArg(v_k_925_, v_v_926_, v_t_927_);
return v___x_929_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2(lean_object* v_00_u03b2_930_, lean_object* v_m_931_, lean_object* v_a_932_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_m_931_, v_a_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___boxed(lean_object* v_00_u03b2_934_, lean_object* v_m_935_, lean_object* v_a_936_){
_start:
{
uint8_t v_res_937_; lean_object* v_r_938_; 
v_res_937_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2(v_00_u03b2_934_, v_m_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_m_935_);
v_r_938_ = lean_box(v_res_937_);
return v_r_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(lean_object* v_ctx_939_, lean_object* v_fvarId_940_){
_start:
{
lean_object* v_resetTargets_941_; lean_object* v_unconditionalBorrows_942_; lean_object* v_derivedValMap_943_; lean_object* v_varMap_944_; lean_object* v_jpLiveVarMap_945_; lean_object* v_idx_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_954_; 
v_resetTargets_941_ = lean_ctor_get(v_ctx_939_, 0);
v_unconditionalBorrows_942_ = lean_ctor_get(v_ctx_939_, 1);
v_derivedValMap_943_ = lean_ctor_get(v_ctx_939_, 2);
v_varMap_944_ = lean_ctor_get(v_ctx_939_, 3);
v_jpLiveVarMap_945_ = lean_ctor_get(v_ctx_939_, 4);
v_idx_946_ = lean_ctor_get(v_ctx_939_, 5);
v_isSharedCheck_954_ = !lean_is_exclusive(v_ctx_939_);
if (v_isSharedCheck_954_ == 0)
{
v___x_948_ = v_ctx_939_;
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_idx_946_);
lean_inc(v_jpLiveVarMap_945_);
lean_inc(v_varMap_944_);
lean_inc(v_derivedValMap_943_);
lean_inc(v_unconditionalBorrows_942_);
lean_inc(v_resetTargets_941_);
lean_dec(v_ctx_939_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_950_, 0, v_fvarId_940_);
lean_ctor_set(v___x_950_, 1, v_unconditionalBorrows_942_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_950_);
v___x_952_ = v___x_948_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_resetTargets_941_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_derivedValMap_943_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_varMap_944_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v_jpLiveVarMap_945_);
lean_ctor_set(v_reuseFailAlloc_953_, 5, v_idx_946_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(lean_object* v_t_955_, lean_object* v_k_956_){
_start:
{
if (lean_obj_tag(v_t_955_) == 0)
{
lean_object* v_k_957_; lean_object* v_v_958_; lean_object* v_l_959_; lean_object* v_r_960_; uint8_t v___x_961_; 
v_k_957_ = lean_ctor_get(v_t_955_, 1);
v_v_958_ = lean_ctor_get(v_t_955_, 2);
v_l_959_ = lean_ctor_get(v_t_955_, 3);
v_r_960_ = lean_ctor_get(v_t_955_, 4);
v___x_961_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_956_, v_k_957_);
switch(v___x_961_)
{
case 0:
{
v_t_955_ = v_l_959_;
goto _start;
}
case 1:
{
lean_object* v___x_963_; 
lean_inc(v_v_958_);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v_v_958_);
return v___x_963_;
}
default: 
{
v_t_955_ = v_r_960_;
goto _start;
}
}
}
else
{
lean_object* v___x_965_; 
v___x_965_ = lean_box(0);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg___boxed(lean_object* v_t_966_, lean_object* v_k_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_t_966_, v_k_967_);
lean_dec(v_k_967_);
lean_dec(v_t_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(lean_object* v_ctx_969_, lean_object* v_as_970_, size_t v_i_971_, size_t v_stop_972_, lean_object* v_b_973_){
_start:
{
lean_object* v___y_975_; uint8_t v___x_979_; 
v___x_979_ = lean_usize_dec_eq(v_i_971_, v_stop_972_);
if (v___x_979_ == 0)
{
lean_object* v_varMap_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_varMap_980_ = lean_ctor_get(v_ctx_969_, 3);
v___x_981_ = lean_array_uget_borrowed(v_as_970_, v_i_971_);
v___x_982_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_varMap_980_, v___x_981_);
if (lean_obj_tag(v___x_982_) == 0)
{
v___y_975_ = v_b_973_;
goto v___jp_974_;
}
else
{
lean_object* v_val_983_; uint8_t v_isPossibleRef_984_; 
v_val_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v___x_982_, 1);
v_isPossibleRef_984_ = lean_ctor_get_uint8(v_val_983_, sizeof(void*)*2);
lean_dec(v_val_983_);
if (v_isPossibleRef_984_ == 0)
{
v___y_975_ = v_b_973_;
goto v___jp_974_;
}
else
{
lean_object* v___x_985_; 
lean_inc(v___x_981_);
v___x_985_ = lean_array_push(v_b_973_, v___x_981_);
v___y_975_ = v___x_985_;
goto v___jp_974_;
}
}
}
else
{
return v_b_973_;
}
v___jp_974_:
{
size_t v___x_976_; size_t v___x_977_; 
v___x_976_ = ((size_t)1ULL);
v___x_977_ = lean_usize_add(v_i_971_, v___x_976_);
v_i_971_ = v___x_977_;
v_b_973_ = v___y_975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1___boxed(lean_object* v_ctx_986_, lean_object* v_as_987_, lean_object* v_i_988_, lean_object* v_stop_989_, lean_object* v_b_990_){
_start:
{
size_t v_i_boxed_991_; size_t v_stop_boxed_992_; lean_object* v_res_993_; 
v_i_boxed_991_ = lean_unbox_usize(v_i_988_);
lean_dec(v_i_988_);
v_stop_boxed_992_ = lean_unbox_usize(v_stop_989_);
lean_dec(v_stop_989_);
v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(v_ctx_986_, v_as_987_, v_i_boxed_991_, v_stop_boxed_992_, v_b_990_);
lean_dec_ref(v_as_987_);
lean_dec_ref(v_ctx_986_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(lean_object* v_ctx_996_, lean_object* v_parents_997_, lean_object* v_decl_998_){
_start:
{
lean_object* v_fvarId_999_; lean_object* v_type_1000_; uint8_t v___x_1001_; 
v_fvarId_999_ = lean_ctor_get(v_decl_998_, 0);
lean_inc(v_fvarId_999_);
v_type_1000_ = lean_ctor_get(v_decl_998_, 2);
lean_inc_ref(v_type_1000_);
lean_dec_ref(v_decl_998_);
v___x_1001_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1000_);
lean_dec_ref(v_type_1000_);
if (v___x_1001_ == 0)
{
lean_dec(v_fvarId_999_);
return v_ctx_996_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_array_get_size(v_parents_997_);
v___x_1004_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1005_ = lean_nat_dec_lt(v___x_1002_, v___x_1003_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_996_, v___x_1004_, v_fvarId_999_);
return v___x_1006_;
}
else
{
size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1007_ = ((size_t)0ULL);
v___x_1008_ = lean_usize_of_nat(v___x_1003_);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__1(v_ctx_996_, v_parents_997_, v___x_1007_, v___x_1008_, v___x_1004_);
v___x_1010_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_996_, v___x_1009_, v_fvarId_999_);
return v___x_1010_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___boxed(lean_object* v_ctx_1011_, lean_object* v_parents_1012_, lean_object* v_decl_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1011_, v_parents_1012_, v_decl_1013_);
lean_dec_ref(v_parents_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0(lean_object* v_00_u03b4_1015_, lean_object* v_t_1016_, lean_object* v_k_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_t_1016_, v_k_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___boxed(lean_object* v_00_u03b4_1019_, lean_object* v_t_1020_, lean_object* v_k_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0(v_00_u03b4_1019_, v_t_1020_, v_k_1021_);
lean_dec(v_k_1021_);
lean_dec(v_t_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(lean_object* v_as_1023_, size_t v_i_1024_, size_t v_stop_1025_, lean_object* v_b_1026_){
_start:
{
lean_object* v___y_1028_; uint8_t v___x_1032_; 
v___x_1032_ = lean_usize_dec_eq(v_i_1024_, v_stop_1025_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_array_uget_borrowed(v_as_1023_, v_i_1024_);
if (lean_obj_tag(v___x_1033_) == 0)
{
v___y_1028_ = v_b_1026_;
goto v___jp_1027_;
}
else
{
lean_object* v_fvarId_1034_; lean_object* v___x_1035_; 
v_fvarId_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_fvarId_1034_);
v___x_1035_ = lean_array_push(v_b_1026_, v_fvarId_1034_);
v___y_1028_ = v___x_1035_;
goto v___jp_1027_;
}
}
else
{
return v_b_1026_;
}
v___jp_1027_:
{
size_t v___x_1029_; size_t v___x_1030_; 
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_add(v_i_1024_, v___x_1029_);
v_i_1024_ = v___x_1030_;
v_b_1026_ = v___y_1028_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0___boxed(lean_object* v_as_1036_, lean_object* v_i_1037_, lean_object* v_stop_1038_, lean_object* v_b_1039_){
_start:
{
size_t v_i_boxed_1040_; size_t v_stop_boxed_1041_; lean_object* v_res_1042_; 
v_i_boxed_1040_ = lean_unbox_usize(v_i_1037_);
lean_dec(v_i_1037_);
v_stop_boxed_1041_ = lean_unbox_usize(v_stop_1038_);
lean_dec(v_stop_1038_);
v_res_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1036_, v_i_boxed_1040_, v_stop_boxed_1041_, v_b_1039_);
lean_dec_ref(v_as_1036_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(lean_object* v_as_1043_, lean_object* v_start_1044_, lean_object* v_stop_1045_){
_start:
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1047_ = lean_nat_dec_lt(v_start_1044_, v_stop_1045_);
if (v___x_1047_ == 0)
{
return v___x_1046_;
}
else
{
lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = lean_array_get_size(v_as_1043_);
v___x_1049_ = lean_nat_dec_le(v_stop_1045_, v___x_1048_);
if (v___x_1049_ == 0)
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_nat_dec_lt(v_start_1044_, v___x_1048_);
if (v___x_1050_ == 0)
{
return v___x_1046_;
}
else
{
size_t v___x_1051_; size_t v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = lean_usize_of_nat(v_start_1044_);
v___x_1052_ = lean_usize_of_nat(v___x_1048_);
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1043_, v___x_1051_, v___x_1052_, v___x_1046_);
return v___x_1053_;
}
}
else
{
size_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = lean_usize_of_nat(v_start_1044_);
v___x_1055_ = lean_usize_of_nat(v_stop_1045_);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0_spec__0(v_as_1043_, v___x_1054_, v___x_1055_, v___x_1046_);
return v___x_1056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0___boxed(lean_object* v_as_1057_, lean_object* v_start_1058_, lean_object* v_stop_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(v_as_1057_, v_start_1058_, v_stop_1059_);
lean_dec(v_stop_1059_);
lean_dec(v_start_1058_);
lean_dec_ref(v_as_1057_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(lean_object* v_ctx_1065_, lean_object* v_decl_1066_){
_start:
{
lean_object* v_args_1068_; lean_object* v_fvarId_1079_; lean_object* v_value_1080_; 
v_fvarId_1079_ = lean_ctor_get(v_decl_1066_, 0);
v_value_1080_ = lean_ctor_get(v_decl_1066_, 3);
switch(lean_obj_tag(v_value_1080_))
{
case 6:
{
lean_object* v_var_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_var_1085_ = lean_ctor_get(v_value_1080_, 1);
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = lean_mk_empty_array_with_capacity(v___x_1086_);
lean_inc(v_var_1085_);
v___x_1088_ = lean_array_push(v___x_1087_, v_var_1085_);
v___x_1089_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1065_, v___x_1088_, v_decl_1066_);
lean_dec_ref(v___x_1088_);
return v___x_1089_;
}
case 9:
{
lean_object* v_fn_1090_; 
v_fn_1090_ = lean_ctor_get(v_value_1080_, 0);
if (lean_obj_tag(v_fn_1090_) == 1)
{
lean_object* v_pre_1091_; 
v_pre_1091_ = lean_ctor_get(v_fn_1090_, 0);
if (lean_obj_tag(v_pre_1091_) == 1)
{
lean_object* v_pre_1092_; 
v_pre_1092_ = lean_ctor_get(v_pre_1091_, 0);
if (lean_obj_tag(v_pre_1092_) == 0)
{
lean_object* v_args_1093_; lean_object* v_str_1094_; lean_object* v_str_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_args_1093_ = lean_ctor_get(v_value_1080_, 1);
v_str_1094_ = lean_ctor_get(v_fn_1090_, 1);
v_str_1095_ = lean_ctor_get(v_pre_1091_, 1);
v___x_1096_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0));
v___x_1097_ = lean_string_dec_eq(v_str_1095_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1098_ = lean_array_get_size(v_args_1093_);
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = lean_nat_dec_eq(v___x_1098_, v___x_1099_);
if (v___x_1100_ == 0)
{
goto v___jp_1076_;
}
else
{
lean_inc(v_fvarId_1079_);
goto v___jp_1081_;
}
}
else
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__1));
v___x_1102_ = lean_string_dec_eq(v_str_1094_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__2));
v___x_1104_ = lean_string_dec_eq(v_str_1094_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__3));
v___x_1106_ = lean_string_dec_eq(v_str_1094_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1107_ = lean_array_get_size(v_args_1093_);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_nat_dec_eq(v___x_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
goto v___jp_1076_;
}
else
{
lean_inc(v_fvarId_1079_);
goto v___jp_1081_;
}
}
else
{
lean_inc_ref(v_args_1093_);
v_args_1068_ = v_args_1093_;
goto v___jp_1067_;
}
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_parents_1120_; lean_object* v___x_1121_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_array_get_borrowed(v___x_1110_, v_args_1093_, v___x_1111_);
v___x_1113_ = lean_unsigned_to_nat(2u);
v___x_1114_ = lean_array_get_borrowed(v___x_1110_, v_args_1093_, v___x_1113_);
v___x_1115_ = lean_mk_empty_array_with_capacity(v___x_1113_);
lean_inc(v___x_1112_);
v___x_1116_ = lean_array_push(v___x_1115_, v___x_1112_);
lean_inc(v___x_1114_);
v___x_1117_ = lean_array_push(v___x_1116_, v___x_1114_);
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = lean_array_get_size(v___x_1117_);
v_parents_1120_ = l_Array_filterMapM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl_spec__0(v___x_1117_, v___x_1118_, v___x_1119_);
lean_dec_ref(v___x_1117_);
v___x_1121_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1065_, v_parents_1120_, v_decl_1066_);
lean_dec_ref(v_parents_1120_);
return v___x_1121_;
}
}
else
{
lean_inc_ref(v_args_1093_);
v_args_1068_ = v_args_1093_;
goto v___jp_1067_;
}
}
}
else
{
lean_object* v_args_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v_args_1122_ = lean_ctor_get(v_value_1080_, 1);
v___x_1123_ = lean_array_get_size(v_args_1122_);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_nat_dec_eq(v___x_1123_, v___x_1124_);
if (v___x_1125_ == 0)
{
goto v___jp_1076_;
}
else
{
lean_inc(v_fvarId_1079_);
goto v___jp_1081_;
}
}
}
else
{
lean_object* v_args_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v_args_1126_ = lean_ctor_get(v_value_1080_, 1);
v___x_1127_ = lean_array_get_size(v_args_1126_);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_nat_dec_eq(v___x_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
goto v___jp_1076_;
}
else
{
lean_inc(v_fvarId_1079_);
goto v___jp_1081_;
}
}
}
else
{
lean_object* v_args_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_args_1130_ = lean_ctor_get(v_value_1080_, 1);
v___x_1131_ = lean_array_get_size(v_args_1130_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_nat_dec_eq(v___x_1131_, v___x_1132_);
if (v___x_1133_ == 0)
{
goto v___jp_1076_;
}
else
{
lean_inc(v_fvarId_1079_);
goto v___jp_1081_;
}
}
}
case 5:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1135_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1065_, v___x_1134_, v_decl_1066_);
return v___x_1135_;
}
case 12:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1137_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1065_, v___x_1136_, v_decl_1066_);
return v___x_1137_;
}
default: 
{
lean_dec_ref(v_decl_1066_);
return v_ctx_1065_;
}
}
v___jp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = lean_array_get(v___x_1069_, v_args_1068_, v___x_1070_);
lean_dec_ref(v_args_1068_);
if (lean_obj_tag(v___x_1071_) == 1)
{
lean_object* v_fvarId_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_fvarId_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_fvarId_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = lean_mk_empty_array_with_capacity(v___x_1070_);
v___x_1074_ = lean_array_push(v___x_1073_, v_fvarId_1072_);
v___x_1075_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1065_, v___x_1074_, v_decl_1066_);
lean_dec_ref(v___x_1074_);
return v___x_1075_;
}
else
{
lean_dec(v___x_1071_);
lean_dec_ref(v_decl_1066_);
return v_ctx_1065_;
}
}
v___jp_1076_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1078_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1065_, v___x_1077_, v_decl_1066_);
return v___x_1078_;
}
v___jp_1081_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
v___x_1083_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue(v_ctx_1065_, v___x_1082_, v_decl_1066_);
v___x_1084_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(v___x_1083_, v_fvarId_1079_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___lam__0(lean_object* v_x1_1138_, lean_object* v_x2_1139_){
_start:
{
lean_object* v_resetTargets_1140_; lean_object* v_unconditionalBorrows_1141_; lean_object* v_derivedValMap_1142_; lean_object* v_varMap_1143_; lean_object* v_jpLiveVarMap_1144_; lean_object* v_idx_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1166_; 
v_resetTargets_1140_ = lean_ctor_get(v_x1_1138_, 0);
v_unconditionalBorrows_1141_ = lean_ctor_get(v_x1_1138_, 1);
v_derivedValMap_1142_ = lean_ctor_get(v_x1_1138_, 2);
v_varMap_1143_ = lean_ctor_get(v_x1_1138_, 3);
v_jpLiveVarMap_1144_ = lean_ctor_get(v_x1_1138_, 4);
v_idx_1145_ = lean_ctor_get(v_x1_1138_, 5);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_x1_1138_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1147_ = v_x1_1138_;
v_isShared_1148_ = v_isSharedCheck_1166_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_idx_1145_);
lean_inc(v_jpLiveVarMap_1144_);
lean_inc(v_varMap_1143_);
lean_inc(v_derivedValMap_1142_);
lean_inc(v_unconditionalBorrows_1141_);
lean_inc(v_resetTargets_1140_);
lean_dec(v_x1_1138_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1166_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_fvarId_1149_; lean_object* v_type_1150_; uint8_t v_borrow_1151_; uint8_t v___x_1152_; uint8_t v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v_varMap_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_ctx_1161_; 
v_fvarId_1149_ = lean_ctor_get(v_x2_1139_, 0);
lean_inc_n(v_fvarId_1149_, 2);
v_type_1150_ = lean_ctor_get(v_x2_1139_, 2);
lean_inc_ref(v_type_1150_);
v_borrow_1151_ = lean_ctor_get_uint8(v_x2_1139_, sizeof(void*)*3);
lean_dec_ref(v_x2_1139_);
v___x_1152_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1150_);
v___x_1153_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1150_);
lean_dec_ref(v_type_1150_);
v___x_1154_ = 0;
v___x_1155_ = lean_box(0);
lean_inc(v_idx_1145_);
v___x_1156_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1156_, 0, v_idx_1145_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*2, v___x_1152_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*2 + 1, v___x_1153_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*2 + 2, v___x_1154_);
v_varMap_1157_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1149_, v___x_1156_, v_varMap_1143_);
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_add(v_idx_1145_, v___x_1158_);
lean_dec(v_idx_1145_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 5, v___x_1159_);
lean_ctor_set(v___x_1147_, 3, v_varMap_1157_);
v_ctx_1161_ = v___x_1147_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_resetTargets_1140_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_unconditionalBorrows_1141_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_derivedValMap_1142_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_varMap_1157_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v_jpLiveVarMap_1144_);
lean_ctor_set(v_reuseFailAlloc_1165_, 5, v___x_1159_);
v_ctx_1161_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v_ctx_1163_; 
v___x_1162_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
lean_inc(v_fvarId_1149_);
v_ctx_1163_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_1161_, v___x_1162_, v_fvarId_1149_);
if (v_borrow_1151_ == 0)
{
lean_dec(v_fvarId_1149_);
return v_ctx_1163_;
}
else
{
if (v___x_1152_ == 0)
{
lean_dec(v_fvarId_1149_);
return v_ctx_1163_;
}
else
{
lean_object* v___x_1164_; 
v___x_1164_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(v_ctx_1163_, v_fvarId_1149_);
return v___x_1164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(lean_object* v_ps_1168_, lean_object* v_x_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = lean_array_get_size(v_ps_1168_);
v___x_1179_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v___x_1180_ = lean_nat_dec_lt(v___x_1177_, v___x_1178_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
lean_dec_ref(v_ps_1168_);
lean_inc(v_a_1175_);
lean_inc_ref(v_a_1174_);
lean_inc(v_a_1173_);
lean_inc_ref(v_a_1172_);
lean_inc(v_a_1171_);
lean_inc_ref(v_a_1170_);
v___x_1181_ = lean_apply_7(v_x_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, lean_box(0));
return v___x_1181_;
}
else
{
lean_object* v___f_1182_; size_t v___x_1183_; size_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___f_1182_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___x_1183_ = ((size_t)0ULL);
v___x_1184_ = lean_usize_of_nat(v___x_1178_);
lean_inc_ref(v_a_1170_);
v___x_1185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1179_, v___f_1182_, v_ps_1168_, v___x_1183_, v___x_1184_, v_a_1170_);
lean_inc(v_a_1175_);
lean_inc_ref(v_a_1174_);
lean_inc(v_a_1173_);
lean_inc_ref(v_a_1172_);
lean_inc(v_a_1171_);
v___x_1186_ = lean_apply_7(v_x_1169_, v___x_1185_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, lean_box(0));
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___boxed(lean_object* v_ps_1187_, lean_object* v_x_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg(v_ps_1187_, v_x_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(lean_object* v_00_u03b1_1197_, lean_object* v_ps_1198_, lean_object* v_x_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_array_get_size(v_ps_1198_);
v___x_1209_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v___x_1210_ = lean_nat_dec_lt(v___x_1207_, v___x_1208_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; 
lean_dec_ref(v_ps_1198_);
lean_inc(v_a_1205_);
lean_inc_ref(v_a_1204_);
lean_inc(v_a_1203_);
lean_inc_ref(v_a_1202_);
lean_inc(v_a_1201_);
lean_inc_ref(v_a_1200_);
v___x_1211_ = lean_apply_7(v_x_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, lean_box(0));
return v___x_1211_;
}
else
{
lean_object* v___f_1212_; size_t v___x_1213_; size_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___f_1212_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___redArg___closed__0));
v___x_1213_ = ((size_t)0ULL);
v___x_1214_ = lean_usize_of_nat(v___x_1208_);
lean_inc_ref(v_a_1200_);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1209_, v___f_1212_, v_ps_1198_, v___x_1213_, v___x_1214_, v_a_1200_);
lean_inc(v_a_1205_);
lean_inc_ref(v_a_1204_);
lean_inc(v_a_1203_);
lean_inc_ref(v_a_1202_);
lean_inc(v_a_1201_);
v___x_1216_ = lean_apply_7(v_x_1199_, v___x_1215_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, lean_box(0));
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams___boxed(lean_object* v_00_u03b1_1217_, lean_object* v_ps_1218_, lean_object* v_x_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withParams(v_00_u03b1_1217_, v_ps_1218_, v_x_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(lean_object* v_decl_1228_, lean_object* v_x_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_fvarId_1237_; lean_object* v_type_1238_; lean_object* v_value_1239_; lean_object* v___y_1241_; 
v_fvarId_1237_ = lean_ctor_get(v_decl_1228_, 0);
v_type_1238_ = lean_ctor_get(v_decl_1228_, 2);
v_value_1239_ = lean_ctor_get(v_decl_1228_, 3);
if (lean_obj_tag(v_value_1239_) == 5)
{
lean_object* v_i_1258_; lean_object* v___x_1259_; 
v_i_1258_ = lean_ctor_get(v_value_1239_, 0);
lean_inc_ref(v_i_1258_);
v___x_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1259_, 0, v_i_1258_);
v___y_1241_ = v___x_1259_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_box(0);
v___y_1241_ = v___x_1260_;
goto v___jp_1240_;
}
v___jp_1240_:
{
lean_object* v_resetTargets_1242_; lean_object* v_unconditionalBorrows_1243_; lean_object* v_derivedValMap_1244_; lean_object* v_varMap_1245_; lean_object* v_jpLiveVarMap_1246_; lean_object* v_idx_1247_; uint8_t v___x_1248_; uint8_t v___x_1249_; uint8_t v___x_1250_; lean_object* v_varInfo_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v_ctx_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_resetTargets_1242_ = lean_ctor_get(v_a_1230_, 0);
v_unconditionalBorrows_1243_ = lean_ctor_get(v_a_1230_, 1);
v_derivedValMap_1244_ = lean_ctor_get(v_a_1230_, 2);
v_varMap_1245_ = lean_ctor_get(v_a_1230_, 3);
v_jpLiveVarMap_1246_ = lean_ctor_get(v_a_1230_, 4);
v_idx_1247_ = lean_ctor_get(v_a_1230_, 5);
v___x_1248_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1238_);
v___x_1249_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1238_);
v___x_1250_ = l_Lean_Compiler_LCNF_LetValue_isPersistent(v_value_1239_);
lean_inc(v_idx_1247_);
v_varInfo_1251_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_varInfo_1251_, 0, v_idx_1247_);
lean_ctor_set(v_varInfo_1251_, 1, v___y_1241_);
lean_ctor_set_uint8(v_varInfo_1251_, sizeof(void*)*2, v___x_1248_);
lean_ctor_set_uint8(v_varInfo_1251_, sizeof(void*)*2 + 1, v___x_1249_);
lean_ctor_set_uint8(v_varInfo_1251_, sizeof(void*)*2 + 2, v___x_1250_);
lean_inc(v_varMap_1245_);
lean_inc(v_fvarId_1237_);
v___x_1252_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1237_, v_varInfo_1251_, v_varMap_1245_);
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = lean_nat_add(v_idx_1247_, v___x_1253_);
lean_inc(v_jpLiveVarMap_1246_);
lean_inc(v_derivedValMap_1244_);
lean_inc(v_unconditionalBorrows_1243_);
lean_inc_ref(v_resetTargets_1242_);
v_ctx_1255_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_ctx_1255_, 0, v_resetTargets_1242_);
lean_ctor_set(v_ctx_1255_, 1, v_unconditionalBorrows_1243_);
lean_ctor_set(v_ctx_1255_, 2, v_derivedValMap_1244_);
lean_ctor_set(v_ctx_1255_, 3, v___x_1252_);
lean_ctor_set(v_ctx_1255_, 4, v_jpLiveVarMap_1246_);
lean_ctor_set(v_ctx_1255_, 5, v___x_1254_);
v___x_1256_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(v_ctx_1255_, v_decl_1228_);
lean_inc(v_a_1235_);
lean_inc_ref(v_a_1234_);
lean_inc(v_a_1233_);
lean_inc_ref(v_a_1232_);
lean_inc(v_a_1231_);
v___x_1257_ = lean_apply_7(v_x_1229_, v___x_1256_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, lean_box(0));
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg___boxed(lean_object* v_decl_1261_, lean_object* v_x_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___redArg(v_decl_1261_, v_x_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(lean_object* v_00_u03b1_1271_, lean_object* v_decl_1272_, lean_object* v_x_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_fvarId_1281_; lean_object* v_type_1282_; lean_object* v_value_1283_; lean_object* v___y_1285_; 
v_fvarId_1281_ = lean_ctor_get(v_decl_1272_, 0);
v_type_1282_ = lean_ctor_get(v_decl_1272_, 2);
v_value_1283_ = lean_ctor_get(v_decl_1272_, 3);
if (lean_obj_tag(v_value_1283_) == 5)
{
lean_object* v_i_1302_; lean_object* v___x_1303_; 
v_i_1302_ = lean_ctor_get(v_value_1283_, 0);
lean_inc_ref(v_i_1302_);
v___x_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_i_1302_);
v___y_1285_ = v___x_1303_;
goto v___jp_1284_;
}
else
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_box(0);
v___y_1285_ = v___x_1304_;
goto v___jp_1284_;
}
v___jp_1284_:
{
lean_object* v_resetTargets_1286_; lean_object* v_unconditionalBorrows_1287_; lean_object* v_derivedValMap_1288_; lean_object* v_varMap_1289_; lean_object* v_jpLiveVarMap_1290_; lean_object* v_idx_1291_; uint8_t v___x_1292_; uint8_t v___x_1293_; uint8_t v___x_1294_; lean_object* v_varInfo_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_ctx_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_resetTargets_1286_ = lean_ctor_get(v_a_1274_, 0);
v_unconditionalBorrows_1287_ = lean_ctor_get(v_a_1274_, 1);
v_derivedValMap_1288_ = lean_ctor_get(v_a_1274_, 2);
v_varMap_1289_ = lean_ctor_get(v_a_1274_, 3);
v_jpLiveVarMap_1290_ = lean_ctor_get(v_a_1274_, 4);
v_idx_1291_ = lean_ctor_get(v_a_1274_, 5);
v___x_1292_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_1282_);
v___x_1293_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_1282_);
v___x_1294_ = l_Lean_Compiler_LCNF_LetValue_isPersistent(v_value_1283_);
lean_inc(v_idx_1291_);
v_varInfo_1295_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_varInfo_1295_, 0, v_idx_1291_);
lean_ctor_set(v_varInfo_1295_, 1, v___y_1285_);
lean_ctor_set_uint8(v_varInfo_1295_, sizeof(void*)*2, v___x_1292_);
lean_ctor_set_uint8(v_varInfo_1295_, sizeof(void*)*2 + 1, v___x_1293_);
lean_ctor_set_uint8(v_varInfo_1295_, sizeof(void*)*2 + 2, v___x_1294_);
lean_inc(v_varMap_1289_);
lean_inc(v_fvarId_1281_);
v___x_1296_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1281_, v_varInfo_1295_, v_varMap_1289_);
v___x_1297_ = lean_unsigned_to_nat(1u);
v___x_1298_ = lean_nat_add(v_idx_1291_, v___x_1297_);
lean_inc(v_jpLiveVarMap_1290_);
lean_inc(v_derivedValMap_1288_);
lean_inc(v_unconditionalBorrows_1287_);
lean_inc_ref(v_resetTargets_1286_);
v_ctx_1299_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_ctx_1299_, 0, v_resetTargets_1286_);
lean_ctor_set(v_ctx_1299_, 1, v_unconditionalBorrows_1287_);
lean_ctor_set(v_ctx_1299_, 2, v_derivedValMap_1288_);
lean_ctor_set(v_ctx_1299_, 3, v___x_1296_);
lean_ctor_set(v_ctx_1299_, 4, v_jpLiveVarMap_1290_);
lean_ctor_set(v_ctx_1299_, 5, v___x_1298_);
v___x_1300_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(v_ctx_1299_, v_decl_1272_);
lean_inc(v_a_1279_);
lean_inc_ref(v_a_1278_);
lean_inc(v_a_1277_);
lean_inc_ref(v_a_1276_);
lean_inc(v_a_1275_);
v___x_1301_ = lean_apply_7(v_x_1273_, v___x_1300_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, lean_box(0));
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl___boxed(lean_object* v_00_u03b1_1305_, lean_object* v_decl_1306_, lean_object* v_x_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withLetDecl(v_00_u03b1_1305_, v_decl_1306_, v_x_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(lean_object* v_discr_1316_, lean_object* v_c_1317_, lean_object* v_x_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_resetTargets_1326_; lean_object* v_unconditionalBorrows_1327_; lean_object* v_derivedValMap_1328_; lean_object* v_varMap_1329_; lean_object* v_jpLiveVarMap_1330_; lean_object* v_idx_1331_; lean_object* v___y_1333_; lean_object* v___f_1338_; lean_object* v___x_1339_; 
v_resetTargets_1326_ = lean_ctor_get(v_a_1319_, 0);
v_unconditionalBorrows_1327_ = lean_ctor_get(v_a_1319_, 1);
v_derivedValMap_1328_ = lean_ctor_get(v_a_1319_, 2);
v_varMap_1329_ = lean_ctor_get(v_a_1319_, 3);
v_jpLiveVarMap_1330_ = lean_ctor_get(v_a_1319_, 4);
v_idx_1331_ = lean_ctor_get(v_a_1319_, 5);
v___f_1338_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_discr_1316_);
lean_inc(v_varMap_1329_);
v___x_1339_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1338_, v_varMap_1329_, v_discr_1316_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_dec_ref(v_c_1317_);
lean_dec(v_discr_1316_);
lean_inc(v_varMap_1329_);
v___y_1333_ = v_varMap_1329_;
goto v___jp_1332_;
}
else
{
lean_object* v_val_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1361_; 
v_val_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1361_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_val_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1361_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
uint8_t v_persistent_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1358_; 
v_persistent_1344_ = lean_ctor_get_uint8(v_val_1340_, sizeof(void*)*2 + 2);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_val_1340_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; lean_object* v_unused_1360_; 
v_unused_1359_ = lean_ctor_get(v_val_1340_, 1);
lean_dec(v_unused_1359_);
v_unused_1360_ = lean_ctor_get(v_val_1340_, 0);
lean_dec(v_unused_1360_);
v___x_1346_ = v_val_1340_;
v_isShared_1347_ = v_isSharedCheck_1358_;
goto v_resetjp_1345_;
}
else
{
lean_dec(v_val_1340_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1358_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1348_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_c_1317_);
v___x_1349_ = lean_unsigned_to_nat(1u);
v___x_1350_ = lean_nat_add(v_idx_1331_, v___x_1349_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v_c_1317_);
v___x_1352_ = v___x_1342_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_c_1317_);
v___x_1352_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1352_);
lean_ctor_set(v___x_1346_, 0, v___x_1350_);
v___x_1354_ = v___x_1346_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v___x_1352_);
lean_ctor_set_uint8(v_reuseFailAlloc_1356_, sizeof(void*)*2 + 2, v_persistent_1344_);
v___x_1354_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; 
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*2, v___x_1348_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*2 + 1, v___x_1348_);
lean_inc(v_varMap_1329_);
v___x_1355_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_1316_, v___x_1354_, v_varMap_1329_);
v___y_1333_ = v___x_1355_;
goto v___jp_1332_;
}
}
}
}
}
v___jp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1334_ = lean_unsigned_to_nat(1u);
v___x_1335_ = lean_nat_add(v_idx_1331_, v___x_1334_);
lean_inc(v_jpLiveVarMap_1330_);
lean_inc(v_derivedValMap_1328_);
lean_inc(v_unconditionalBorrows_1327_);
lean_inc_ref(v_resetTargets_1326_);
v___x_1336_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1336_, 0, v_resetTargets_1326_);
lean_ctor_set(v___x_1336_, 1, v_unconditionalBorrows_1327_);
lean_ctor_set(v___x_1336_, 2, v_derivedValMap_1328_);
lean_ctor_set(v___x_1336_, 3, v___y_1333_);
lean_ctor_set(v___x_1336_, 4, v_jpLiveVarMap_1330_);
lean_ctor_set(v___x_1336_, 5, v___x_1335_);
lean_inc(v_a_1324_);
lean_inc_ref(v_a_1323_);
lean_inc(v_a_1322_);
lean_inc_ref(v_a_1321_);
lean_inc(v_a_1320_);
v___x_1337_ = lean_apply_7(v_x_1318_, v___x_1336_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, lean_box(0));
return v___x_1337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg___boxed(lean_object* v_discr_1362_, lean_object* v_c_1363_, lean_object* v_x_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___redArg(v_discr_1362_, v_c_1363_, v_x_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(lean_object* v_00_u03b1_1373_, lean_object* v_discr_1374_, lean_object* v_c_1375_, lean_object* v_x_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_resetTargets_1384_; lean_object* v_unconditionalBorrows_1385_; lean_object* v_derivedValMap_1386_; lean_object* v_varMap_1387_; lean_object* v_jpLiveVarMap_1388_; lean_object* v_idx_1389_; lean_object* v___y_1391_; lean_object* v___f_1396_; lean_object* v___x_1397_; 
v_resetTargets_1384_ = lean_ctor_get(v_a_1377_, 0);
v_unconditionalBorrows_1385_ = lean_ctor_get(v_a_1377_, 1);
v_derivedValMap_1386_ = lean_ctor_get(v_a_1377_, 2);
v_varMap_1387_ = lean_ctor_get(v_a_1377_, 3);
v_jpLiveVarMap_1388_ = lean_ctor_get(v_a_1377_, 4);
v_idx_1389_ = lean_ctor_get(v_a_1377_, 5);
v___f_1396_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_discr_1374_);
lean_inc(v_varMap_1387_);
v___x_1397_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1396_, v_varMap_1387_, v_discr_1374_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_dec_ref(v_c_1375_);
lean_dec(v_discr_1374_);
lean_inc(v_varMap_1387_);
v___y_1391_ = v_varMap_1387_;
goto v___jp_1390_;
}
else
{
lean_object* v_val_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1419_; 
v_val_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1419_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_val_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1419_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
uint8_t v_persistent_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1416_; 
v_persistent_1402_ = lean_ctor_get_uint8(v_val_1398_, sizeof(void*)*2 + 2);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_val_1398_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; lean_object* v_unused_1418_; 
v_unused_1417_ = lean_ctor_get(v_val_1398_, 1);
lean_dec(v_unused_1417_);
v_unused_1418_ = lean_ctor_get(v_val_1398_, 0);
lean_dec(v_unused_1418_);
v___x_1404_ = v_val_1398_;
v_isShared_1405_ = v_isSharedCheck_1416_;
goto v_resetjp_1403_;
}
else
{
lean_dec(v_val_1398_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1416_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1406_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_c_1375_);
v___x_1407_ = lean_unsigned_to_nat(1u);
v___x_1408_ = lean_nat_add(v_idx_1389_, v___x_1407_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v_c_1375_);
v___x_1410_ = v___x_1400_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_c_1375_);
v___x_1410_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1412_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 1, v___x_1410_);
lean_ctor_set(v___x_1404_, 0, v___x_1408_);
v___x_1412_ = v___x_1404_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, sizeof(void*)*2 + 2, v_persistent_1402_);
v___x_1412_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; 
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*2, v___x_1406_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*2 + 1, v___x_1406_);
lean_inc(v_varMap_1387_);
v___x_1413_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_1374_, v___x_1412_, v_varMap_1387_);
v___y_1391_ = v___x_1413_;
goto v___jp_1390_;
}
}
}
}
}
v___jp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1392_ = lean_unsigned_to_nat(1u);
v___x_1393_ = lean_nat_add(v_idx_1389_, v___x_1392_);
lean_inc(v_jpLiveVarMap_1388_);
lean_inc(v_derivedValMap_1386_);
lean_inc(v_unconditionalBorrows_1385_);
lean_inc_ref(v_resetTargets_1384_);
v___x_1394_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1394_, 0, v_resetTargets_1384_);
lean_ctor_set(v___x_1394_, 1, v_unconditionalBorrows_1385_);
lean_ctor_set(v___x_1394_, 2, v_derivedValMap_1386_);
lean_ctor_set(v___x_1394_, 3, v___y_1391_);
lean_ctor_set(v___x_1394_, 4, v_jpLiveVarMap_1388_);
lean_ctor_set(v___x_1394_, 5, v___x_1393_);
lean_inc(v_a_1382_);
lean_inc_ref(v_a_1381_);
lean_inc(v_a_1380_);
lean_inc_ref(v_a_1379_);
lean_inc(v_a_1378_);
v___x_1395_ = lean_apply_7(v_x_1376_, v___x_1394_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, lean_box(0));
return v___x_1395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt___boxed(lean_object* v_00_u03b1_1420_, lean_object* v_discr_1421_, lean_object* v_c_1422_, lean_object* v_x_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCtorAlt(v_00_u03b1_1420_, v_discr_1421_, v_c_1422_, v_x_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
lean_dec(v_a_1429_);
lean_dec_ref(v_a_1428_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(lean_object* v_x_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1440_ = lean_st_ref_get(v_a_1434_);
v___x_1441_ = lean_st_ref_take(v_a_1434_);
lean_dec(v___x_1441_);
v___x_1442_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_1443_ = lean_st_ref_put(v_a_1434_, v___x_1442_);
lean_inc(v_a_1438_);
lean_inc_ref(v_a_1437_);
lean_inc(v_a_1436_);
lean_inc_ref(v_a_1435_);
lean_inc(v_a_1434_);
lean_inc_ref(v_a_1433_);
v___x_1444_ = lean_apply_7(v_x_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, lean_box(0));
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1456_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1456_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1456_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1449_ = lean_st_ref_get(v_a_1434_);
v___x_1450_ = lean_st_ref_take(v_a_1434_);
lean_dec(v___x_1450_);
v___x_1451_ = lean_st_ref_put(v_a_1434_, v___x_1440_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v_a_1445_);
lean_ctor_set(v___x_1452_, 1, v___x_1449_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1452_);
v___x_1454_ = v___x_1447_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec(v___x_1440_);
v_a_1457_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1444_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1444_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg___boxed(lean_object* v_x_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___redArg(v_x_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(lean_object* v_00_u03b1_1474_, lean_object* v_x_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1483_ = lean_st_ref_get(v_a_1477_);
v___x_1484_ = lean_st_ref_take(v_a_1477_);
lean_dec(v___x_1484_);
v___x_1485_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_1486_ = lean_st_ref_put(v_a_1477_, v___x_1485_);
lean_inc(v_a_1481_);
lean_inc_ref(v_a_1480_);
lean_inc(v_a_1479_);
lean_inc_ref(v_a_1478_);
lean_inc(v_a_1477_);
lean_inc_ref(v_a_1476_);
v___x_1487_ = lean_apply_7(v_x_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, lean_box(0));
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1499_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1499_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1499_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1492_ = lean_st_ref_get(v_a_1477_);
v___x_1493_ = lean_st_ref_take(v_a_1477_);
lean_dec(v___x_1493_);
v___x_1494_ = lean_st_ref_put(v_a_1477_, v___x_1483_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_a_1488_);
lean_ctor_set(v___x_1495_, 1, v___x_1492_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1495_);
v___x_1497_ = v___x_1490_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v___x_1483_);
v_a_1500_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1487_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1487_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars___boxed(lean_object* v_00_u03b1_1508_, lean_object* v_x_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_withCollectLiveVars(v_00_u03b1_1508_, v_x_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
return v_res_1517_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0(lean_object* v_liveVars_1518_, lean_object* v___x_1519_, lean_object* v___x_1520_, uint8_t v___x_1521_, lean_object* v_v_1522_){
_start:
{
lean_object* v_vars_1523_; lean_object* v_borrows_1524_; uint8_t v___x_1525_; 
v_vars_1523_ = lean_ctor_get(v_liveVars_1518_, 0);
v_borrows_1524_ = lean_ctor_get(v_liveVars_1518_, 1);
lean_inc(v_v_1522_);
lean_inc_ref(v___x_1520_);
lean_inc_ref(v___x_1519_);
v___x_1525_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1519_, v___x_1520_, v_vars_1523_, v_v_1522_);
if (v___x_1525_ == 0)
{
uint8_t v___x_1526_; 
v___x_1526_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1519_, v___x_1520_, v_borrows_1524_, v_v_1522_);
if (v___x_1526_ == 0)
{
return v___x_1521_;
}
else
{
return v___x_1525_;
}
}
else
{
uint8_t v___x_1527_; 
lean_dec(v_v_1522_);
lean_dec_ref(v___x_1520_);
lean_dec_ref(v___x_1519_);
v___x_1527_ = 0;
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0___boxed(lean_object* v_liveVars_1528_, lean_object* v___x_1529_, lean_object* v___x_1530_, lean_object* v___x_1531_, lean_object* v_v_1532_){
_start:
{
uint8_t v___x_367__boxed_1533_; uint8_t v_res_1534_; lean_object* v_r_1535_; 
v___x_367__boxed_1533_ = lean_unbox(v___x_1531_);
v_res_1534_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0(v_liveVars_1528_, v___x_1529_, v___x_1530_, v___x_367__boxed_1533_, v_v_1532_);
lean_dec_ref(v_liveVars_1528_);
v_r_1535_ = lean_box(v_res_1534_);
return v_r_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1(lean_object* v___f_1536_, lean_object* v___x_1537_, lean_object* v_derivedValMap_1538_, lean_object* v_shouldAdd_1539_, lean_object* v___x_1540_, lean_object* v___x_1541_, lean_object* v_liveVars_1542_, lean_object* v_child_1543_){
_start:
{
lean_object* v_cinfo_1560_; lean_object* v_parents_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
lean_inc(v_child_1543_);
lean_inc(v_derivedValMap_1538_);
v_cinfo_1560_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_1536_, v___x_1537_, v_derivedValMap_1538_, v_child_1543_);
v_parents_1561_ = lean_ctor_get(v_cinfo_1560_, 0);
lean_inc_ref(v_parents_1561_);
lean_dec(v_cinfo_1560_);
v___x_1562_ = lean_unsigned_to_nat(0u);
v___x_1563_ = lean_array_get_size(v_parents_1561_);
v___x_1564_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__9));
v___x_1565_ = lean_nat_dec_lt(v___x_1562_, v___x_1563_);
if (v___x_1565_ == 0)
{
lean_dec_ref(v_parents_1561_);
goto v___jp_1544_;
}
else
{
if (v___x_1565_ == 0)
{
lean_dec_ref(v_parents_1561_);
goto v___jp_1544_;
}
else
{
lean_object* v___x_1566_; lean_object* v___f_1567_; size_t v___x_1568_; size_t v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1566_ = lean_box(v___x_1565_);
lean_inc_ref(v___x_1541_);
lean_inc_ref(v___x_1540_);
lean_inc_ref(v_liveVars_1542_);
v___f_1567_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1567_, 0, v_liveVars_1542_);
lean_closure_set(v___f_1567_, 1, v___x_1540_);
lean_closure_set(v___f_1567_, 2, v___x_1541_);
lean_closure_set(v___f_1567_, 3, v___x_1566_);
v___x_1568_ = ((size_t)0ULL);
v___x_1569_ = lean_usize_of_nat(v___x_1563_);
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1564_, v___f_1567_, v_parents_1561_, v___x_1568_, v___x_1569_);
v___x_1571_ = lean_unbox(v___x_1570_);
lean_dec(v___x_1570_);
if (v___x_1571_ == 0)
{
goto v___jp_1544_;
}
else
{
lean_object* v___x_1572_; 
lean_dec_ref(v___x_1541_);
lean_dec_ref(v___x_1540_);
v___x_1572_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_child_1543_, v_derivedValMap_1538_, v_liveVars_1542_, v_shouldAdd_1539_);
return v___x_1572_;
}
}
}
v___jp_1544_:
{
lean_object* v___x_1545_; uint8_t v___x_1546_; 
lean_inc_ref(v_shouldAdd_1539_);
lean_inc(v_child_1543_);
v___x_1545_ = lean_apply_1(v_shouldAdd_1539_, v_child_1543_);
v___x_1546_ = lean_unbox(v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
lean_dec_ref(v___x_1541_);
lean_dec_ref(v___x_1540_);
v___x_1547_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_child_1543_, v_derivedValMap_1538_, v_liveVars_1542_, v_shouldAdd_1539_);
return v___x_1547_;
}
else
{
lean_object* v_vars_1548_; lean_object* v_borrows_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1559_; 
v_vars_1548_ = lean_ctor_get(v_liveVars_1542_, 0);
v_borrows_1549_ = lean_ctor_get(v_liveVars_1542_, 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_liveVars_1542_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1551_ = v_liveVars_1542_;
v_isShared_1552_ = v_isSharedCheck_1559_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_borrows_1549_);
lean_inc(v_vars_1548_);
lean_dec(v_liveVars_1542_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1559_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1553_ = lean_box(0);
lean_inc(v_child_1543_);
v___x_1554_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1540_, v___x_1541_, v_borrows_1549_, v_child_1543_, v___x_1553_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 1, v___x_1554_);
v___x_1556_ = v___x_1551_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_vars_1548_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; 
v___x_1557_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_child_1543_, v_derivedValMap_1538_, v___x_1556_, v_shouldAdd_1539_);
return v___x_1557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1___boxed(lean_object* v___f_1573_, lean_object* v___x_1574_, lean_object* v_derivedValMap_1575_, lean_object* v_shouldAdd_1576_, lean_object* v___x_1577_, lean_object* v___x_1578_, lean_object* v_liveVars_1579_, lean_object* v_child_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1(v___f_1573_, v___x_1574_, v_derivedValMap_1575_, v_shouldAdd_1576_, v___x_1577_, v___x_1578_, v_liveVars_1579_, v_child_1580_);
lean_dec_ref(v___x_1574_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(lean_object* v_fvarId_1582_, lean_object* v_derivedValMap_1583_, lean_object* v_liveVars_1584_, lean_object* v_shouldAdd_1585_){
_start:
{
lean_object* v___f_1586_; lean_object* v___x_1587_; 
v___f_1586_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
lean_inc(v_derivedValMap_1583_);
v___x_1587_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_1586_, v_derivedValMap_1583_, v_fvarId_1582_);
if (lean_obj_tag(v___x_1587_) == 1)
{
lean_object* v_val_1588_; lean_object* v_children_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___f_1593_; lean_object* v___x_1594_; 
v_val_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v_children_1589_ = lean_ctor_get(v_val_1588_, 1);
lean_inc(v_children_1589_);
lean_dec(v_val_1588_);
v___x_1590_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default));
v___x_1591_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_1592_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___f_1593_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___lam__1___boxed), 8, 6);
lean_closure_set(v___f_1593_, 0, v___f_1586_);
lean_closure_set(v___f_1593_, 1, v___x_1590_);
lean_closure_set(v___f_1593_, 2, v_derivedValMap_1583_);
lean_closure_set(v___f_1593_, 3, v_shouldAdd_1585_);
lean_closure_set(v___f_1593_, 4, v___x_1591_);
lean_closure_set(v___f_1593_, 5, v___x_1592_);
v___x_1594_ = l_List_foldl___redArg(v___f_1593_, v_liveVars_1584_, v_children_1589_);
return v___x_1594_;
}
else
{
lean_dec(v___x_1587_);
lean_dec_ref(v_shouldAdd_1585_);
lean_dec(v_derivedValMap_1583_);
return v_liveVars_1584_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0(lean_object* v_val_1595_, lean_object* v___x_1596_, lean_object* v___x_1597_, lean_object* v_shouldBorrow_1598_, uint8_t v___x_1599_, lean_object* v_y_1600_){
_start:
{
lean_object* v_vars_1601_; uint8_t v___x_1602_; 
v_vars_1601_ = lean_ctor_get(v_val_1595_, 0);
lean_inc(v_y_1600_);
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1596_, v___x_1597_, v_vars_1601_, v_y_1600_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = lean_apply_1(v_shouldBorrow_1598_, v_y_1600_);
v___x_1604_ = lean_unbox(v___x_1603_);
return v___x_1604_;
}
else
{
lean_dec(v_y_1600_);
lean_dec_ref(v_shouldBorrow_1598_);
return v___x_1599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0___boxed(lean_object* v_val_1605_, lean_object* v___x_1606_, lean_object* v___x_1607_, lean_object* v_shouldBorrow_1608_, lean_object* v___x_1609_, lean_object* v_y_1610_){
_start:
{
uint8_t v___x_1972__boxed_1611_; uint8_t v_res_1612_; lean_object* v_r_1613_; 
v___x_1972__boxed_1611_ = lean_unbox(v___x_1609_);
v_res_1612_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0(v_val_1605_, v___x_1606_, v___x_1607_, v_shouldBorrow_1608_, v___x_1972__boxed_1611_, v_y_1610_);
lean_dec_ref(v_val_1605_);
v_r_1613_ = lean_box(v_res_1612_);
return v_r_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(lean_object* v_fvarId_1614_, lean_object* v_shouldBorrow_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v_vars_1622_; uint8_t v___x_1623_; 
v___x_1619_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_1620_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
v___x_1621_ = lean_st_ref_get(v_a_1617_);
v_vars_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc_ref(v_vars_1622_);
lean_dec(v___x_1621_);
lean_inc(v_fvarId_1614_);
v___x_1623_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1619_, v___x_1620_, v_vars_1622_, v_fvarId_1614_);
lean_dec_ref(v_vars_1622_);
if (v___x_1623_ == 0)
{
lean_object* v_derivedValMap_1624_; lean_object* v___x_1625_; lean_object* v_vars_1626_; lean_object* v_borrows_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1643_; 
v_derivedValMap_1624_ = lean_ctor_get(v_a_1616_, 2);
v___x_1625_ = lean_st_ref_take(v_a_1617_);
v_vars_1626_ = lean_ctor_get(v___x_1625_, 0);
v_borrows_1627_ = lean_ctor_get(v___x_1625_, 1);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1629_ = v___x_1625_;
v_isShared_1630_ = v_isSharedCheck_1643_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_borrows_1627_);
lean_inc(v_vars_1626_);
lean_dec(v___x_1625_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1643_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1631_ = lean_box(0);
lean_inc(v_fvarId_1614_);
v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1619_, v___x_1620_, v_vars_1626_, v_fvarId_1614_, v___x_1631_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1632_);
v___x_1634_ = v___x_1629_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_borrows_1627_);
v___x_1634_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___f_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1635_ = lean_st_ref_put(v_a_1617_, v___x_1634_);
v___x_1636_ = lean_st_ref_take(v_a_1617_);
v___x_1637_ = lean_box(v___x_1623_);
lean_inc(v___x_1636_);
v___f_1638_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1638_, 0, v___x_1636_);
lean_closure_set(v___f_1638_, 1, v___x_1619_);
lean_closure_set(v___f_1638_, 2, v___x_1620_);
lean_closure_set(v___f_1638_, 3, v_shouldBorrow_1615_);
lean_closure_set(v___f_1638_, 4, v___x_1637_);
lean_inc(v_derivedValMap_1624_);
v___x_1639_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants(v_fvarId_1614_, v_derivedValMap_1624_, v___x_1636_, v___f_1638_);
v___x_1640_ = lean_st_ref_put(v_a_1617_, v___x_1639_);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1631_);
return v___x_1641_;
}
}
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec_ref(v_shouldBorrow_1615_);
lean_dec(v_fvarId_1614_);
v___x_1644_ = lean_box(0);
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
return v___x_1645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg___boxed(lean_object* v_fvarId_1646_, lean_object* v_shouldBorrow_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_1646_, v_shouldBorrow_1647_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(lean_object* v_fvarId_1652_, lean_object* v_shouldBorrow_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___redArg(v_fvarId_1652_, v_shouldBorrow_1653_, v_a_1654_, v_a_1655_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___boxed(lean_object* v_fvarId_1662_, lean_object* v_shouldBorrow_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar(v_fvarId_1662_, v_shouldBorrow_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
return v_res_1671_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(lean_object* v_liveVars_1672_, lean_object* v_as_1673_, size_t v_i_1674_, size_t v_stop_1675_){
_start:
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_usize_dec_eq(v_i_1674_, v_stop_1675_);
if (v___x_1680_ == 0)
{
lean_object* v_vars_1681_; lean_object* v_borrows_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v_vars_1681_ = lean_ctor_get(v_liveVars_1672_, 0);
v_borrows_1682_ = lean_ctor_get(v_liveVars_1672_, 1);
v___x_1683_ = lean_array_uget_borrowed(v_as_1673_, v_i_1674_);
v___x_1684_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1681_, v___x_1683_);
if (v___x_1684_ == 0)
{
uint8_t v___x_1685_; 
v___x_1685_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_1682_, v___x_1683_);
if (v___x_1685_ == 0)
{
uint8_t v___x_1686_; 
v___x_1686_ = 1;
return v___x_1686_;
}
else
{
goto v___jp_1676_;
}
}
else
{
goto v___jp_1676_;
}
}
else
{
uint8_t v___x_1687_; 
v___x_1687_ = 0;
return v___x_1687_;
}
v___jp_1676_:
{
size_t v___x_1677_; size_t v___x_1678_; 
v___x_1677_ = ((size_t)1ULL);
v___x_1678_ = lean_usize_add(v_i_1674_, v___x_1677_);
v_i_1674_ = v___x_1678_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3___boxed(lean_object* v_liveVars_1688_, lean_object* v_as_1689_, lean_object* v_i_1690_, lean_object* v_stop_1691_){
_start:
{
size_t v_i_boxed_1692_; size_t v_stop_boxed_1693_; uint8_t v_res_1694_; lean_object* v_r_1695_; 
v_i_boxed_1692_ = lean_unbox_usize(v_i_1690_);
lean_dec(v_i_1690_);
v_stop_boxed_1693_ = lean_unbox_usize(v_stop_1691_);
lean_dec(v_stop_1691_);
v_res_1694_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_liveVars_1688_, v_as_1689_, v_i_boxed_1692_, v_stop_boxed_1693_);
lean_dec_ref(v_as_1689_);
lean_dec_ref(v_liveVars_1688_);
v_r_1695_ = lean_box(v_res_1694_);
return v_r_1695_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(lean_object* v_y_1696_, lean_object* v_as_1697_, size_t v_i_1698_, size_t v_stop_1699_){
_start:
{
uint8_t v___x_1704_; 
v___x_1704_ = lean_usize_dec_eq(v_i_1698_, v_stop_1699_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_array_uget_borrowed(v_as_1697_, v_i_1698_);
if (lean_obj_tag(v___x_1705_) == 0)
{
goto v___jp_1700_;
}
else
{
lean_object* v_fvarId_1706_; uint8_t v___x_1707_; 
v_fvarId_1706_ = lean_ctor_get(v___x_1705_, 0);
v___x_1707_ = l_Lean_instBEqFVarId_beq(v_y_1696_, v_fvarId_1706_);
if (v___x_1707_ == 0)
{
goto v___jp_1700_;
}
else
{
return v___x_1707_;
}
}
}
else
{
uint8_t v___x_1708_; 
v___x_1708_ = 0;
return v___x_1708_;
}
v___jp_1700_:
{
size_t v___x_1701_; size_t v___x_1702_; 
v___x_1701_ = ((size_t)1ULL);
v___x_1702_ = lean_usize_add(v_i_1698_, v___x_1701_);
v_i_1698_ = v___x_1702_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0___boxed(lean_object* v_y_1709_, lean_object* v_as_1710_, lean_object* v_i_1711_, lean_object* v_stop_1712_){
_start:
{
size_t v_i_boxed_1713_; size_t v_stop_boxed_1714_; uint8_t v_res_1715_; lean_object* v_r_1716_; 
v_i_boxed_1713_ = lean_unbox_usize(v_i_1711_);
lean_dec(v_i_1711_);
v_stop_boxed_1714_ = lean_unbox_usize(v_stop_1712_);
lean_dec(v_stop_1712_);
v_res_1715_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_y_1709_, v_as_1710_, v_i_boxed_1713_, v_stop_boxed_1714_);
lean_dec_ref(v_as_1710_);
lean_dec(v_y_1709_);
v_r_1716_ = lean_box(v_res_1715_);
return v_r_1716_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2_spec__4(lean_object* v_msg_1717_){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDerivedValInfo_default));
v___x_1719_ = lean_panic_fn_borrowed(v___x_1718_, v_msg_1717_);
return v___x_1719_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1723_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__2));
v___x_1724_ = lean_unsigned_to_nat(13u);
v___x_1725_ = lean_unsigned_to_nat(227u);
v___x_1726_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__1));
v___x_1727_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__0));
v___x_1728_ = l_mkPanicMessageWithDecl(v___x_1727_, v___x_1726_, v___x_1725_, v___x_1724_, v___x_1723_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(lean_object* v_t_1729_, lean_object* v_k_1730_){
_start:
{
if (lean_obj_tag(v_t_1729_) == 0)
{
lean_object* v_k_1731_; lean_object* v_v_1732_; lean_object* v_l_1733_; lean_object* v_r_1734_; uint8_t v___x_1735_; 
v_k_1731_ = lean_ctor_get(v_t_1729_, 1);
v_v_1732_ = lean_ctor_get(v_t_1729_, 2);
v_l_1733_ = lean_ctor_get(v_t_1729_, 3);
v_r_1734_ = lean_ctor_get(v_t_1729_, 4);
v___x_1735_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1730_, v_k_1731_);
switch(v___x_1735_)
{
case 0:
{
v_t_1729_ = v_l_1733_;
goto _start;
}
case 1:
{
lean_inc(v_v_1732_);
return v_v_1732_;
}
default: 
{
v_t_1729_ = v_r_1734_;
goto _start;
}
}
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3);
v___x_1739_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2_spec__4(v___x_1738_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___boxed(lean_object* v_t_1740_, lean_object* v_k_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_t_1740_, v_k_1741_);
lean_dec(v_k_1741_);
lean_dec(v_t_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(lean_object* v___x_1743_, lean_object* v_args_1744_, uint8_t v___x_1745_, lean_object* v_derivedValMap_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
if (lean_obj_tag(v_x_1748_) == 0)
{
return v_x_1747_;
}
else
{
lean_object* v_head_1749_; lean_object* v_tail_1750_; lean_object* v_cinfo_1778_; lean_object* v_parents_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v_head_1749_ = lean_ctor_get(v_x_1748_, 0);
lean_inc(v_head_1749_);
v_tail_1750_ = lean_ctor_get(v_x_1748_, 1);
lean_inc(v_tail_1750_);
lean_dec_ref_known(v_x_1748_, 2);
v_cinfo_1778_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_1746_, v_head_1749_);
v_parents_1779_ = lean_ctor_get(v_cinfo_1778_, 0);
lean_inc_ref(v_parents_1779_);
lean_dec_ref(v_cinfo_1778_);
v___x_1780_ = lean_unsigned_to_nat(0u);
v___x_1781_ = lean_array_get_size(v_parents_1779_);
v___x_1782_ = lean_nat_dec_lt(v___x_1780_, v___x_1781_);
if (v___x_1782_ == 0)
{
lean_dec_ref(v_parents_1779_);
goto v___jp_1765_;
}
else
{
size_t v___x_1783_; size_t v___x_1784_; uint8_t v___x_1785_; 
v___x_1783_ = ((size_t)0ULL);
v___x_1784_ = lean_usize_of_nat(v___x_1781_);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_1747_, v_parents_1779_, v___x_1783_, v___x_1784_);
lean_dec_ref(v_parents_1779_);
if (v___x_1785_ == 0)
{
goto v___jp_1765_;
}
else
{
lean_object* v___x_1786_; 
v___x_1786_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1743_, v_args_1744_, v___x_1745_, v_head_1749_, v_derivedValMap_1746_, v_x_1747_);
lean_dec(v_head_1749_);
v_x_1747_ = v___x_1786_;
v_x_1748_ = v_tail_1750_;
goto _start;
}
}
v___jp_1751_:
{
lean_object* v_vars_1752_; lean_object* v_borrows_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1764_; 
v_vars_1752_ = lean_ctor_get(v_x_1747_, 0);
v_borrows_1753_ = lean_ctor_get(v_x_1747_, 1);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_x_1747_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1755_ = v_x_1747_;
v_isShared_1756_ = v_isSharedCheck_1764_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_borrows_1753_);
lean_inc(v_vars_1752_);
lean_dec(v_x_1747_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1764_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1757_ = lean_box(0);
lean_inc(v_head_1749_);
v___x_1758_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_1753_, v_head_1749_, v___x_1757_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v___x_1758_);
v___x_1760_ = v___x_1755_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_vars_1752_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1761_; 
v___x_1761_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1743_, v_args_1744_, v___x_1745_, v_head_1749_, v_derivedValMap_1746_, v___x_1760_);
lean_dec(v_head_1749_);
v_x_1747_ = v___x_1761_;
v_x_1748_ = v_tail_1750_;
goto _start;
}
}
}
v___jp_1765_:
{
lean_object* v_vars_1766_; uint8_t v___x_1767_; 
v_vars_1766_ = lean_ctor_get(v___x_1743_, 0);
v___x_1767_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1766_, v_head_1749_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = lean_array_get_size(v_args_1744_);
v___x_1770_ = lean_nat_dec_lt(v___x_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
goto v___jp_1751_;
}
else
{
if (v___x_1770_ == 0)
{
goto v___jp_1751_;
}
else
{
size_t v___x_1771_; size_t v___x_1772_; uint8_t v___x_1773_; 
v___x_1771_ = ((size_t)0ULL);
v___x_1772_ = lean_usize_of_nat(v___x_1769_);
v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_head_1749_, v_args_1744_, v___x_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
goto v___jp_1751_;
}
else
{
lean_object* v___x_1774_; 
v___x_1774_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1743_, v_args_1744_, v___x_1745_, v_head_1749_, v_derivedValMap_1746_, v_x_1747_);
lean_dec(v_head_1749_);
v_x_1747_ = v___x_1774_;
v_x_1748_ = v_tail_1750_;
goto _start;
}
}
}
}
else
{
if (v___x_1745_ == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1743_, v_args_1744_, v___x_1745_, v_head_1749_, v_derivedValMap_1746_, v_x_1747_);
lean_dec(v_head_1749_);
v_x_1747_ = v___x_1776_;
v_x_1748_ = v_tail_1750_;
goto _start;
}
else
{
goto v___jp_1751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(lean_object* v___x_1788_, lean_object* v_args_1789_, uint8_t v___x_1790_, lean_object* v_derivedValMap_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_){
_start:
{
if (lean_obj_tag(v_x_1793_) == 0)
{
return v_x_1792_;
}
else
{
lean_object* v_head_1794_; lean_object* v_tail_1795_; lean_object* v_cinfo_1823_; lean_object* v_parents_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v_head_1794_ = lean_ctor_get(v_x_1793_, 0);
lean_inc(v_head_1794_);
v_tail_1795_ = lean_ctor_get(v_x_1793_, 1);
lean_inc(v_tail_1795_);
lean_dec_ref_known(v_x_1793_, 2);
v_cinfo_1823_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_1791_, v_head_1794_);
v_parents_1824_ = lean_ctor_get(v_cinfo_1823_, 0);
lean_inc_ref(v_parents_1824_);
lean_dec_ref(v_cinfo_1823_);
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = lean_array_get_size(v_parents_1824_);
v___x_1827_ = lean_nat_dec_lt(v___x_1825_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_dec_ref(v_parents_1824_);
goto v___jp_1810_;
}
else
{
size_t v___x_1828_; size_t v___x_1829_; uint8_t v___x_1830_; 
v___x_1828_ = ((size_t)0ULL);
v___x_1829_ = lean_usize_of_nat(v___x_1826_);
v___x_1830_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_1792_, v_parents_1824_, v___x_1828_, v___x_1829_);
lean_dec_ref(v_parents_1824_);
if (v___x_1830_ == 0)
{
goto v___jp_1810_;
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1788_, v_args_1789_, v___x_1790_, v_head_1794_, v_derivedValMap_1791_, v_x_1792_);
lean_dec(v_head_1794_);
v___x_1832_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1788_, v_args_1789_, v___x_1790_, v_derivedValMap_1791_, v___x_1831_, v_tail_1795_);
return v___x_1832_;
}
}
v___jp_1796_:
{
lean_object* v_vars_1797_; lean_object* v_borrows_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1809_; 
v_vars_1797_ = lean_ctor_get(v_x_1792_, 0);
v_borrows_1798_ = lean_ctor_get(v_x_1792_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_x_1792_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1800_ = v_x_1792_;
v_isShared_1801_ = v_isSharedCheck_1809_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_borrows_1798_);
lean_inc(v_vars_1797_);
lean_dec(v_x_1792_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1809_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1802_ = lean_box(0);
lean_inc(v_head_1794_);
v___x_1803_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_1798_, v_head_1794_, v___x_1802_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 1, v___x_1803_);
v___x_1805_ = v___x_1800_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_vars_1797_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1788_, v_args_1789_, v___x_1790_, v_head_1794_, v_derivedValMap_1791_, v___x_1805_);
lean_dec(v_head_1794_);
v___x_1807_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1788_, v_args_1789_, v___x_1790_, v_derivedValMap_1791_, v___x_1806_, v_tail_1795_);
return v___x_1807_;
}
}
}
v___jp_1810_:
{
lean_object* v_vars_1811_; uint8_t v___x_1812_; 
v_vars_1811_ = lean_ctor_get(v___x_1788_, 0);
v___x_1812_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1811_, v_head_1794_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_array_get_size(v_args_1789_);
v___x_1815_ = lean_nat_dec_lt(v___x_1813_, v___x_1814_);
if (v___x_1815_ == 0)
{
goto v___jp_1796_;
}
else
{
if (v___x_1815_ == 0)
{
goto v___jp_1796_;
}
else
{
size_t v___x_1816_; size_t v___x_1817_; uint8_t v___x_1818_; 
v___x_1816_ = ((size_t)0ULL);
v___x_1817_ = lean_usize_of_nat(v___x_1814_);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__0(v_head_1794_, v_args_1789_, v___x_1816_, v___x_1817_);
if (v___x_1818_ == 0)
{
goto v___jp_1796_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1788_, v_args_1789_, v___x_1790_, v_head_1794_, v_derivedValMap_1791_, v_x_1792_);
lean_dec(v_head_1794_);
v___x_1820_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1788_, v_args_1789_, v___x_1790_, v_derivedValMap_1791_, v___x_1819_, v_tail_1795_);
return v___x_1820_;
}
}
}
}
else
{
if (v___x_1790_ == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1788_, v_args_1789_, v___x_1790_, v_head_1794_, v_derivedValMap_1791_, v_x_1792_);
lean_dec(v_head_1794_);
v___x_1822_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1788_, v_args_1789_, v___x_1790_, v_derivedValMap_1791_, v___x_1821_, v_tail_1795_);
return v___x_1822_;
}
else
{
goto v___jp_1796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(lean_object* v___x_1833_, lean_object* v_args_1834_, uint8_t v___x_1835_, lean_object* v_fvarId_1836_, lean_object* v_derivedValMap_1837_, lean_object* v_liveVars_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_derivedValMap_1837_, v_fvarId_1836_);
if (lean_obj_tag(v___x_1839_) == 1)
{
lean_object* v_val_1840_; lean_object* v_children_1841_; lean_object* v___x_1842_; 
v_val_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v_children_1841_ = lean_ctor_get(v_val_1840_, 1);
lean_inc(v_children_1841_);
lean_dec(v_val_1840_);
v___x_1842_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(v___x_1833_, v_args_1834_, v___x_1835_, v_derivedValMap_1837_, v_liveVars_1838_, v_children_1841_);
return v___x_1842_;
}
else
{
lean_dec(v___x_1839_);
return v_liveVars_1838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1___boxed(lean_object* v___x_1843_, lean_object* v_args_1844_, lean_object* v___x_1845_, lean_object* v_fvarId_1846_, lean_object* v_derivedValMap_1847_, lean_object* v_liveVars_1848_){
_start:
{
uint8_t v___x_2261__boxed_1849_; lean_object* v_res_1850_; 
v___x_2261__boxed_1849_ = lean_unbox(v___x_1845_);
v_res_1850_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1843_, v_args_1844_, v___x_2261__boxed_1849_, v_fvarId_1846_, v_derivedValMap_1847_, v_liveVars_1848_);
lean_dec(v_derivedValMap_1847_);
lean_dec(v_fvarId_1846_);
lean_dec_ref(v_args_1844_);
lean_dec_ref(v___x_1843_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v___x_1851_, lean_object* v_args_1852_, lean_object* v___x_1853_, lean_object* v_derivedValMap_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
uint8_t v___x_2266__boxed_1857_; lean_object* v_res_1858_; 
v___x_2266__boxed_1857_ = lean_unbox(v___x_1853_);
v_res_1858_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4_spec__7(v___x_1851_, v_args_1852_, v___x_2266__boxed_1857_, v_derivedValMap_1854_, v_x_1855_, v_x_1856_);
lean_dec(v_derivedValMap_1854_);
lean_dec_ref(v_args_1852_);
lean_dec_ref(v___x_1851_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4___boxed(lean_object* v___x_1859_, lean_object* v_args_1860_, lean_object* v___x_1861_, lean_object* v_derivedValMap_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_){
_start:
{
uint8_t v___x_2298__boxed_1865_; lean_object* v_res_1866_; 
v___x_2298__boxed_1865_ = lean_unbox(v___x_1861_);
v_res_1866_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__4(v___x_1859_, v_args_1860_, v___x_2298__boxed_1865_, v_derivedValMap_1862_, v_x_1863_, v_x_1864_);
lean_dec(v_derivedValMap_1862_);
lean_dec_ref(v_args_1860_);
lean_dec_ref(v___x_1859_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(lean_object* v_args_1867_, lean_object* v_fvarId_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1872_; lean_object* v_vars_1873_; uint8_t v___x_1874_; 
v___x_1872_ = lean_st_ref_get(v_a_1870_);
v_vars_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc_ref(v_vars_1873_);
lean_dec(v___x_1872_);
v___x_1874_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_1873_, v_fvarId_1868_);
lean_dec_ref(v_vars_1873_);
if (v___x_1874_ == 0)
{
lean_object* v_derivedValMap_1875_; lean_object* v___x_1876_; lean_object* v_vars_1877_; lean_object* v_borrows_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1892_; 
v_derivedValMap_1875_ = lean_ctor_get(v_a_1869_, 2);
v___x_1876_ = lean_st_ref_take(v_a_1870_);
v_vars_1877_ = lean_ctor_get(v___x_1876_, 0);
v_borrows_1878_ = lean_ctor_get(v___x_1876_, 1);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1880_ = v___x_1876_;
v_isShared_1881_ = v_isSharedCheck_1892_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_borrows_1878_);
lean_inc(v_vars_1877_);
lean_dec(v___x_1876_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1892_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1882_ = lean_box(0);
lean_inc(v_fvarId_1868_);
v___x_1883_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_vars_1877_, v_fvarId_1868_, v___x_1882_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1883_);
v___x_1885_ = v___x_1880_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_borrows_1878_);
v___x_1885_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1886_ = lean_st_ref_put(v_a_1870_, v___x_1885_);
v___x_1887_ = lean_st_ref_take(v_a_1870_);
lean_inc(v___x_1887_);
v___x_1888_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1(v___x_1887_, v_args_1867_, v___x_1874_, v_fvarId_1868_, v_derivedValMap_1875_, v___x_1887_);
lean_dec(v_fvarId_1868_);
lean_dec(v___x_1887_);
v___x_1889_ = lean_st_ref_put(v_a_1870_, v___x_1888_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1882_);
return v___x_1890_;
}
}
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec(v_fvarId_1868_);
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg___boxed(lean_object* v_args_1895_, lean_object* v_fvarId_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_1895_, v_fvarId_1896_, v_a_1897_, v_a_1898_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec_ref(v_args_1895_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(lean_object* v_args_1901_, lean_object* v_as_1902_, size_t v_i_1903_, size_t v_stop_1904_, lean_object* v_b_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_a_1914_; uint8_t v___x_1918_; 
v___x_1918_ = lean_usize_dec_eq(v_i_1903_, v_stop_1904_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_array_uget_borrowed(v_as_1902_, v_i_1903_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v___x_1920_; 
v___x_1920_ = lean_box(0);
v_a_1914_ = v___x_1920_;
goto v___jp_1913_;
}
else
{
lean_object* v_fvarId_1921_; lean_object* v___x_1922_; 
v_fvarId_1921_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_fvarId_1921_);
v___x_1922_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_1901_, v_fvarId_1921_, v___y_1906_, v___y_1907_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
v_a_1914_ = v_a_1923_;
goto v___jp_1913_;
}
else
{
return v___x_1922_;
}
}
}
else
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1924_, 0, v_b_1905_);
return v___x_1924_;
}
v___jp_1913_:
{
size_t v___x_1915_; size_t v___x_1916_; 
v___x_1915_ = ((size_t)1ULL);
v___x_1916_ = lean_usize_add(v_i_1903_, v___x_1915_);
v_i_1903_ = v___x_1916_;
v_b_1905_ = v_a_1914_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2___boxed(lean_object* v_args_1925_, lean_object* v_as_1926_, lean_object* v_i_1927_, lean_object* v_stop_1928_, lean_object* v_b_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
size_t v_i_boxed_1937_; size_t v_stop_boxed_1938_; lean_object* v_res_1939_; 
v_i_boxed_1937_ = lean_unbox_usize(v_i_1927_);
lean_dec(v_i_1927_);
v_stop_boxed_1938_ = lean_unbox_usize(v_stop_1928_);
lean_dec(v_stop_1928_);
v_res_1939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(v_args_1925_, v_as_1926_, v_i_boxed_1937_, v_stop_boxed_1938_, v_b_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec_ref(v_as_1926_);
lean_dec_ref(v_args_1925_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(lean_object* v_args_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = lean_array_get_size(v_args_1940_);
v___x_1950_ = lean_box(0);
v___x_1951_ = lean_nat_dec_lt(v___x_1948_, v___x_1949_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1950_);
return v___x_1952_;
}
else
{
size_t v___x_1953_; size_t v___x_1954_; lean_object* v___x_1955_; 
v___x_1953_ = ((size_t)0ULL);
v___x_1954_ = lean_usize_of_nat(v___x_1949_);
v___x_1955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__2(v_args_1940_, v_args_1940_, v___x_1953_, v___x_1954_, v___x_1950_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
return v___x_1955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs___boxed(lean_object* v_args_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec_ref(v_args_1956_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(lean_object* v_args_1965_, lean_object* v_fvarId_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___redArg(v_args_1965_, v_fvarId_1966_, v_a_1967_, v_a_1968_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1___boxed(lean_object* v_args_1975_, lean_object* v_fvarId_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1(v_args_1975_, v_fvarId_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec_ref(v_args_1975_);
return v_res_1984_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_instMonadEIO___redArg();
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(lean_object* v_msg_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v_toApplicative_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2063_; 
v___x_1998_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0);
v___x_1999_ = l_StateRefT_x27_instMonad___redArg(v___x_1998_);
v_toApplicative_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v___x_1999_, 1);
lean_dec(v_unused_2064_);
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2063_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_toApplicative_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2063_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v_toFunctor_2004_; lean_object* v_toSeq_2005_; lean_object* v_toSeqLeft_2006_; lean_object* v_toSeqRight_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2061_; 
v_toFunctor_2004_ = lean_ctor_get(v_toApplicative_2000_, 0);
v_toSeq_2005_ = lean_ctor_get(v_toApplicative_2000_, 2);
v_toSeqLeft_2006_ = lean_ctor_get(v_toApplicative_2000_, 3);
v_toSeqRight_2007_ = lean_ctor_get(v_toApplicative_2000_, 4);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_toApplicative_2000_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v_toApplicative_2000_, 1);
lean_dec(v_unused_2062_);
v___x_2009_ = v_toApplicative_2000_;
v_isShared_2010_ = v_isSharedCheck_2061_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_toSeqRight_2007_);
lean_inc(v_toSeqLeft_2006_);
lean_inc(v_toSeq_2005_);
lean_inc(v_toFunctor_2004_);
lean_dec(v_toApplicative_2000_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2061_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___f_2011_; lean_object* v___f_2012_; lean_object* v___f_2013_; lean_object* v___f_2014_; lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___f_2017_; lean_object* v___f_2018_; lean_object* v___x_2020_; 
v___f_2011_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__1));
v___f_2012_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2004_);
v___f_2013_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2013_, 0, v_toFunctor_2004_);
v___f_2014_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2014_, 0, v_toFunctor_2004_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___f_2013_);
lean_ctor_set(v___x_2015_, 1, v___f_2014_);
v___f_2016_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2016_, 0, v_toSeqRight_2007_);
v___f_2017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2017_, 0, v_toSeqLeft_2006_);
v___f_2018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2018_, 0, v_toSeq_2005_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v___f_2016_);
lean_ctor_set(v___x_2009_, 3, v___f_2017_);
lean_ctor_set(v___x_2009_, 2, v___f_2018_);
lean_ctor_set(v___x_2009_, 1, v___f_2011_);
lean_ctor_set(v___x_2009_, 0, v___x_2015_);
v___x_2020_ = v___x_2009_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___f_2011_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v___f_2018_);
lean_ctor_set(v_reuseFailAlloc_2060_, 3, v___f_2017_);
lean_ctor_set(v_reuseFailAlloc_2060_, 4, v___f_2016_);
v___x_2020_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 1, v___f_2012_);
lean_ctor_set(v___x_2002_, 0, v___x_2020_);
v___x_2022_ = v___x_2002_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v___f_2012_);
v___x_2022_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; lean_object* v_toApplicative_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2057_; 
v___x_2023_ = l_StateRefT_x27_instMonad___redArg(v___x_2022_);
v_toApplicative_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v___x_2023_, 1);
lean_dec(v_unused_2058_);
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2057_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_toApplicative_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2057_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v_toFunctor_2028_; lean_object* v_toSeq_2029_; lean_object* v_toSeqLeft_2030_; lean_object* v_toSeqRight_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2055_; 
v_toFunctor_2028_ = lean_ctor_get(v_toApplicative_2024_, 0);
v_toSeq_2029_ = lean_ctor_get(v_toApplicative_2024_, 2);
v_toSeqLeft_2030_ = lean_ctor_get(v_toApplicative_2024_, 3);
v_toSeqRight_2031_ = lean_ctor_get(v_toApplicative_2024_, 4);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_toApplicative_2024_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; 
v_unused_2056_ = lean_ctor_get(v_toApplicative_2024_, 1);
lean_dec(v_unused_2056_);
v___x_2033_ = v_toApplicative_2024_;
v_isShared_2034_ = v_isSharedCheck_2055_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_toSeqRight_2031_);
lean_inc(v_toSeqLeft_2030_);
lean_inc(v_toSeq_2029_);
lean_inc(v_toFunctor_2028_);
lean_dec(v_toApplicative_2024_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2055_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___f_2035_; lean_object* v___f_2036_; lean_object* v___f_2037_; lean_object* v___f_2038_; lean_object* v___x_2039_; lean_object* v___f_2040_; lean_object* v___f_2041_; lean_object* v___f_2042_; lean_object* v___x_2044_; 
v___f_2035_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__3));
v___f_2036_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2028_);
v___f_2037_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2037_, 0, v_toFunctor_2028_);
v___f_2038_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2038_, 0, v_toFunctor_2028_);
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___f_2037_);
lean_ctor_set(v___x_2039_, 1, v___f_2038_);
v___f_2040_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2040_, 0, v_toSeqRight_2031_);
v___f_2041_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2041_, 0, v_toSeqLeft_2030_);
v___f_2042_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2042_, 0, v_toSeq_2029_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 4, v___f_2040_);
lean_ctor_set(v___x_2033_, 3, v___f_2041_);
lean_ctor_set(v___x_2033_, 2, v___f_2042_);
lean_ctor_set(v___x_2033_, 1, v___f_2035_);
lean_ctor_set(v___x_2033_, 0, v___x_2039_);
v___x_2044_ = v___x_2033_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___f_2035_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v___f_2042_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v___f_2041_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v___f_2040_);
v___x_2044_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2046_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 1, v___f_2036_);
lean_ctor_set(v___x_2026_, 0, v___x_2044_);
v___x_2046_ = v___x_2026_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___f_2036_);
v___x_2046_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___f_2050_; lean_object* v___x_1110__overap_2051_; lean_object* v___x_2052_; 
v___x_2047_ = l_StateRefT_x27_instMonad___redArg(v___x_2046_);
v___x_2048_ = lean_box(0);
v___x_2049_ = l_instInhabitedOfMonad___redArg(v___x_2047_, v___x_2048_);
v___f_2050_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2050_, 0, v___x_2049_);
v___x_1110__overap_2051_ = lean_panic_fn_borrowed(v___f_2050_, v_msg_1990_);
lean_dec_ref(v___f_2050_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1995_);
lean_inc(v___y_1994_);
lean_inc_ref(v___y_1993_);
lean_inc(v___y_1992_);
lean_inc_ref(v___y_1991_);
v___x_2052_ = lean_apply_7(v___x_1110__overap_2051_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, lean_box(0));
return v___x_2052_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___boxed(lean_object* v_msg_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(v_msg_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_2074_, uint8_t v___x_2075_, lean_object* v_derivedValMap_2076_, lean_object* v_x_2077_, lean_object* v_x_2078_){
_start:
{
if (lean_obj_tag(v_x_2078_) == 0)
{
return v_x_2077_;
}
else
{
lean_object* v_head_2079_; lean_object* v_tail_2080_; lean_object* v_cinfo_2100_; lean_object* v_parents_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v_head_2079_ = lean_ctor_get(v_x_2078_, 0);
lean_inc(v_head_2079_);
v_tail_2080_ = lean_ctor_get(v_x_2078_, 1);
lean_inc(v_tail_2080_);
lean_dec_ref_known(v_x_2078_, 2);
v_cinfo_2100_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2076_, v_head_2079_);
v_parents_2101_ = lean_ctor_get(v_cinfo_2100_, 0);
lean_inc_ref(v_parents_2101_);
lean_dec_ref(v_cinfo_2100_);
v___x_2102_ = lean_unsigned_to_nat(0u);
v___x_2103_ = lean_array_get_size(v_parents_2101_);
v___x_2104_ = lean_nat_dec_lt(v___x_2102_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_dec_ref(v_parents_2101_);
goto v___jp_2095_;
}
else
{
size_t v___x_2105_; size_t v___x_2106_; uint8_t v___x_2107_; 
v___x_2105_ = ((size_t)0ULL);
v___x_2106_ = lean_usize_of_nat(v___x_2103_);
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2077_, v_parents_2101_, v___x_2105_, v___x_2106_);
lean_dec_ref(v_parents_2101_);
if (v___x_2107_ == 0)
{
goto v___jp_2095_;
}
else
{
lean_object* v___x_2108_; 
v___x_2108_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2074_, v___x_2075_, v_head_2079_, v_derivedValMap_2076_, v_x_2077_);
lean_dec(v_head_2079_);
v_x_2077_ = v___x_2108_;
v_x_2078_ = v_tail_2080_;
goto _start;
}
}
v___jp_2081_:
{
lean_object* v_vars_2082_; lean_object* v_borrows_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2094_; 
v_vars_2082_ = lean_ctor_get(v_x_2077_, 0);
v_borrows_2083_ = lean_ctor_get(v_x_2077_, 1);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_x_2077_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2085_ = v_x_2077_;
v_isShared_2086_ = v_isSharedCheck_2094_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_borrows_2083_);
lean_inc(v_vars_2082_);
lean_dec(v_x_2077_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2094_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2087_ = lean_box(0);
lean_inc(v_head_2079_);
v___x_2088_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2083_, v_head_2079_, v___x_2087_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 1, v___x_2088_);
v___x_2090_ = v___x_2085_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_vars_2082_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; 
v___x_2091_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2074_, v___x_2075_, v_head_2079_, v_derivedValMap_2076_, v___x_2090_);
lean_dec(v_head_2079_);
v_x_2077_ = v___x_2091_;
v_x_2078_ = v_tail_2080_;
goto _start;
}
}
}
v___jp_2095_:
{
lean_object* v_vars_2096_; uint8_t v___x_2097_; 
v_vars_2096_ = lean_ctor_get(v___x_2074_, 0);
v___x_2097_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2096_, v_head_2079_);
if (v___x_2097_ == 0)
{
goto v___jp_2081_;
}
else
{
if (v___x_2075_ == 0)
{
lean_object* v___x_2098_; 
v___x_2098_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2074_, v___x_2075_, v_head_2079_, v_derivedValMap_2076_, v_x_2077_);
lean_dec(v_head_2079_);
v_x_2077_ = v___x_2098_;
v_x_2078_ = v_tail_2080_;
goto _start;
}
else
{
goto v___jp_2081_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(lean_object* v___x_2110_, uint8_t v___x_2111_, lean_object* v_derivedValMap_2112_, lean_object* v_x_2113_, lean_object* v_x_2114_){
_start:
{
if (lean_obj_tag(v_x_2114_) == 0)
{
return v_x_2113_;
}
else
{
lean_object* v_head_2115_; lean_object* v_tail_2116_; lean_object* v_cinfo_2136_; lean_object* v_parents_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v_head_2115_ = lean_ctor_get(v_x_2114_, 0);
lean_inc(v_head_2115_);
v_tail_2116_ = lean_ctor_get(v_x_2114_, 1);
lean_inc(v_tail_2116_);
lean_dec_ref_known(v_x_2114_, 2);
v_cinfo_2136_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2112_, v_head_2115_);
v_parents_2137_ = lean_ctor_get(v_cinfo_2136_, 0);
lean_inc_ref(v_parents_2137_);
lean_dec_ref(v_cinfo_2136_);
v___x_2138_ = lean_unsigned_to_nat(0u);
v___x_2139_ = lean_array_get_size(v_parents_2137_);
v___x_2140_ = lean_nat_dec_lt(v___x_2138_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_dec_ref(v_parents_2137_);
goto v___jp_2131_;
}
else
{
size_t v___x_2141_; size_t v___x_2142_; uint8_t v___x_2143_; 
v___x_2141_ = ((size_t)0ULL);
v___x_2142_ = lean_usize_of_nat(v___x_2139_);
v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2113_, v_parents_2137_, v___x_2141_, v___x_2142_);
lean_dec_ref(v_parents_2137_);
if (v___x_2143_ == 0)
{
goto v___jp_2131_;
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2110_, v___x_2111_, v_head_2115_, v_derivedValMap_2112_, v_x_2113_);
lean_dec(v_head_2115_);
v___x_2145_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2110_, v___x_2111_, v_derivedValMap_2112_, v___x_2144_, v_tail_2116_);
return v___x_2145_;
}
}
v___jp_2117_:
{
lean_object* v_vars_2118_; lean_object* v_borrows_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2130_; 
v_vars_2118_ = lean_ctor_get(v_x_2113_, 0);
v_borrows_2119_ = lean_ctor_get(v_x_2113_, 1);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_x_2113_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2121_ = v_x_2113_;
v_isShared_2122_ = v_isSharedCheck_2130_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_borrows_2119_);
lean_inc(v_vars_2118_);
lean_dec(v_x_2113_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2130_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2123_ = lean_box(0);
lean_inc(v_head_2115_);
v___x_2124_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2119_, v_head_2115_, v___x_2123_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v___x_2124_);
v___x_2126_ = v___x_2121_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_vars_2118_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2110_, v___x_2111_, v_head_2115_, v_derivedValMap_2112_, v___x_2126_);
lean_dec(v_head_2115_);
v___x_2128_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2110_, v___x_2111_, v_derivedValMap_2112_, v___x_2127_, v_tail_2116_);
return v___x_2128_;
}
}
}
v___jp_2131_:
{
lean_object* v_vars_2132_; uint8_t v___x_2133_; 
v_vars_2132_ = lean_ctor_get(v___x_2110_, 0);
v___x_2133_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2132_, v_head_2115_);
if (v___x_2133_ == 0)
{
goto v___jp_2117_;
}
else
{
if (v___x_2111_ == 0)
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2110_, v___x_2111_, v_head_2115_, v_derivedValMap_2112_, v_x_2113_);
lean_dec(v_head_2115_);
v___x_2135_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2110_, v___x_2111_, v_derivedValMap_2112_, v___x_2134_, v_tail_2116_);
return v___x_2135_;
}
else
{
goto v___jp_2117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(lean_object* v___x_2146_, uint8_t v___x_2147_, lean_object* v_fvarId_2148_, lean_object* v_derivedValMap_2149_, lean_object* v_liveVars_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_derivedValMap_2149_, v_fvarId_2148_);
if (lean_obj_tag(v___x_2151_) == 1)
{
lean_object* v_val_2152_; lean_object* v_children_2153_; lean_object* v___x_2154_; 
v_val_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_val_2152_);
lean_dec_ref_known(v___x_2151_, 1);
v_children_2153_ = lean_ctor_get(v_val_2152_, 1);
lean_inc(v_children_2153_);
lean_dec(v_val_2152_);
v___x_2154_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(v___x_2146_, v___x_2147_, v_derivedValMap_2149_, v_liveVars_2150_, v_children_2153_);
return v___x_2154_;
}
else
{
lean_dec(v___x_2151_);
return v_liveVars_2150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0___boxed(lean_object* v___x_2155_, lean_object* v___x_2156_, lean_object* v_fvarId_2157_, lean_object* v_derivedValMap_2158_, lean_object* v_liveVars_2159_){
_start:
{
uint8_t v___x_1721__boxed_2160_; lean_object* v_res_2161_; 
v___x_1721__boxed_2160_ = lean_unbox(v___x_2156_);
v_res_2161_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2155_, v___x_1721__boxed_2160_, v_fvarId_2157_, v_derivedValMap_2158_, v_liveVars_2159_);
lean_dec(v_derivedValMap_2158_);
lean_dec(v_fvarId_2157_);
lean_dec_ref(v___x_2155_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v___x_2162_, lean_object* v___x_2163_, lean_object* v_derivedValMap_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_){
_start:
{
uint8_t v___x_1726__boxed_2167_; lean_object* v_res_2168_; 
v___x_1726__boxed_2167_ = lean_unbox(v___x_2163_);
v_res_2168_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2_spec__3(v___x_2162_, v___x_1726__boxed_2167_, v_derivedValMap_2164_, v_x_2165_, v_x_2166_);
lean_dec(v_derivedValMap_2164_);
lean_dec_ref(v___x_2162_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2___boxed(lean_object* v___x_2169_, lean_object* v___x_2170_, lean_object* v_derivedValMap_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
uint8_t v___x_1750__boxed_2174_; lean_object* v_res_2175_; 
v___x_1750__boxed_2174_ = lean_unbox(v___x_2170_);
v_res_2175_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0_spec__2(v___x_2169_, v___x_1750__boxed_2174_, v_derivedValMap_2171_, v_x_2172_, v_x_2173_);
lean_dec(v_derivedValMap_2171_);
lean_dec_ref(v___x_2169_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(lean_object* v_fvarId_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v___x_2180_; lean_object* v_vars_2181_; uint8_t v___x_2182_; 
v___x_2180_ = lean_st_ref_get(v_a_2178_);
v_vars_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc_ref(v_vars_2181_);
lean_dec(v___x_2180_);
v___x_2182_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2181_, v_fvarId_2176_);
lean_dec_ref(v_vars_2181_);
if (v___x_2182_ == 0)
{
lean_object* v_derivedValMap_2183_; lean_object* v___x_2184_; lean_object* v_vars_2185_; lean_object* v_borrows_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2200_; 
v_derivedValMap_2183_ = lean_ctor_get(v_a_2177_, 2);
v___x_2184_ = lean_st_ref_take(v_a_2178_);
v_vars_2185_ = lean_ctor_get(v___x_2184_, 0);
v_borrows_2186_ = lean_ctor_get(v___x_2184_, 1);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2188_ = v___x_2184_;
v_isShared_2189_ = v_isSharedCheck_2200_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_borrows_2186_);
lean_inc(v_vars_2185_);
lean_dec(v___x_2184_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2200_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2190_ = lean_box(0);
lean_inc(v_fvarId_2176_);
v___x_2191_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_vars_2185_, v_fvarId_2176_, v___x_2190_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2191_);
v___x_2193_ = v___x_2188_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_borrows_2186_);
v___x_2193_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2194_ = lean_st_ref_put(v_a_2178_, v___x_2193_);
v___x_2195_ = lean_st_ref_take(v_a_2178_);
lean_inc(v___x_2195_);
v___x_2196_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0_spec__0(v___x_2195_, v___x_2182_, v_fvarId_2176_, v_derivedValMap_2183_, v___x_2195_);
lean_dec(v_fvarId_2176_);
lean_dec(v___x_2195_);
v___x_2197_ = lean_st_ref_put(v_a_2178_, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2190_);
return v___x_2198_;
}
}
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v_fvarId_2176_);
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg___boxed(lean_object* v_fvarId_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
return v_res_2207_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2209_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_2210_ = lean_unsigned_to_nat(20u);
v___x_2211_ = lean_unsigned_to_nat(343u);
v___x_2212_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__0));
v___x_2213_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_2214_ = l_mkPanicMessageWithDecl(v___x_2213_, v___x_2212_, v___x_2211_, v___x_2210_, v___x_2209_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(lean_object* v_value_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
switch(lean_obj_tag(v_value_2215_))
{
case 4:
{
lean_object* v_fvarId_2223_; lean_object* v_args_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_fvarId_2223_ = lean_ctor_get(v_value_2215_, 0);
lean_inc(v_fvarId_2223_);
v_args_2224_ = lean_ctor_get(v_value_2215_, 1);
lean_inc_ref(v_args_2224_);
lean_dec_ref_known(v_value_2215_, 2);
v___x_2225_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2223_, v_a_2216_, v_a_2217_);
lean_dec_ref(v___x_2225_);
v___x_2226_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2224_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec_ref(v_args_2224_);
return v___x_2226_;
}
case 5:
{
lean_object* v_args_2227_; lean_object* v___x_2228_; 
v_args_2227_ = lean_ctor_get(v_value_2215_, 1);
lean_inc_ref(v_args_2227_);
lean_dec_ref_known(v_value_2215_, 2);
v___x_2228_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2227_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec_ref(v_args_2227_);
return v___x_2228_;
}
case 6:
{
lean_object* v_var_2229_; lean_object* v___x_2230_; 
v_var_2229_ = lean_ctor_get(v_value_2215_, 1);
lean_inc(v_var_2229_);
lean_dec_ref_known(v_value_2215_, 2);
v___x_2230_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2229_, v_a_2216_, v_a_2217_);
return v___x_2230_;
}
case 7:
{
lean_object* v_var_2231_; lean_object* v___x_2232_; 
v_var_2231_ = lean_ctor_get(v_value_2215_, 1);
lean_inc(v_var_2231_);
lean_dec_ref_known(v_value_2215_, 2);
v___x_2232_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2231_, v_a_2216_, v_a_2217_);
return v___x_2232_;
}
case 8:
{
lean_object* v_var_2233_; lean_object* v___x_2234_; 
v_var_2233_ = lean_ctor_get(v_value_2215_, 2);
lean_inc(v_var_2233_);
lean_dec_ref_known(v_value_2215_, 3);
v___x_2234_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2233_, v_a_2216_, v_a_2217_);
return v___x_2234_;
}
case 9:
{
lean_object* v_args_2235_; lean_object* v___x_2236_; 
v_args_2235_ = lean_ctor_get(v_value_2215_, 1);
lean_inc_ref(v_args_2235_);
lean_dec_ref_known(v_value_2215_, 2);
v___x_2236_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2235_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec_ref(v_args_2235_);
return v___x_2236_;
}
case 10:
{
lean_object* v_args_2237_; lean_object* v___x_2238_; 
v_args_2237_ = lean_ctor_get(v_value_2215_, 1);
lean_inc_ref(v_args_2237_);
lean_dec_ref_known(v_value_2215_, 2);
v___x_2238_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2237_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec_ref(v_args_2237_);
return v___x_2238_;
}
case 11:
{
lean_object* v_var_2239_; lean_object* v___x_2240_; 
v_var_2239_ = lean_ctor_get(v_value_2215_, 1);
lean_inc(v_var_2239_);
lean_dec_ref_known(v_value_2215_, 2);
v___x_2240_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2239_, v_a_2216_, v_a_2217_);
return v___x_2240_;
}
case 12:
{
lean_object* v_var_2241_; lean_object* v_args_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_var_2241_ = lean_ctor_get(v_value_2215_, 0);
lean_inc(v_var_2241_);
v_args_2242_ = lean_ctor_get(v_value_2215_, 2);
lean_inc_ref(v_args_2242_);
lean_dec_ref_known(v_value_2215_, 3);
v___x_2243_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_var_2241_, v_a_2216_, v_a_2217_);
lean_dec_ref(v___x_2243_);
v___x_2244_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_2242_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec_ref(v_args_2242_);
return v___x_2244_;
}
case 13:
{
lean_object* v_fvarId_2245_; lean_object* v___x_2246_; 
v_fvarId_2245_ = lean_ctor_get(v_value_2215_, 1);
lean_inc(v_fvarId_2245_);
lean_dec_ref_known(v_value_2215_, 2);
v___x_2246_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2245_, v_a_2216_, v_a_2217_);
return v___x_2246_;
}
case 14:
{
lean_object* v_fvarId_2247_; lean_object* v___x_2248_; 
v_fvarId_2247_ = lean_ctor_get(v_value_2215_, 0);
lean_inc(v_fvarId_2247_);
lean_dec_ref_known(v_value_2215_, 1);
v___x_2248_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2247_, v_a_2216_, v_a_2217_);
return v___x_2248_;
}
case 15:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_dec_ref_known(v_value_2215_, 1);
v___x_2249_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___closed__1);
v___x_2250_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1(v___x_2249_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2250_;
}
default: 
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec(v_value_2215_);
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue___boxed(lean_object* v_value_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(v_value_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(lean_object* v_fvarId_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_2262_, v_a_2263_, v_a_2264_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___boxed(lean_object* v_fvarId_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0(v_fvarId_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_);
lean_dec(v_a_2277_);
lean_dec_ref(v_a_2276_);
lean_dec(v_a_2275_);
lean_dec_ref(v_a_2274_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(lean_object* v_fvarId_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v___x_2283_; lean_object* v_vars_2284_; lean_object* v_borrows_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2299_; 
v___x_2283_ = lean_st_ref_take(v_a_2281_);
v_vars_2284_ = lean_ctor_get(v___x_2283_, 0);
v_borrows_2285_ = lean_ctor_get(v___x_2283_, 1);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2287_ = v___x_2283_;
v_isShared_2288_ = v_isSharedCheck_2299_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_borrows_2285_);
lean_inc(v_vars_2284_);
lean_dec(v___x_2283_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2299_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v_vars_2292_; lean_object* v_borrows_2293_; lean_object* v___x_2295_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_2291_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
lean_inc(v_fvarId_2280_);
v_vars_2292_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2290_, v___x_2291_, v_vars_2284_, v_fvarId_2280_);
v_borrows_2293_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2290_, v___x_2291_, v_borrows_2285_, v_fvarId_2280_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 1, v_borrows_2293_);
lean_ctor_set(v___x_2287_, 0, v_vars_2292_);
v___x_2295_ = v___x_2287_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_vars_2292_);
lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_borrows_2293_);
v___x_2295_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = lean_st_ref_put(v_a_2281_, v___x_2295_);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2289_);
return v___x_2297_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg___boxed(lean_object* v_fvarId_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___redArg(v_fvarId_2300_, v_a_2301_);
lean_dec(v_a_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(lean_object* v_fvarId_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2312_; lean_object* v_vars_2313_; lean_object* v_borrows_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2328_; 
v___x_2312_ = lean_st_ref_take(v_a_2306_);
v_vars_2313_ = lean_ctor_get(v___x_2312_, 0);
v_borrows_2314_ = lean_ctor_get(v___x_2312_, 1);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2316_ = v___x_2312_;
v_isShared_2317_ = v_isSharedCheck_2328_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_borrows_2314_);
lean_inc(v_vars_2313_);
lean_dec(v___x_2312_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2328_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v_vars_2321_; lean_object* v_borrows_2322_; lean_object* v___x_2324_; 
v___x_2318_ = lean_box(0);
v___x_2319_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__10));
v___x_2320_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LiveVars_union___closed__11));
lean_inc(v_fvarId_2304_);
v_vars_2321_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2319_, v___x_2320_, v_vars_2313_, v_fvarId_2304_);
v_borrows_2322_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v___x_2319_, v___x_2320_, v_borrows_2314_, v_fvarId_2304_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 1, v_borrows_2322_);
lean_ctor_set(v___x_2316_, 0, v_vars_2321_);
v___x_2324_ = v___x_2316_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_vars_2321_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_borrows_2322_);
v___x_2324_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = lean_st_ref_put(v_a_2306_, v___x_2324_);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2318_);
return v___x_2326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar___boxed(lean_object* v_fvarId_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_bindVar(v_fvarId_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(lean_object* v_liveVars_2338_, lean_object* v_derivedValMap_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_){
_start:
{
if (lean_obj_tag(v_x_2341_) == 0)
{
return v_x_2340_;
}
else
{
lean_object* v_head_2342_; lean_object* v_tail_2343_; lean_object* v_cinfo_2362_; lean_object* v_parents_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; 
v_head_2342_ = lean_ctor_get(v_x_2341_, 0);
lean_inc(v_head_2342_);
v_tail_2343_ = lean_ctor_get(v_x_2341_, 1);
lean_inc(v_tail_2343_);
lean_dec_ref_known(v_x_2341_, 2);
v_cinfo_2362_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2339_, v_head_2342_);
v_parents_2363_ = lean_ctor_get(v_cinfo_2362_, 0);
lean_inc_ref(v_parents_2363_);
lean_dec_ref(v_cinfo_2362_);
v___x_2364_ = lean_unsigned_to_nat(0u);
v___x_2365_ = lean_array_get_size(v_parents_2363_);
v___x_2366_ = lean_nat_dec_lt(v___x_2364_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_dec_ref(v_parents_2363_);
goto v___jp_2344_;
}
else
{
size_t v___x_2367_; size_t v___x_2368_; uint8_t v___x_2369_; 
v___x_2367_ = ((size_t)0ULL);
v___x_2368_ = lean_usize_of_nat(v___x_2365_);
v___x_2369_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2340_, v_parents_2363_, v___x_2367_, v___x_2368_);
lean_dec_ref(v_parents_2363_);
if (v___x_2369_ == 0)
{
goto v___jp_2344_;
}
else
{
lean_object* v___x_2370_; 
v___x_2370_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2338_, v_head_2342_, v_derivedValMap_2339_, v_x_2340_);
lean_dec(v_head_2342_);
v_x_2340_ = v___x_2370_;
v_x_2341_ = v_tail_2343_;
goto _start;
}
}
v___jp_2344_:
{
lean_object* v_vars_2345_; uint8_t v___x_2346_; 
v_vars_2345_ = lean_ctor_get(v_liveVars_2338_, 0);
v___x_2346_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2345_, v_head_2342_);
if (v___x_2346_ == 0)
{
lean_object* v_vars_2347_; lean_object* v_borrows_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2359_; 
v_vars_2347_ = lean_ctor_get(v_x_2340_, 0);
v_borrows_2348_ = lean_ctor_get(v_x_2340_, 1);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_x_2340_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2350_ = v_x_2340_;
v_isShared_2351_ = v_isSharedCheck_2359_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_borrows_2348_);
lean_inc(v_vars_2347_);
lean_dec(v_x_2340_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2359_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2352_ = lean_box(0);
lean_inc(v_head_2342_);
v___x_2353_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2348_, v_head_2342_, v___x_2352_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 1, v___x_2353_);
v___x_2355_ = v___x_2350_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_vars_2347_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2356_; 
v___x_2356_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2338_, v_head_2342_, v_derivedValMap_2339_, v___x_2355_);
lean_dec(v_head_2342_);
v_x_2340_ = v___x_2356_;
v_x_2341_ = v_tail_2343_;
goto _start;
}
}
}
else
{
lean_object* v___x_2360_; 
v___x_2360_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2338_, v_head_2342_, v_derivedValMap_2339_, v_x_2340_);
lean_dec(v_head_2342_);
v_x_2340_ = v___x_2360_;
v_x_2341_ = v_tail_2343_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(lean_object* v_liveVars_2372_, lean_object* v_derivedValMap_2373_, lean_object* v_x_2374_, lean_object* v_x_2375_){
_start:
{
if (lean_obj_tag(v_x_2375_) == 0)
{
return v_x_2374_;
}
else
{
lean_object* v_head_2376_; lean_object* v_tail_2377_; lean_object* v_cinfo_2396_; lean_object* v_parents_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v_head_2376_ = lean_ctor_get(v_x_2375_, 0);
lean_inc(v_head_2376_);
v_tail_2377_ = lean_ctor_get(v_x_2375_, 1);
lean_inc(v_tail_2377_);
lean_dec_ref_known(v_x_2375_, 2);
v_cinfo_2396_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2(v_derivedValMap_2373_, v_head_2376_);
v_parents_2397_ = lean_ctor_get(v_cinfo_2396_, 0);
lean_inc_ref(v_parents_2397_);
lean_dec_ref(v_cinfo_2396_);
v___x_2398_ = lean_unsigned_to_nat(0u);
v___x_2399_ = lean_array_get_size(v_parents_2397_);
v___x_2400_ = lean_nat_dec_lt(v___x_2398_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_dec_ref(v_parents_2397_);
goto v___jp_2378_;
}
else
{
size_t v___x_2401_; size_t v___x_2402_; uint8_t v___x_2403_; 
v___x_2401_ = ((size_t)0ULL);
v___x_2402_ = lean_usize_of_nat(v___x_2399_);
v___x_2403_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__3(v_x_2374_, v_parents_2397_, v___x_2401_, v___x_2402_);
lean_dec_ref(v_parents_2397_);
if (v___x_2403_ == 0)
{
goto v___jp_2378_;
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2372_, v_head_2376_, v_derivedValMap_2373_, v_x_2374_);
lean_dec(v_head_2376_);
v___x_2405_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2372_, v_derivedValMap_2373_, v___x_2404_, v_tail_2377_);
return v___x_2405_;
}
}
v___jp_2378_:
{
lean_object* v_vars_2379_; uint8_t v___x_2380_; 
v_vars_2379_ = lean_ctor_get(v_liveVars_2372_, 0);
v___x_2380_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2379_, v_head_2376_);
if (v___x_2380_ == 0)
{
lean_object* v_vars_2381_; lean_object* v_borrows_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2393_; 
v_vars_2381_ = lean_ctor_get(v_x_2374_, 0);
v_borrows_2382_ = lean_ctor_get(v_x_2374_, 1);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_x_2374_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2384_ = v_x_2374_;
v_isShared_2385_ = v_isSharedCheck_2393_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_borrows_2382_);
lean_inc(v_vars_2381_);
lean_dec(v_x_2374_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2393_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v___x_2386_ = lean_box(0);
lean_inc(v_head_2376_);
v___x_2387_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2382_, v_head_2376_, v___x_2386_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 1, v___x_2387_);
v___x_2389_ = v___x_2384_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_vars_2381_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2372_, v_head_2376_, v_derivedValMap_2373_, v___x_2389_);
lean_dec(v_head_2376_);
v___x_2391_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2372_, v_derivedValMap_2373_, v___x_2390_, v_tail_2377_);
return v___x_2391_;
}
}
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2372_, v_head_2376_, v_derivedValMap_2373_, v_x_2374_);
lean_dec(v_head_2376_);
v___x_2395_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2372_, v_derivedValMap_2373_, v___x_2394_, v_tail_2377_);
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(lean_object* v_liveVars_2406_, lean_object* v_fvarId_2407_, lean_object* v_derivedValMap_2408_, lean_object* v_liveVars_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_derivedValMap_2408_, v_fvarId_2407_);
if (lean_obj_tag(v___x_2410_) == 1)
{
lean_object* v_val_2411_; lean_object* v_children_2412_; lean_object* v___x_2413_; 
v_val_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_val_2411_);
lean_dec_ref_known(v___x_2410_, 1);
v_children_2412_ = lean_ctor_get(v_val_2411_, 1);
lean_inc(v_children_2412_);
lean_dec(v_val_2411_);
v___x_2413_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(v_liveVars_2406_, v_derivedValMap_2408_, v_liveVars_2409_, v_children_2412_);
return v___x_2413_;
}
else
{
lean_dec(v___x_2410_);
return v_liveVars_2409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0___boxed(lean_object* v_liveVars_2414_, lean_object* v_fvarId_2415_, lean_object* v_derivedValMap_2416_, lean_object* v_liveVars_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2414_, v_fvarId_2415_, v_derivedValMap_2416_, v_liveVars_2417_);
lean_dec(v_derivedValMap_2416_);
lean_dec(v_fvarId_2415_);
lean_dec_ref(v_liveVars_2414_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1___boxed(lean_object* v_liveVars_2419_, lean_object* v_derivedValMap_2420_, lean_object* v_x_2421_, lean_object* v_x_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_List_foldl___at___00List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0_spec__1(v_liveVars_2419_, v_derivedValMap_2420_, v_x_2421_, v_x_2422_);
lean_dec(v_derivedValMap_2420_);
lean_dec_ref(v_liveVars_2419_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0___boxed(lean_object* v_liveVars_2424_, lean_object* v_derivedValMap_2425_, lean_object* v_x_2426_, lean_object* v_x_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0_spec__0(v_liveVars_2424_, v_derivedValMap_2425_, v_x_2426_, v_x_2427_);
lean_dec(v_derivedValMap_2425_);
lean_dec_ref(v_liveVars_2424_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(lean_object* v_a_2429_, lean_object* v_liveVars_2430_, lean_object* v_x_2431_, lean_object* v_x_2432_){
_start:
{
if (lean_obj_tag(v_x_2432_) == 0)
{
return v_x_2431_;
}
else
{
lean_object* v_key_2433_; lean_object* v_tail_2434_; lean_object* v_derivedValMap_2435_; lean_object* v___x_2436_; 
v_key_2433_ = lean_ctor_get(v_x_2432_, 0);
v_tail_2434_ = lean_ctor_get(v_x_2432_, 2);
v_derivedValMap_2435_ = lean_ctor_get(v_a_2429_, 2);
v___x_2436_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2430_, v_key_2433_, v_derivedValMap_2435_, v_x_2431_);
v_x_2431_ = v___x_2436_;
v_x_2432_ = v_tail_2434_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2___boxed(lean_object* v_a_2438_, lean_object* v_liveVars_2439_, lean_object* v_x_2440_, lean_object* v_x_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(v_a_2438_, v_liveVars_2439_, v_x_2440_, v_x_2441_);
lean_dec(v_x_2441_);
lean_dec_ref(v_liveVars_2439_);
lean_dec_ref(v_a_2438_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(lean_object* v_a_2443_, lean_object* v_liveVars_2444_, lean_object* v_x_2445_, lean_object* v_x_2446_){
_start:
{
if (lean_obj_tag(v_x_2446_) == 0)
{
return v_x_2445_;
}
else
{
lean_object* v_key_2447_; lean_object* v_tail_2448_; lean_object* v_derivedValMap_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_key_2447_ = lean_ctor_get(v_x_2446_, 0);
v_tail_2448_ = lean_ctor_get(v_x_2446_, 2);
v_derivedValMap_2449_ = lean_ctor_get(v_a_2443_, 2);
v___x_2450_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2444_, v_key_2447_, v_derivedValMap_2449_, v_x_2445_);
v___x_2451_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1_spec__2(v_a_2443_, v_liveVars_2444_, v___x_2450_, v_tail_2448_);
return v___x_2451_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1___boxed(lean_object* v_a_2452_, lean_object* v_liveVars_2453_, lean_object* v_x_2454_, lean_object* v_x_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(v_a_2452_, v_liveVars_2453_, v_x_2454_, v_x_2455_);
lean_dec(v_x_2455_);
lean_dec_ref(v_liveVars_2453_);
lean_dec_ref(v_a_2452_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(lean_object* v_a_2457_, lean_object* v_liveVars_2458_, lean_object* v_as_2459_, size_t v_i_2460_, size_t v_stop_2461_, lean_object* v_b_2462_){
_start:
{
uint8_t v___x_2463_; 
v___x_2463_ = lean_usize_dec_eq(v_i_2460_, v_stop_2461_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; size_t v___x_2466_; size_t v___x_2467_; 
v___x_2464_ = lean_array_uget_borrowed(v_as_2459_, v_i_2460_);
v___x_2465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__1(v_a_2457_, v_liveVars_2458_, v_b_2462_, v___x_2464_);
v___x_2466_ = ((size_t)1ULL);
v___x_2467_ = lean_usize_add(v_i_2460_, v___x_2466_);
v_i_2460_ = v___x_2467_;
v_b_2462_ = v___x_2465_;
goto _start;
}
else
{
return v_b_2462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2___boxed(lean_object* v_a_2469_, lean_object* v_liveVars_2470_, lean_object* v_as_2471_, lean_object* v_i_2472_, lean_object* v_stop_2473_, lean_object* v_b_2474_){
_start:
{
size_t v_i_boxed_2475_; size_t v_stop_boxed_2476_; lean_object* v_res_2477_; 
v_i_boxed_2475_ = lean_unbox_usize(v_i_2472_);
lean_dec(v_i_2472_);
v_stop_boxed_2476_ = lean_unbox_usize(v_stop_2473_);
lean_dec(v_stop_2473_);
v_res_2477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2469_, v_liveVars_2470_, v_as_2471_, v_i_boxed_2475_, v_stop_boxed_2476_, v_b_2474_);
lean_dec_ref(v_as_2471_);
lean_dec_ref(v_liveVars_2470_);
lean_dec_ref(v_a_2469_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(lean_object* v_a_2478_, lean_object* v_liveVars_2479_, lean_object* v_x_2480_, lean_object* v_x_2481_){
_start:
{
if (lean_obj_tag(v_x_2481_) == 0)
{
return v_x_2480_;
}
else
{
lean_object* v_head_2482_; lean_object* v_tail_2483_; lean_object* v_derivedValMap_2484_; lean_object* v_vars_2485_; lean_object* v_borrows_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2497_; 
v_head_2482_ = lean_ctor_get(v_x_2481_, 0);
lean_inc(v_head_2482_);
v_tail_2483_ = lean_ctor_get(v_x_2481_, 1);
lean_inc(v_tail_2483_);
lean_dec_ref_known(v_x_2481_, 2);
v_derivedValMap_2484_ = lean_ctor_get(v_a_2478_, 2);
v_vars_2485_ = lean_ctor_get(v_x_2480_, 0);
v_borrows_2486_ = lean_ctor_get(v_x_2480_, 1);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_x_2480_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2488_ = v_x_2480_;
v_isShared_2489_ = v_isSharedCheck_2497_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_borrows_2486_);
lean_inc(v_vars_2485_);
lean_dec(v_x_2480_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2497_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2490_ = lean_box(0);
lean_inc(v_head_2482_);
v___x_2491_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_borrows_2486_, v_head_2482_, v___x_2490_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 1, v___x_2491_);
v___x_2493_ = v___x_2488_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_vars_2485_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; 
v___x_2494_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__0(v_liveVars_2479_, v_head_2482_, v_derivedValMap_2484_, v___x_2493_);
lean_dec(v_head_2482_);
v_x_2480_ = v___x_2494_;
v_x_2481_ = v_tail_2483_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3___boxed(lean_object* v_a_2498_, lean_object* v_liveVars_2499_, lean_object* v_x_2500_, lean_object* v_x_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(v_a_2498_, v_liveVars_2499_, v_x_2500_, v_x_2501_);
lean_dec_ref(v_liveVars_2499_);
lean_dec_ref(v_a_2498_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(lean_object* v_liveVars_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v___y_2507_; lean_object* v_unconditionalBorrows_2518_; lean_object* v___x_2519_; lean_object* v_vars_2520_; lean_object* v_buckets_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v_unconditionalBorrows_2518_ = lean_ctor_get(v_a_2504_, 1);
lean_inc(v_unconditionalBorrows_2518_);
lean_inc_ref(v_liveVars_2503_);
v___x_2519_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__3(v_a_2504_, v_liveVars_2503_, v_liveVars_2503_, v_unconditionalBorrows_2518_);
v_vars_2520_ = lean_ctor_get(v_liveVars_2503_, 0);
v_buckets_2521_ = lean_ctor_get(v_vars_2520_, 1);
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = lean_array_get_size(v_buckets_2521_);
v___x_2524_ = lean_nat_dec_lt(v___x_2522_, v___x_2523_);
if (v___x_2524_ == 0)
{
v___y_2507_ = v___x_2519_;
goto v___jp_2506_;
}
else
{
size_t v___x_2525_; size_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = ((size_t)0ULL);
v___x_2526_ = lean_usize_of_nat(v___x_2523_);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2504_, v_liveVars_2503_, v_buckets_2521_, v___x_2525_, v___x_2526_, v___x_2519_);
v___y_2507_ = v___x_2527_;
goto v___jp_2506_;
}
v___jp_2506_:
{
lean_object* v_borrows_2508_; lean_object* v_buckets_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v_borrows_2508_ = lean_ctor_get(v___y_2507_, 1);
v_buckets_2509_ = lean_ctor_get(v_borrows_2508_, 1);
v___x_2510_ = lean_unsigned_to_nat(0u);
v___x_2511_ = lean_array_get_size(v_buckets_2509_);
v___x_2512_ = lean_nat_dec_lt(v___x_2510_, v___x_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; 
lean_dec_ref(v_liveVars_2503_);
v___x_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___y_2507_);
return v___x_2513_;
}
else
{
size_t v___x_2514_; size_t v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
lean_inc_ref(v_buckets_2509_);
v___x_2514_ = ((size_t)0ULL);
v___x_2515_ = lean_usize_of_nat(v___x_2511_);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows_spec__2(v_a_2504_, v_liveVars_2503_, v_buckets_2509_, v___x_2514_, v___x_2515_, v___y_2507_);
lean_dec_ref(v_buckets_2509_);
lean_dec_ref(v_liveVars_2503_);
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
return v___x_2517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg___boxed(lean_object* v_liveVars_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v_liveVars_2528_, v_a_2529_);
lean_dec_ref(v_a_2529_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows(lean_object* v_liveVars_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v_liveVars_2532_, v_a_2533_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___boxed(lean_object* v_liveVars_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows(v_liveVars_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2565_; 
v___x_2553_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_2554_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_2553_, v_a_2550_);
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2565_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2565_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2559_ = lean_st_ref_take(v_a_2551_);
lean_dec(v___x_2559_);
v___x_2560_ = lean_box(0);
v___x_2561_ = lean_st_ref_put(v_a_2551_, v_a_2555_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2560_);
v___x_2563_ = v___x_2557_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2560_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg___boxed(lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___redArg(v_a_2566_, v_a_2567_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2589_; 
v___x_2577_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_2578_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_2577_, v_a_2570_);
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2589_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2589_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2583_ = lean_st_ref_take(v_a_2571_);
lean_dec(v___x_2583_);
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_st_ref_put(v_a_2571_, v_a_2579_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2584_);
v___x_2587_ = v___x_2581_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2584_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars___boxed(lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_setRetLiveVars(v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(lean_object* v_fvarId_2598_, lean_object* v_k_2599_, lean_object* v_n_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2603_ = lean_unsigned_to_nat(0u);
v___x_2604_ = lean_nat_dec_eq(v_n_2600_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_object* v_varMap_2605_; lean_object* v___f_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v_isDefiniteRef_2609_; uint8_t v_persistent_2610_; uint8_t v___y_2612_; 
v_varMap_2605_ = lean_ctor_get(v_a_2601_, 3);
v___f_2606_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_2607_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_fvarId_2598_);
lean_inc(v_varMap_2605_);
v___x_2608_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_2606_, v___x_2607_, v_varMap_2605_, v_fvarId_2598_);
v_isDefiniteRef_2609_ = lean_ctor_get_uint8(v___x_2608_, sizeof(void*)*2 + 1);
v_persistent_2610_ = lean_ctor_get_uint8(v___x_2608_, sizeof(void*)*2 + 2);
lean_dec(v___x_2608_);
if (v_isDefiniteRef_2609_ == 0)
{
uint8_t v___x_2615_; 
v___x_2615_ = 1;
v___y_2612_ = v___x_2615_;
goto v___jp_2611_;
}
else
{
v___y_2612_ = v___x_2604_;
goto v___jp_2611_;
}
v___jp_2611_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_2613_, 0, v_fvarId_2598_);
lean_ctor_set(v___x_2613_, 1, v_n_2600_);
lean_ctor_set(v___x_2613_, 2, v_k_2599_);
lean_ctor_set_uint8(v___x_2613_, sizeof(void*)*3, v___y_2612_);
lean_ctor_set_uint8(v___x_2613_, sizeof(void*)*3 + 1, v_persistent_2610_);
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
return v___x_2614_;
}
}
else
{
lean_object* v___x_2616_; 
lean_dec(v_n_2600_);
lean_dec(v_fvarId_2598_);
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_k_2599_);
return v___x_2616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg___boxed(lean_object* v_fvarId_2617_, lean_object* v_k_2618_, lean_object* v_n_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___redArg(v_fvarId_2617_, v_k_2618_, v_n_2619_, v_a_2620_);
lean_dec_ref(v_a_2620_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(lean_object* v_fvarId_2623_, lean_object* v_k_2624_, lean_object* v_n_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2633_ = lean_unsigned_to_nat(0u);
v___x_2634_ = lean_nat_dec_eq(v_n_2625_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_object* v_varMap_2635_; lean_object* v___f_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v_isDefiniteRef_2639_; uint8_t v_persistent_2640_; uint8_t v___y_2642_; 
v_varMap_2635_ = lean_ctor_get(v_a_2626_, 3);
v___f_2636_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getVarInfo___redArg___closed__0));
v___x_2637_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
lean_inc(v_fvarId_2623_);
lean_inc(v_varMap_2635_);
v___x_2638_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v___f_2636_, v___x_2637_, v_varMap_2635_, v_fvarId_2623_);
v_isDefiniteRef_2639_ = lean_ctor_get_uint8(v___x_2638_, sizeof(void*)*2 + 1);
v_persistent_2640_ = lean_ctor_get_uint8(v___x_2638_, sizeof(void*)*2 + 2);
lean_dec(v___x_2638_);
if (v_isDefiniteRef_2639_ == 0)
{
uint8_t v___x_2645_; 
v___x_2645_ = 1;
v___y_2642_ = v___x_2645_;
goto v___jp_2641_;
}
else
{
v___y_2642_ = v___x_2634_;
goto v___jp_2641_;
}
v___jp_2641_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_2643_, 0, v_fvarId_2623_);
lean_ctor_set(v___x_2643_, 1, v_n_2625_);
lean_ctor_set(v___x_2643_, 2, v_k_2624_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*3, v___y_2642_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*3 + 1, v_persistent_2640_);
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
return v___x_2644_;
}
}
else
{
lean_object* v___x_2646_; 
lean_dec(v_n_2625_);
lean_dec(v_fvarId_2623_);
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v_k_2624_);
return v___x_2646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc___boxed(lean_object* v_fvarId_2647_, lean_object* v_k_2648_, lean_object* v_n_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addInc(v_fvarId_2647_, v_k_2648_, v_n_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0_spec__0(lean_object* v_msg_2658_){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedVarInfo_default));
v___x_2660_ = lean_panic_fn_borrowed(v___x_2659_, v_msg_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(lean_object* v_t_2661_, lean_object* v_k_2662_){
_start:
{
if (lean_obj_tag(v_t_2661_) == 0)
{
lean_object* v_k_2663_; lean_object* v_v_2664_; lean_object* v_l_2665_; lean_object* v_r_2666_; uint8_t v___x_2667_; 
v_k_2663_ = lean_ctor_get(v_t_2661_, 1);
v_v_2664_ = lean_ctor_get(v_t_2661_, 2);
v_l_2665_ = lean_ctor_get(v_t_2661_, 3);
v_r_2666_ = lean_ctor_get(v_t_2661_, 4);
v___x_2667_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2662_, v_k_2663_);
switch(v___x_2667_)
{
case 0:
{
v_t_2661_ = v_l_2665_;
goto _start;
}
case 1:
{
lean_inc(v_v_2664_);
return v_v_2664_;
}
default: 
{
v_t_2661_ = v_r_2666_;
goto _start;
}
}
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3);
v___x_2671_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0_spec__0(v___x_2670_);
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0___boxed(lean_object* v_t_2672_, lean_object* v_k_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_t_2672_, v_k_2673_);
lean_dec(v_k_2673_);
lean_dec(v_t_2672_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(lean_object* v_fvarId_2675_, lean_object* v_k_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v_varMap_2679_; lean_object* v___x_2680_; lean_object* v_ctorInfo_2681_; 
v_varMap_2679_ = lean_ctor_get(v_a_2677_, 3);
v___x_2680_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_2679_, v_fvarId_2675_);
v_ctorInfo_2681_ = lean_ctor_get(v___x_2680_, 1);
lean_inc(v_ctorInfo_2681_);
if (lean_obj_tag(v_ctorInfo_2681_) == 0)
{
uint8_t v_isDefiniteRef_2682_; uint8_t v_persistent_2683_; lean_object* v___x_2684_; uint8_t v___y_2686_; 
v_isDefiniteRef_2682_ = lean_ctor_get_uint8(v___x_2680_, sizeof(void*)*2 + 1);
v_persistent_2683_ = lean_ctor_get_uint8(v___x_2680_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_2680_);
v___x_2684_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_2682_ == 0)
{
uint8_t v___x_2690_; 
v___x_2690_ = 1;
v___y_2686_ = v___x_2690_;
goto v___jp_2685_;
}
else
{
uint8_t v___x_2691_; 
v___x_2691_ = 0;
v___y_2686_ = v___x_2691_;
goto v___jp_2685_;
}
v___jp_2685_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = lean_box(0);
v___x_2688_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_2688_, 0, v_fvarId_2675_);
lean_ctor_set(v___x_2688_, 1, v___x_2684_);
lean_ctor_set(v___x_2688_, 2, v___x_2687_);
lean_ctor_set(v___x_2688_, 3, v_k_2676_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*4, v___y_2686_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*4 + 1, v_persistent_2683_);
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
return v___x_2689_;
}
}
else
{
uint8_t v_persistent_2692_; lean_object* v_val_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2707_; 
v_persistent_2692_ = lean_ctor_get_uint8(v___x_2680_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_2680_);
v_val_2693_ = lean_ctor_get(v_ctorInfo_2681_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_ctorInfo_2681_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2695_ = v_ctorInfo_2681_;
v_isShared_2696_ = v_isSharedCheck_2707_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_val_2693_);
lean_dec(v_ctorInfo_2681_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2707_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
uint8_t v___x_2697_; 
v___x_2697_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_val_2693_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; 
lean_del_object(v___x_2695_);
lean_dec(v_val_2693_);
lean_dec(v_fvarId_2675_);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v_k_2676_);
return v___x_2698_;
}
else
{
lean_object* v_size_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; lean_object* v___x_2703_; 
v_size_2699_ = lean_ctor_get(v_val_2693_, 2);
lean_inc(v_size_2699_);
lean_dec(v_val_2693_);
v___x_2700_ = lean_unsigned_to_nat(1u);
v___x_2701_ = 0;
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v_size_2699_);
v___x_2703_ = v___x_2695_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_size_2699_);
v___x_2703_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_2704_, 0, v_fvarId_2675_);
lean_ctor_set(v___x_2704_, 1, v___x_2700_);
lean_ctor_set(v___x_2704_, 2, v___x_2703_);
lean_ctor_set(v___x_2704_, 3, v_k_2676_);
lean_ctor_set_uint8(v___x_2704_, sizeof(void*)*4, v___x_2701_);
lean_ctor_set_uint8(v___x_2704_, sizeof(void*)*4 + 1, v_persistent_2692_);
v___x_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
return v___x_2705_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg___boxed(lean_object* v_fvarId_2708_, lean_object* v_k_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_2708_, v_k_2709_, v_a_2710_);
lean_dec_ref(v_a_2710_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(lean_object* v_fvarId_2713_, lean_object* v_k_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_2713_, v_k_2714_, v_a_2715_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___boxed(lean_object* v_fvarId_2723_, lean_object* v_k_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec(v_fvarId_2723_, v_k_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
lean_dec(v_a_2726_);
lean_dec_ref(v_a_2725_);
return v_res_2732_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(lean_object* v_x_2733_, lean_object* v_x_2734_){
_start:
{
lean_object* v_snd_2735_; lean_object* v_snd_2736_; uint8_t v___x_2737_; 
v_snd_2735_ = lean_ctor_get(v_x_2733_, 1);
v_snd_2736_ = lean_ctor_get(v_x_2734_, 1);
v___x_2737_ = lean_nat_dec_lt(v_snd_2735_, v_snd_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0___boxed(lean_object* v_x_2738_, lean_object* v_x_2739_){
_start:
{
uint8_t v_res_2740_; lean_object* v_r_2741_; 
v_res_2740_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v_x_2738_, v_x_2739_);
lean_dec_ref(v_x_2739_);
lean_dec_ref(v_x_2738_);
v_r_2741_ = lean_box(v_res_2740_);
return v_r_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(lean_object* v_hi_2742_, lean_object* v_pivot_2743_, lean_object* v_as_2744_, lean_object* v_i_2745_, lean_object* v_k_2746_){
_start:
{
uint8_t v___x_2747_; 
v___x_2747_ = lean_nat_dec_lt(v_k_2746_, v_hi_2742_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_dec(v_k_2746_);
v___x_2748_ = lean_array_fswap(v_as_2744_, v_i_2745_, v_hi_2742_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_i_2745_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
return v___x_2749_;
}
else
{
lean_object* v___x_2750_; lean_object* v_snd_2751_; lean_object* v_snd_2752_; uint8_t v___x_2753_; 
v___x_2750_ = lean_array_fget_borrowed(v_as_2744_, v_k_2746_);
v_snd_2751_ = lean_ctor_get(v___x_2750_, 1);
v_snd_2752_ = lean_ctor_get(v_pivot_2743_, 1);
v___x_2753_ = lean_nat_dec_lt(v_snd_2751_, v_snd_2752_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = lean_unsigned_to_nat(1u);
v___x_2755_ = lean_nat_add(v_k_2746_, v___x_2754_);
lean_dec(v_k_2746_);
v_k_2746_ = v___x_2755_;
goto _start;
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2757_ = lean_array_fswap(v_as_2744_, v_i_2745_, v_k_2746_);
v___x_2758_ = lean_unsigned_to_nat(1u);
v___x_2759_ = lean_nat_add(v_i_2745_, v___x_2758_);
lean_dec(v_i_2745_);
v___x_2760_ = lean_nat_add(v_k_2746_, v___x_2758_);
lean_dec(v_k_2746_);
v_as_2744_ = v___x_2757_;
v_i_2745_ = v___x_2759_;
v_k_2746_ = v___x_2760_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg___boxed(lean_object* v_hi_2762_, lean_object* v_pivot_2763_, lean_object* v_as_2764_, lean_object* v_i_2765_, lean_object* v_k_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(v_hi_2762_, v_pivot_2763_, v_as_2764_, v_i_2765_, v_k_2766_);
lean_dec_ref(v_pivot_2763_);
lean_dec(v_hi_2762_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(lean_object* v_n_2768_, lean_object* v_as_2769_, lean_object* v_lo_2770_, lean_object* v_hi_2771_){
_start:
{
lean_object* v___y_2773_; uint8_t v___x_2783_; 
v___x_2783_ = lean_nat_dec_lt(v_lo_2770_, v_hi_2771_);
if (v___x_2783_ == 0)
{
lean_dec(v_lo_2770_);
return v_as_2769_;
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v_mid_2786_; lean_object* v___y_2788_; lean_object* v___y_2794_; lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v___x_2784_ = lean_nat_add(v_lo_2770_, v_hi_2771_);
v___x_2785_ = lean_unsigned_to_nat(1u);
v_mid_2786_ = lean_nat_shiftr(v___x_2784_, v___x_2785_);
lean_dec(v___x_2784_);
v___x_2799_ = lean_array_fget_borrowed(v_as_2769_, v_mid_2786_);
v___x_2800_ = lean_array_fget_borrowed(v_as_2769_, v_lo_2770_);
v___x_2801_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v___x_2799_, v___x_2800_);
if (v___x_2801_ == 0)
{
v___y_2794_ = v_as_2769_;
goto v___jp_2793_;
}
else
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_array_fswap(v_as_2769_, v_lo_2770_, v_mid_2786_);
v___y_2794_ = v___x_2802_;
goto v___jp_2793_;
}
v___jp_2787_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v___x_2789_ = lean_array_fget_borrowed(v___y_2788_, v_mid_2786_);
v___x_2790_ = lean_array_fget_borrowed(v___y_2788_, v_hi_2771_);
v___x_2791_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v___x_2789_, v___x_2790_);
if (v___x_2791_ == 0)
{
lean_dec(v_mid_2786_);
v___y_2773_ = v___y_2788_;
goto v___jp_2772_;
}
else
{
lean_object* v___x_2792_; 
v___x_2792_ = lean_array_fswap(v___y_2788_, v_mid_2786_, v_hi_2771_);
lean_dec(v_mid_2786_);
v___y_2773_ = v___x_2792_;
goto v___jp_2772_;
}
}
v___jp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v___x_2795_ = lean_array_fget_borrowed(v___y_2794_, v_hi_2771_);
v___x_2796_ = lean_array_fget_borrowed(v___y_2794_, v_lo_2770_);
v___x_2797_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___lam__0(v___x_2795_, v___x_2796_);
if (v___x_2797_ == 0)
{
v___y_2788_ = v___y_2794_;
goto v___jp_2787_;
}
else
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_array_fswap(v___y_2794_, v_lo_2770_, v_hi_2771_);
v___y_2788_ = v___x_2798_;
goto v___jp_2787_;
}
}
}
v___jp_2772_:
{
lean_object* v_pivot_2774_; lean_object* v___x_2775_; lean_object* v_fst_2776_; lean_object* v_snd_2777_; uint8_t v___x_2778_; 
v_pivot_2774_ = lean_array_fget(v___y_2773_, v_hi_2771_);
lean_inc_n(v_lo_2770_, 2);
v___x_2775_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(v_hi_2771_, v_pivot_2774_, v___y_2773_, v_lo_2770_, v_lo_2770_);
lean_dec(v_pivot_2774_);
v_fst_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_fst_2776_);
v_snd_2777_ = lean_ctor_get(v___x_2775_, 1);
lean_inc(v_snd_2777_);
lean_dec_ref(v___x_2775_);
v___x_2778_ = lean_nat_dec_le(v_hi_2771_, v_fst_2776_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2779_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_n_2768_, v_snd_2777_, v_lo_2770_, v_fst_2776_);
v___x_2780_ = lean_unsigned_to_nat(1u);
v___x_2781_ = lean_nat_add(v_fst_2776_, v___x_2780_);
lean_dec(v_fst_2776_);
v_as_2769_ = v___x_2779_;
v_lo_2770_ = v___x_2781_;
goto _start;
}
else
{
lean_dec(v_fst_2776_);
lean_dec(v_lo_2770_);
return v_snd_2777_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg___boxed(lean_object* v_n_2803_, lean_object* v_as_2804_, lean_object* v_lo_2805_, lean_object* v_hi_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_n_2803_, v_as_2804_, v_lo_2805_, v_hi_2806_);
lean_dec(v_hi_2806_);
lean_dec(v_n_2803_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(lean_object* v_altLiveVars_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
if (lean_obj_tag(v_a_2809_) == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2814_, 0, v_a_2810_);
v___x_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
return v___x_2815_;
}
else
{
lean_object* v_key_2816_; lean_object* v_tail_2817_; lean_object* v_fst_2818_; lean_object* v_snd_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2870_; 
v_key_2816_ = lean_ctor_get(v_a_2809_, 0);
v_tail_2817_ = lean_ctor_get(v_a_2809_, 2);
v_fst_2818_ = lean_ctor_get(v_a_2810_, 0);
v_snd_2819_ = lean_ctor_get(v_a_2810_, 1);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_a_2810_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2821_ = v_a_2810_;
v_isShared_2822_ = v_isSharedCheck_2870_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_snd_2819_);
lean_inc(v_fst_2818_);
lean_dec(v_a_2810_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2870_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v_varMap_2823_; lean_object* v_vars_2824_; lean_object* v_borrows_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v_varMap_2823_ = lean_ctor_get(v___y_2811_, 3);
v_vars_2824_ = lean_ctor_get(v_altLiveVars_2808_, 0);
v_borrows_2825_ = lean_ctor_get(v_altLiveVars_2808_, 1);
v___x_2826_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_2823_, v_key_2816_);
v___x_2827_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_2824_, v_key_2816_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; uint8_t v_isPossibleRef_2834_; 
v___x_2828_ = lean_st_ref_get(v___y_2812_);
v_isPossibleRef_2834_ = lean_ctor_get_uint8(v___x_2826_, sizeof(void*)*2);
if (v_isPossibleRef_2834_ == 0)
{
lean_dec(v___x_2828_);
lean_dec_ref(v___x_2826_);
goto v___jp_2829_;
}
else
{
lean_object* v_idx_2835_; lean_object* v_borrows_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2847_; 
v_idx_2835_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_idx_2835_);
lean_dec_ref(v___x_2826_);
v_borrows_2836_ = lean_ctor_get(v___x_2828_, 1);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v___x_2828_, 0);
lean_dec(v_unused_2848_);
v___x_2838_ = v___x_2828_;
v_isShared_2839_ = v_isSharedCheck_2847_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_borrows_2836_);
lean_dec(v___x_2828_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2847_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
uint8_t v___x_2840_; 
v___x_2840_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_2836_, v_key_2816_);
lean_dec_ref(v_borrows_2836_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2842_; 
lean_del_object(v___x_2821_);
lean_inc(v_key_2816_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v_idx_2835_);
lean_ctor_set(v___x_2838_, 0, v_key_2816_);
v___x_2842_ = v___x_2838_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_key_2816_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_idx_2835_);
v___x_2842_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_array_push(v_snd_2819_, v___x_2842_);
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v_fst_2818_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v_a_2809_ = v_tail_2817_;
v_a_2810_ = v___x_2844_;
goto _start;
}
}
else
{
lean_del_object(v___x_2838_);
lean_dec(v_idx_2835_);
goto v___jp_2829_;
}
}
}
v___jp_2829_:
{
lean_object* v___x_2831_; 
if (v_isShared_2822_ == 0)
{
v___x_2831_ = v___x_2821_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_fst_2818_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_snd_2819_);
v___x_2831_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
v_a_2809_ = v_tail_2817_;
v_a_2810_ = v___x_2831_;
goto _start;
}
}
}
else
{
lean_object* v___x_2849_; lean_object* v_borrows_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2868_; 
v___x_2849_ = lean_st_ref_get(v___y_2812_);
v_borrows_2855_ = lean_ctor_get(v___x_2849_, 1);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; 
v_unused_2869_ = lean_ctor_get(v___x_2849_, 0);
lean_dec(v_unused_2869_);
v___x_2857_ = v___x_2849_;
v_isShared_2858_ = v_isSharedCheck_2868_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_borrows_2855_);
lean_dec(v___x_2849_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2868_;
goto v_resetjp_2856_;
}
v___jp_2850_:
{
lean_object* v___x_2852_; 
if (v_isShared_2822_ == 0)
{
v___x_2852_ = v___x_2821_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_fst_2818_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_snd_2819_);
v___x_2852_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
v_a_2809_ = v_tail_2817_;
v_a_2810_ = v___x_2852_;
goto _start;
}
}
v_resetjp_2856_:
{
uint8_t v___x_2859_; 
v___x_2859_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_2855_, v_key_2816_);
lean_dec_ref(v_borrows_2855_);
if (v___x_2859_ == 0)
{
lean_del_object(v___x_2857_);
lean_dec_ref(v___x_2826_);
goto v___jp_2850_;
}
else
{
uint8_t v___x_2860_; 
v___x_2860_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_2825_, v_key_2816_);
if (v___x_2860_ == 0)
{
lean_object* v_idx_2861_; lean_object* v___x_2863_; 
lean_del_object(v___x_2821_);
v_idx_2861_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_idx_2861_);
lean_dec_ref(v___x_2826_);
lean_inc(v_key_2816_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 1, v_idx_2861_);
lean_ctor_set(v___x_2857_, 0, v_key_2816_);
v___x_2863_ = v___x_2857_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_key_2816_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_idx_2861_);
v___x_2863_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_array_push(v_fst_2818_, v___x_2863_);
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
lean_ctor_set(v___x_2865_, 1, v_snd_2819_);
v_a_2809_ = v_tail_2817_;
v_a_2810_ = v___x_2865_;
goto _start;
}
}
else
{
lean_del_object(v___x_2857_);
lean_dec_ref(v___x_2826_);
goto v___jp_2850_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg___boxed(lean_object* v_altLiveVars_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_2871_, v_a_2872_, v_a_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v_a_2872_);
lean_dec_ref(v_altLiveVars_2871_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(lean_object* v_altLiveVars_2878_, lean_object* v_as_2879_, size_t v_sz_2880_, size_t v_i_2881_, lean_object* v_b_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
uint8_t v___x_2890_; 
v___x_2890_ = lean_usize_dec_lt(v_i_2881_, v_sz_2880_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v_b_2882_);
return v___x_2891_;
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2893_; 
v_a_2892_ = lean_array_uget_borrowed(v_as_2879_, v_i_2881_);
v___x_2893_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_2878_, v_a_2892_, v_b_2882_, v___y_2883_, v___y_2884_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2906_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2906_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2906_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
if (lean_obj_tag(v_a_2894_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2900_; 
v_a_2898_ = lean_ctor_get(v_a_2894_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v_a_2894_, 1);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v_a_2898_);
v___x_2900_ = v___x_2896_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2898_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
else
{
lean_object* v_a_2902_; size_t v___x_2903_; size_t v___x_2904_; 
lean_del_object(v___x_2896_);
v_a_2902_ = lean_ctor_get(v_a_2894_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v_a_2894_, 1);
v___x_2903_ = ((size_t)1ULL);
v___x_2904_ = lean_usize_add(v_i_2881_, v___x_2903_);
v_i_2881_ = v___x_2904_;
v_b_2882_ = v_a_2902_;
goto _start;
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
v_a_2907_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2893_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2893_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1___boxed(lean_object* v_altLiveVars_2915_, lean_object* v_as_2916_, lean_object* v_sz_2917_, lean_object* v_i_2918_, lean_object* v_b_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
size_t v_sz_boxed_2927_; size_t v_i_boxed_2928_; lean_object* v_res_2929_; 
v_sz_boxed_2927_ = lean_unbox_usize(v_sz_2917_);
lean_dec(v_sz_2917_);
v_i_boxed_2928_ = lean_unbox_usize(v_i_2918_);
lean_dec(v_i_2918_);
v_res_2929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(v_altLiveVars_2915_, v_as_2916_, v_sz_boxed_2927_, v_i_boxed_2928_, v_b_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec_ref(v_as_2916_);
lean_dec_ref(v_altLiveVars_2915_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(lean_object* v_as_2930_, size_t v_i_2931_, size_t v_stop_2932_, lean_object* v_b_2933_, lean_object* v___y_2934_){
_start:
{
uint8_t v___x_2936_; 
v___x_2936_ = lean_usize_dec_eq(v_i_2931_, v_stop_2932_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; lean_object* v_fst_2938_; lean_object* v___x_2939_; 
v___x_2937_ = lean_array_uget_borrowed(v_as_2930_, v_i_2931_);
v_fst_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_fst_2938_);
v___x_2939_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fst_2938_, v_b_2933_, v___y_2934_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; size_t v___x_2941_; size_t v___x_2942_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = ((size_t)1ULL);
v___x_2942_ = lean_usize_add(v_i_2931_, v___x_2941_);
v_i_2931_ = v___x_2942_;
v_b_2933_ = v_a_2940_;
goto _start;
}
else
{
return v___x_2939_;
}
}
else
{
lean_object* v___x_2944_; 
v___x_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2944_, 0, v_b_2933_);
return v___x_2944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg___boxed(lean_object* v_as_2945_, lean_object* v_i_2946_, lean_object* v_stop_2947_, lean_object* v_b_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
size_t v_i_boxed_2951_; size_t v_stop_boxed_2952_; lean_object* v_res_2953_; 
v_i_boxed_2951_ = lean_unbox_usize(v_i_2946_);
lean_dec(v_i_2946_);
v_stop_boxed_2952_ = lean_unbox_usize(v_stop_2947_);
lean_dec(v_stop_2947_);
v_res_2953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_as_2945_, v_i_boxed_2951_, v_stop_boxed_2952_, v_b_2948_, v___y_2949_);
lean_dec_ref(v___y_2949_);
lean_dec_ref(v_as_2945_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(lean_object* v_as_2954_, size_t v_i_2955_, size_t v_stop_2956_, lean_object* v_b_2957_, lean_object* v___y_2958_){
_start:
{
uint8_t v___x_2960_; 
v___x_2960_ = lean_usize_dec_eq(v_i_2955_, v_stop_2956_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; lean_object* v_fst_2962_; lean_object* v_varMap_2963_; lean_object* v___x_2964_; uint8_t v_isDefiniteRef_2965_; uint8_t v_persistent_2966_; lean_object* v___x_2967_; uint8_t v___y_2969_; 
v___x_2961_ = lean_array_uget_borrowed(v_as_2954_, v_i_2955_);
v_fst_2962_ = lean_ctor_get(v___x_2961_, 0);
v_varMap_2963_ = lean_ctor_get(v___y_2958_, 3);
v___x_2964_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_2963_, v_fst_2962_);
v_isDefiniteRef_2965_ = lean_ctor_get_uint8(v___x_2964_, sizeof(void*)*2 + 1);
v_persistent_2966_ = lean_ctor_get_uint8(v___x_2964_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_2964_);
v___x_2967_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_2965_ == 0)
{
uint8_t v___x_2974_; 
v___x_2974_ = 1;
v___y_2969_ = v___x_2974_;
goto v___jp_2968_;
}
else
{
v___y_2969_ = v___x_2960_;
goto v___jp_2968_;
}
v___jp_2968_:
{
lean_object* v___x_2970_; size_t v___x_2971_; size_t v___x_2972_; 
lean_inc(v_fst_2962_);
v___x_2970_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_2970_, 0, v_fst_2962_);
lean_ctor_set(v___x_2970_, 1, v___x_2967_);
lean_ctor_set(v___x_2970_, 2, v_b_2957_);
lean_ctor_set_uint8(v___x_2970_, sizeof(void*)*3, v___y_2969_);
lean_ctor_set_uint8(v___x_2970_, sizeof(void*)*3 + 1, v_persistent_2966_);
v___x_2971_ = ((size_t)1ULL);
v___x_2972_ = lean_usize_add(v_i_2955_, v___x_2971_);
v_i_2955_ = v___x_2972_;
v_b_2957_ = v___x_2970_;
goto _start;
}
}
else
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v_b_2957_);
return v___x_2975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg___boxed(lean_object* v_as_2976_, lean_object* v_i_2977_, lean_object* v_stop_2978_, lean_object* v_b_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
size_t v_i_boxed_2982_; size_t v_stop_boxed_2983_; lean_object* v_res_2984_; 
v_i_boxed_2982_ = lean_unbox_usize(v_i_2977_);
lean_dec(v_i_2977_);
v_stop_boxed_2983_ = lean_unbox_usize(v_stop_2978_);
lean_dec(v_stop_2978_);
v_res_2984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v_as_2976_, v_i_boxed_2982_, v_stop_boxed_2983_, v_b_2979_, v___y_2980_);
lean_dec_ref(v___y_2980_);
lean_dec_ref(v_as_2976_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(lean_object* v_altLiveVars_2989_, lean_object* v_k_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v_vars_3000_; lean_object* v___x_3001_; lean_object* v_buckets_3002_; size_t v_sz_3003_; size_t v___x_3004_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___x_3013_; 
v___x_2998_ = lean_unsigned_to_nat(0u);
v___x_2999_ = lean_st_ref_get(v_a_2992_);
v_vars_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_ref(v_vars_3000_);
lean_dec(v___x_2999_);
v___x_3001_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___closed__1));
v_buckets_3002_ = lean_ctor_get(v_vars_3000_, 1);
lean_inc_ref(v_buckets_3002_);
lean_dec_ref(v_vars_3000_);
v_sz_3003_ = lean_array_size(v_buckets_3002_);
v___x_3004_ = ((size_t)0ULL);
v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__1(v_altLiveVars_2989_, v_buckets_3002_, v_sz_3003_, v___x_3004_, v___x_3001_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
lean_dec_ref(v_buckets_3002_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3063_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3063_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3063_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v_fst_3018_; lean_object* v_snd_3019_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___x_3034_; lean_object* v___y_3036_; lean_object* v_a_3037_; lean_object* v___y_3043_; lean_object* v___x_3052_; lean_object* v___y_3054_; lean_object* v___y_3055_; uint8_t v___x_3057_; 
v_fst_3018_ = lean_ctor_get(v_a_3014_, 0);
lean_inc(v_fst_3018_);
v_snd_3019_ = lean_ctor_get(v_a_3014_, 1);
lean_inc(v_snd_3019_);
lean_dec(v_a_3014_);
v___x_3034_ = lean_unsigned_to_nat(1u);
v___x_3052_ = lean_array_get_size(v_snd_3019_);
v___x_3057_ = lean_nat_dec_eq(v___x_3052_, v___x_2998_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; lean_object* v___y_3060_; uint8_t v___x_3062_; 
v___x_3058_ = lean_nat_sub(v___x_3052_, v___x_3034_);
v___x_3062_ = lean_nat_dec_le(v___x_2998_, v___x_3058_);
if (v___x_3062_ == 0)
{
lean_inc(v___x_3058_);
v___y_3060_ = v___x_3058_;
goto v___jp_3059_;
}
else
{
v___y_3060_ = v___x_2998_;
goto v___jp_3059_;
}
v___jp_3059_:
{
uint8_t v___x_3061_; 
v___x_3061_ = lean_nat_dec_le(v___y_3060_, v___x_3058_);
if (v___x_3061_ == 0)
{
lean_dec(v___x_3058_);
lean_inc(v___y_3060_);
v___y_3054_ = v___y_3060_;
v___y_3055_ = v___y_3060_;
goto v___jp_3053_;
}
else
{
v___y_3054_ = v___y_3060_;
v___y_3055_ = v___x_3058_;
goto v___jp_3053_;
}
}
}
else
{
v___y_3043_ = v_snd_3019_;
goto v___jp_3042_;
}
v___jp_3020_:
{
lean_object* v___x_3026_; 
v___x_3026_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v___y_3024_, v_fst_3018_, v___y_3022_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec(v___y_3024_);
v___y_3006_ = v___y_3021_;
v___y_3007_ = v___y_3023_;
v___y_3008_ = v___x_3026_;
goto v___jp_3005_;
}
v___jp_3027_:
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_nat_dec_le(v___y_3032_, v___y_3030_);
if (v___x_3033_ == 0)
{
lean_dec(v___y_3030_);
lean_inc(v___y_3032_);
v___y_3021_ = v___y_3028_;
v___y_3022_ = v___y_3032_;
v___y_3023_ = v___y_3029_;
v___y_3024_ = v___y_3031_;
v___y_3025_ = v___y_3032_;
goto v___jp_3020_;
}
else
{
v___y_3021_ = v___y_3028_;
v___y_3022_ = v___y_3032_;
v___y_3023_ = v___y_3029_;
v___y_3024_ = v___y_3031_;
v___y_3025_ = v___y_3030_;
goto v___jp_3020_;
}
}
v___jp_3035_:
{
lean_object* v___x_3038_; uint8_t v___x_3039_; 
v___x_3038_ = lean_array_get_size(v_fst_3018_);
v___x_3039_ = lean_nat_dec_eq(v___x_3038_, v___x_2998_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = lean_nat_sub(v___x_3038_, v___x_3034_);
v___x_3041_ = lean_nat_dec_le(v___x_2998_, v___x_3040_);
if (v___x_3041_ == 0)
{
lean_inc(v___x_3040_);
v___y_3028_ = v_a_3037_;
v___y_3029_ = v___y_3036_;
v___y_3030_ = v___x_3040_;
v___y_3031_ = v___x_3038_;
v___y_3032_ = v___x_3040_;
goto v___jp_3027_;
}
else
{
v___y_3028_ = v_a_3037_;
v___y_3029_ = v___y_3036_;
v___y_3030_ = v___x_3040_;
v___y_3031_ = v___x_3038_;
v___y_3032_ = v___x_2998_;
goto v___jp_3027_;
}
}
else
{
v___y_3006_ = v_a_3037_;
v___y_3007_ = v___y_3036_;
v___y_3008_ = v_fst_3018_;
goto v___jp_3005_;
}
}
v___jp_3042_:
{
lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3044_ = lean_array_get_size(v___y_3043_);
v___x_3045_ = lean_nat_dec_lt(v___x_2998_, v___x_3044_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3047_; 
lean_dec_ref(v___y_3043_);
lean_inc_ref(v_k_2990_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v_k_2990_);
v___x_3047_ = v___x_3016_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_k_2990_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
v___y_3036_ = v___x_3047_;
v_a_3037_ = v_k_2990_;
goto v___jp_3035_;
}
}
else
{
size_t v___x_3049_; lean_object* v___x_3050_; 
lean_del_object(v___x_3016_);
v___x_3049_ = lean_usize_of_nat(v___x_3044_);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v___y_3043_, v___x_3004_, v___x_3049_, v_k_2990_, v_a_2991_);
lean_dec_ref(v___y_3043_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
v___y_3036_ = v___x_3050_;
v_a_3037_ = v_a_3051_;
goto v___jp_3035_;
}
else
{
lean_dec(v_fst_3018_);
return v___x_3050_;
}
}
}
v___jp_3053_:
{
lean_object* v___x_3056_; 
v___x_3056_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v___x_3052_, v_snd_3019_, v___y_3054_, v___y_3055_);
lean_dec(v___y_3055_);
v___y_3043_ = v___x_3056_;
goto v___jp_3042_;
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref(v_k_2990_);
v_a_3064_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3013_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3013_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
v___jp_3005_:
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = lean_array_get_size(v___y_3008_);
v___x_3010_ = lean_nat_dec_lt(v___x_2998_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_dec_ref(v___y_3008_);
lean_dec_ref(v___y_3006_);
return v___y_3007_;
}
else
{
size_t v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v___y_3007_);
v___x_3011_ = lean_usize_of_nat(v___x_3009_);
v___x_3012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v___y_3008_, v___x_3004_, v___x_3011_, v___y_3006_, v_a_2991_);
lean_dec_ref(v___y_3008_);
return v___x_3012_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt___boxed(lean_object* v_altLiveVars_3072_, lean_object* v_k_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_altLiveVars_3072_, v_k_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec_ref(v_a_3074_);
lean_dec_ref(v_altLiveVars_3072_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(lean_object* v_altLiveVars_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___redArg(v_altLiveVars_3082_, v_a_3083_, v_a_3084_, v___y_3085_, v___y_3086_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0___boxed(lean_object* v_altLiveVars_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__0(v_altLiveVars_3093_, v_a_3094_, v_a_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v_a_3094_);
lean_dec_ref(v_altLiveVars_3093_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(lean_object* v_as_3104_, size_t v_i_3105_, size_t v_stop_3106_, lean_object* v_b_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___redArg(v_as_3104_, v_i_3105_, v_stop_3106_, v_b_3107_, v___y_3108_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2___boxed(lean_object* v_as_3116_, lean_object* v_i_3117_, lean_object* v_stop_3118_, lean_object* v_b_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
size_t v_i_boxed_3127_; size_t v_stop_boxed_3128_; lean_object* v_res_3129_; 
v_i_boxed_3127_ = lean_unbox_usize(v_i_3117_);
lean_dec(v_i_3117_);
v_stop_boxed_3128_ = lean_unbox_usize(v_stop_3118_);
lean_dec(v_stop_3118_);
v_res_3129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__2(v_as_3116_, v_i_boxed_3127_, v_stop_boxed_3128_, v_b_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec_ref(v_as_3116_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3(lean_object* v_n_3130_, lean_object* v_as_3131_, lean_object* v_lo_3132_, lean_object* v_hi_3133_, lean_object* v_w_3134_, lean_object* v_hlo_3135_, lean_object* v_hhi_3136_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___redArg(v_n_3130_, v_as_3131_, v_lo_3132_, v_hi_3133_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3___boxed(lean_object* v_n_3138_, lean_object* v_as_3139_, lean_object* v_lo_3140_, lean_object* v_hi_3141_, lean_object* v_w_3142_, lean_object* v_hlo_3143_, lean_object* v_hhi_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3(v_n_3138_, v_as_3139_, v_lo_3140_, v_hi_3141_, v_w_3142_, v_hlo_3143_, v_hhi_3144_);
lean_dec(v_hi_3141_);
lean_dec(v_n_3138_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(lean_object* v_as_3146_, size_t v_i_3147_, size_t v_stop_3148_, lean_object* v_b_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___redArg(v_as_3146_, v_i_3147_, v_stop_3148_, v_b_3149_, v___y_3150_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4___boxed(lean_object* v_as_3158_, lean_object* v_i_3159_, lean_object* v_stop_3160_, lean_object* v_b_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
size_t v_i_boxed_3169_; size_t v_stop_boxed_3170_; lean_object* v_res_3171_; 
v_i_boxed_3169_ = lean_unbox_usize(v_i_3159_);
lean_dec(v_i_3159_);
v_stop_boxed_3170_ = lean_unbox_usize(v_stop_3160_);
lean_dec(v_stop_3160_);
v_res_3171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__4(v_as_3158_, v_i_boxed_3169_, v_stop_boxed_3170_, v_b_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec_ref(v_as_3158_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3(lean_object* v_n_3172_, lean_object* v_lo_3173_, lean_object* v_hi_3174_, lean_object* v_hhi_3175_, lean_object* v_pivot_3176_, lean_object* v_as_3177_, lean_object* v_i_3178_, lean_object* v_k_3179_, lean_object* v_ilo_3180_, lean_object* v_ik_3181_, lean_object* v_w_3182_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___redArg(v_hi_3174_, v_pivot_3176_, v_as_3177_, v_i_3178_, v_k_3179_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3___boxed(lean_object* v_n_3184_, lean_object* v_lo_3185_, lean_object* v_hi_3186_, lean_object* v_hhi_3187_, lean_object* v_pivot_3188_, lean_object* v_as_3189_, lean_object* v_i_3190_, lean_object* v_k_3191_, lean_object* v_ilo_3192_, lean_object* v_ik_3193_, lean_object* v_w_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt_spec__3_spec__3(v_n_3184_, v_lo_3185_, v_hi_3186_, v_hhi_3187_, v_pivot_3188_, v_as_3189_, v_i_3190_, v_k_3191_, v_ilo_3192_, v_ik_3193_, v_w_3194_);
lean_dec_ref(v_pivot_3188_);
lean_dec(v_hi_3186_);
lean_dec(v_lo_3185_);
lean_dec(v_n_3184_);
return v_res_3195_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(lean_object* v_args_3196_, lean_object* v_x_3197_, lean_object* v_n_3198_, lean_object* v_i_3199_){
_start:
{
lean_object* v_zero_3200_; uint8_t v_isZero_3201_; 
v_zero_3200_ = lean_unsigned_to_nat(0u);
v_isZero_3201_ = lean_nat_dec_eq(v_i_3199_, v_zero_3200_);
if (v_isZero_3201_ == 1)
{
lean_dec(v_i_3199_);
return v_isZero_3201_;
}
else
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; 
v___x_3202_ = lean_box(0);
v___x_3203_ = lean_nat_sub(v_n_3198_, v_i_3199_);
v___x_3204_ = lean_array_get_borrowed(v___x_3202_, v_args_3196_, v___x_3203_);
lean_dec(v___x_3203_);
v___x_3205_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_3204_, v_x_3197_);
if (v___x_3205_ == 0)
{
lean_object* v_one_3206_; lean_object* v_n_3207_; 
v_one_3206_ = lean_unsigned_to_nat(1u);
v_n_3207_ = lean_nat_sub(v_i_3199_, v_one_3206_);
lean_dec(v_i_3199_);
v_i_3199_ = v_n_3207_;
goto _start;
}
else
{
lean_dec(v_i_3199_);
return v_isZero_3201_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg___boxed(lean_object* v_args_3209_, lean_object* v_x_3210_, lean_object* v_n_3211_, lean_object* v_i_3212_){
_start:
{
uint8_t v_res_3213_; lean_object* v_r_3214_; 
v_res_3213_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3209_, v_x_3210_, v_n_3211_, v_i_3212_);
lean_dec(v_n_3211_);
lean_dec(v_x_3210_);
lean_dec_ref(v_args_3209_);
v_r_3214_ = lean_box(v_res_3213_);
return v_r_3214_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(lean_object* v_args_3215_, lean_object* v_i_3216_){
_start:
{
lean_object* v___x_3217_; lean_object* v_x_3218_; uint8_t v___x_3219_; 
v___x_3217_ = lean_box(0);
v_x_3218_ = lean_array_get_borrowed(v___x_3217_, v_args_3215_, v_i_3216_);
lean_inc(v_i_3216_);
v___x_3219_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3215_, v_x_3218_, v_i_3216_, v_i_3216_);
lean_dec(v_i_3216_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc___boxed(lean_object* v_args_3220_, lean_object* v_i_3221_){
_start:
{
uint8_t v_res_3222_; lean_object* v_r_3223_; 
v_res_3222_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3220_, v_i_3221_);
lean_dec_ref(v_args_3220_);
v_r_3223_ = lean_box(v_res_3222_);
return v_r_3223_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(lean_object* v_args_3224_, lean_object* v_x_3225_, lean_object* v_n_3226_, lean_object* v_i_3227_, lean_object* v_a_3228_){
_start:
{
uint8_t v___x_3229_; 
v___x_3229_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___redArg(v_args_3224_, v_x_3225_, v_n_3226_, v_i_3227_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0___boxed(lean_object* v_args_3230_, lean_object* v_x_3231_, lean_object* v_n_3232_, lean_object* v_i_3233_, lean_object* v_a_3234_){
_start:
{
uint8_t v_res_3235_; lean_object* v_r_3236_; 
v_res_3235_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc_spec__0(v_args_3230_, v_x_3231_, v_n_3232_, v_i_3233_, v_a_3234_);
lean_dec(v_n_3232_);
lean_dec(v_x_3231_);
lean_dec_ref(v_args_3230_);
v_r_3236_ = lean_box(v_res_3235_);
return v_r_3236_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(lean_object* v_args_3237_, lean_object* v_arg_3238_, lean_object* v_consumeParamPred_3239_, lean_object* v_n_3240_, lean_object* v_i_3241_){
_start:
{
lean_object* v_zero_3242_; uint8_t v_isZero_3243_; 
v_zero_3242_ = lean_unsigned_to_nat(0u);
v_isZero_3243_ = lean_nat_dec_eq(v_i_3241_, v_zero_3242_);
if (v_isZero_3243_ == 1)
{
uint8_t v___x_3244_; 
lean_dec(v_i_3241_);
lean_dec_ref(v_consumeParamPred_3239_);
v___x_3244_ = 0;
return v___x_3244_;
}
else
{
lean_object* v_one_3245_; lean_object* v_n_3246_; lean_object* v___x_3247_; lean_object* v_arg_x27_3248_; 
v_one_3245_ = lean_unsigned_to_nat(1u);
v_n_3246_ = lean_nat_sub(v_i_3241_, v_one_3245_);
v___x_3247_ = lean_nat_sub(v_n_3240_, v_i_3241_);
lean_dec(v_i_3241_);
v_arg_x27_3248_ = lean_array_fget_borrowed(v_args_3237_, v___x_3247_);
if (lean_obj_tag(v_arg_x27_3248_) == 0)
{
lean_dec(v___x_3247_);
v_i_3241_ = v_n_3246_;
goto _start;
}
else
{
lean_object* v_fvarId_3250_; uint8_t v___x_3251_; 
v_fvarId_3250_ = lean_ctor_get(v_arg_x27_3248_, 0);
v___x_3251_ = l_Lean_instBEqFVarId_beq(v_arg_3238_, v_fvarId_3250_);
if (v___x_3251_ == 0)
{
lean_dec(v___x_3247_);
v_i_3241_ = v_n_3246_;
goto _start;
}
else
{
lean_object* v___x_3253_; uint8_t v___x_3254_; 
lean_inc_ref(v_consumeParamPred_3239_);
v___x_3253_ = lean_apply_1(v_consumeParamPred_3239_, v___x_3247_);
v___x_3254_ = lean_unbox(v___x_3253_);
if (v___x_3254_ == 0)
{
lean_dec(v_n_3246_);
lean_dec_ref(v_consumeParamPred_3239_);
return v___x_3251_;
}
else
{
v_i_3241_ = v_n_3246_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg___boxed(lean_object* v_args_3256_, lean_object* v_arg_3257_, lean_object* v_consumeParamPred_3258_, lean_object* v_n_3259_, lean_object* v_i_3260_){
_start:
{
uint8_t v_res_3261_; lean_object* v_r_3262_; 
v_res_3261_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3256_, v_arg_3257_, v_consumeParamPred_3258_, v_n_3259_, v_i_3260_);
lean_dec(v_n_3259_);
lean_dec(v_arg_3257_);
lean_dec_ref(v_args_3256_);
v_r_3262_ = lean_box(v_res_3261_);
return v_r_3262_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(lean_object* v_arg_3263_, lean_object* v_args_3264_, lean_object* v_consumeParamPred_3265_){
_start:
{
lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = lean_array_get_size(v_args_3264_);
v___x_3267_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3264_, v_arg_3263_, v_consumeParamPred_3265_, v___x_3266_, v___x_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux___boxed(lean_object* v_arg_3268_, lean_object* v_args_3269_, lean_object* v_consumeParamPred_3270_){
_start:
{
uint8_t v_res_3271_; lean_object* v_r_3272_; 
v_res_3271_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_arg_3268_, v_args_3269_, v_consumeParamPred_3270_);
lean_dec_ref(v_args_3269_);
lean_dec(v_arg_3268_);
v_r_3272_ = lean_box(v_res_3271_);
return v_r_3272_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(lean_object* v_args_3273_, lean_object* v_arg_3274_, lean_object* v_consumeParamPred_3275_, lean_object* v_n_3276_, lean_object* v_i_3277_, lean_object* v_a_3278_){
_start:
{
uint8_t v___x_3279_; 
v___x_3279_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___redArg(v_args_3273_, v_arg_3274_, v_consumeParamPred_3275_, v_n_3276_, v_i_3277_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0___boxed(lean_object* v_args_3280_, lean_object* v_arg_3281_, lean_object* v_consumeParamPred_3282_, lean_object* v_n_3283_, lean_object* v_i_3284_, lean_object* v_a_3285_){
_start:
{
uint8_t v_res_3286_; lean_object* v_r_3287_; 
v_res_3286_ = l___private_Init_Data_Nat_Fold_0__Nat_anyTR_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux_spec__0(v_args_3280_, v_arg_3281_, v_consumeParamPred_3282_, v_n_3283_, v_i_3284_, v_a_3285_);
lean_dec(v_n_3283_);
lean_dec(v_arg_3281_);
lean_dec_ref(v_args_3280_);
v_r_3287_ = lean_box(v_res_3286_);
return v_r_3287_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_3288_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(lean_object* v_ps_3289_, lean_object* v_i_3290_){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; uint8_t v_borrow_3293_; 
v___x_3291_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___closed__0);
v___x_3292_ = lean_array_get_borrowed(v___x_3291_, v_ps_3289_, v_i_3290_);
v_borrow_3293_ = lean_ctor_get_uint8(v___x_3292_, sizeof(void*)*3);
if (v_borrow_3293_ == 0)
{
uint8_t v___x_3294_; 
v___x_3294_ = 1;
return v___x_3294_;
}
else
{
uint8_t v___x_3295_; 
v___x_3295_ = 0;
return v___x_3295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed(lean_object* v_ps_3296_, lean_object* v_i_3297_){
_start:
{
uint8_t v_res_3298_; lean_object* v_r_3299_; 
v_res_3298_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0(v_ps_3296_, v_i_3297_);
lean_dec(v_i_3297_);
lean_dec_ref(v_ps_3296_);
v_r_3299_ = lean_box(v_res_3298_);
return v_r_3299_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(lean_object* v_arg_3300_, lean_object* v_args_3301_, lean_object* v_ps_3302_){
_start:
{
lean_object* v___f_3303_; uint8_t v___x_3304_; 
v___f_3303_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3303_, 0, v_ps_3302_);
v___x_3304_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_arg_3300_, v_args_3301_, v___f_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___boxed(lean_object* v_arg_3305_, lean_object* v_args_3306_, lean_object* v_ps_3307_){
_start:
{
uint8_t v_res_3308_; lean_object* v_r_3309_; 
v_res_3308_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(v_arg_3305_, v_args_3306_, v_ps_3307_);
lean_dec_ref(v_args_3306_);
lean_dec(v_arg_3305_);
v_r_3309_ = lean_box(v_res_3308_);
return v_r_3309_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(lean_object* v_upperBound_3310_, lean_object* v_args_3311_, lean_object* v_arg_3312_, lean_object* v_consumeParamPred_3313_, lean_object* v_a_3314_, lean_object* v_b_3315_){
_start:
{
lean_object* v_a_3317_; uint8_t v___x_3321_; 
v___x_3321_ = lean_nat_dec_lt(v_a_3314_, v_upperBound_3310_);
if (v___x_3321_ == 0)
{
lean_dec(v_a_3314_);
lean_dec_ref(v_consumeParamPred_3313_);
return v_b_3315_;
}
else
{
lean_object* v___x_3322_; 
v___x_3322_ = lean_array_fget_borrowed(v_args_3311_, v_a_3314_);
if (lean_obj_tag(v___x_3322_) == 1)
{
lean_object* v_fvarId_3323_; uint8_t v___x_3324_; 
v_fvarId_3323_ = lean_ctor_get(v___x_3322_, 0);
v___x_3324_ = l_Lean_instBEqFVarId_beq(v_arg_3312_, v_fvarId_3323_);
if (v___x_3324_ == 0)
{
v_a_3317_ = v_b_3315_;
goto v___jp_3316_;
}
else
{
lean_object* v___x_3325_; uint8_t v___x_3326_; 
lean_inc_ref(v_consumeParamPred_3313_);
lean_inc(v_a_3314_);
v___x_3325_ = lean_apply_1(v_consumeParamPred_3313_, v_a_3314_);
v___x_3326_ = lean_unbox(v___x_3325_);
if (v___x_3326_ == 0)
{
v_a_3317_ = v_b_3315_;
goto v___jp_3316_;
}
else
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = lean_unsigned_to_nat(1u);
v___x_3328_ = lean_nat_add(v_b_3315_, v___x_3327_);
lean_dec(v_b_3315_);
v_a_3317_ = v___x_3328_;
goto v___jp_3316_;
}
}
}
else
{
v_a_3317_ = v_b_3315_;
goto v___jp_3316_;
}
}
v___jp_3316_:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = lean_unsigned_to_nat(1u);
v___x_3319_ = lean_nat_add(v_a_3314_, v___x_3318_);
lean_dec(v_a_3314_);
v_a_3314_ = v___x_3319_;
v_b_3315_ = v_a_3317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg___boxed(lean_object* v_upperBound_3329_, lean_object* v_args_3330_, lean_object* v_arg_3331_, lean_object* v_consumeParamPred_3332_, lean_object* v_a_3333_, lean_object* v_b_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v_upperBound_3329_, v_args_3330_, v_arg_3331_, v_consumeParamPred_3332_, v_a_3333_, v_b_3334_);
lean_dec(v_arg_3331_);
lean_dec_ref(v_args_3330_);
lean_dec(v_upperBound_3329_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(lean_object* v_arg_3336_, lean_object* v_args_3337_, lean_object* v_consumeParamPred_3338_){
_start:
{
lean_object* v_num_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v_num_3339_ = lean_unsigned_to_nat(0u);
v___x_3340_ = lean_array_get_size(v_args_3337_);
v___x_3341_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v___x_3340_, v_args_3337_, v_arg_3336_, v_consumeParamPred_3338_, v_num_3339_, v_num_3339_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions___boxed(lean_object* v_arg_3342_, lean_object* v_args_3343_, lean_object* v_consumeParamPred_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(v_arg_3342_, v_args_3343_, v_consumeParamPred_3344_);
lean_dec_ref(v_args_3343_);
lean_dec(v_arg_3342_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0(lean_object* v_upperBound_3346_, lean_object* v_args_3347_, lean_object* v_arg_3348_, lean_object* v_consumeParamPred_3349_, lean_object* v_inst_3350_, lean_object* v_R_3351_, lean_object* v_a_3352_, lean_object* v_b_3353_, lean_object* v_c_3354_){
_start:
{
lean_object* v___x_3355_; 
v___x_3355_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___redArg(v_upperBound_3346_, v_args_3347_, v_arg_3348_, v_consumeParamPred_3349_, v_a_3352_, v_b_3353_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0___boxed(lean_object* v_upperBound_3356_, lean_object* v_args_3357_, lean_object* v_arg_3358_, lean_object* v_consumeParamPred_3359_, lean_object* v_inst_3360_, lean_object* v_R_3361_, lean_object* v_a_3362_, lean_object* v_b_3363_, lean_object* v_c_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions_spec__0(v_upperBound_3356_, v_args_3357_, v_arg_3358_, v_consumeParamPred_3359_, v_inst_3360_, v_R_3361_, v_a_3362_, v_b_3363_, v_c_3364_);
lean_dec(v_arg_3358_);
lean_dec_ref(v_args_3357_);
lean_dec(v_upperBound_3356_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(lean_object* v_fvarId_3366_, lean_object* v_b_3367_, uint8_t v___x_3368_, lean_object* v_numIncs_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_a_3378_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = lean_nat_dec_eq(v_numIncs_3369_, v___x_3381_);
if (v___x_3382_ == 0)
{
lean_object* v_varMap_3383_; lean_object* v___x_3384_; uint8_t v_isDefiniteRef_3385_; uint8_t v_persistent_3386_; uint8_t v___y_3388_; 
v_varMap_3383_ = lean_ctor_get(v___y_3370_, 3);
v___x_3384_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3383_, v_fvarId_3366_);
v_isDefiniteRef_3385_ = lean_ctor_get_uint8(v___x_3384_, sizeof(void*)*2 + 1);
v_persistent_3386_ = lean_ctor_get_uint8(v___x_3384_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_3384_);
if (v_isDefiniteRef_3385_ == 0)
{
v___y_3388_ = v___x_3368_;
goto v___jp_3387_;
}
else
{
v___y_3388_ = v___x_3382_;
goto v___jp_3387_;
}
v___jp_3387_:
{
lean_object* v___x_3389_; 
v___x_3389_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_3389_, 0, v_fvarId_3366_);
lean_ctor_set(v___x_3389_, 1, v_numIncs_3369_);
lean_ctor_set(v___x_3389_, 2, v_b_3367_);
lean_ctor_set_uint8(v___x_3389_, sizeof(void*)*3, v___y_3388_);
lean_ctor_set_uint8(v___x_3389_, sizeof(void*)*3 + 1, v_persistent_3386_);
v_a_3378_ = v___x_3389_;
goto v___jp_3377_;
}
}
else
{
lean_dec(v_numIncs_3369_);
lean_dec(v_fvarId_3366_);
v_a_3378_ = v_b_3367_;
goto v___jp_3377_;
}
v___jp_3377_:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3379_, 0, v_a_3378_);
v___x_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
return v___x_3380_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0___boxed(lean_object* v_fvarId_3390_, lean_object* v_b_3391_, lean_object* v___x_3392_, lean_object* v_numIncs_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
uint8_t v___x_7166__boxed_3401_; lean_object* v_res_3402_; 
v___x_7166__boxed_3401_ = lean_unbox(v___x_3392_);
v_res_3402_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3390_, v_b_3391_, v___x_7166__boxed_3401_, v_numIncs_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(lean_object* v_upperBound_3403_, lean_object* v_args_3404_, lean_object* v_consumeParamPred_3405_, lean_object* v_a_3406_, lean_object* v_b_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v_a_3416_; lean_object* v___y_3421_; uint8_t v___x_3440_; 
v___x_3440_ = lean_nat_dec_lt(v_a_3406_, v_upperBound_3403_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; 
lean_dec(v_a_3406_);
lean_dec_ref(v_consumeParamPred_3405_);
v___x_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3441_, 0, v_b_3407_);
return v___x_3441_;
}
else
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_array_fget_borrowed(v_args_3404_, v_a_3406_);
if (lean_obj_tag(v___x_3442_) == 1)
{
lean_object* v_fvarId_3443_; lean_object* v_varMap_3444_; lean_object* v___x_3445_; uint8_t v_isPossibleRef_3446_; 
v_fvarId_3443_ = lean_ctor_get(v___x_3442_, 0);
v_varMap_3444_ = lean_ctor_get(v___y_3408_, 3);
v___x_3445_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3444_, v_fvarId_3443_);
v_isPossibleRef_3446_ = lean_ctor_get_uint8(v___x_3445_, sizeof(void*)*2);
lean_dec_ref(v___x_3445_);
if (v_isPossibleRef_3446_ == 0)
{
v_a_3416_ = v_b_3407_;
goto v___jp_3415_;
}
else
{
uint8_t v___x_3447_; 
lean_inc(v_a_3406_);
v___x_3447_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3404_, v_a_3406_);
if (v___x_3447_ == 0)
{
v_a_3416_ = v_b_3407_;
goto v___jp_3415_;
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v_vars_3450_; uint8_t v___x_3451_; lean_object* v___x_3452_; 
lean_inc_ref(v_consumeParamPred_3405_);
v___x_3448_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_getNumConsumptions(v_fvarId_3443_, v_args_3404_, v_consumeParamPred_3405_);
v___x_3449_ = lean_st_ref_get(v___y_3409_);
v_vars_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc_ref(v_vars_3450_);
lean_dec(v___x_3449_);
v___x_3451_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_3450_, v_fvarId_3443_);
lean_dec_ref(v_vars_3450_);
v___x_3452_ = lean_st_ref_get(v___y_3409_);
if (v___x_3451_ == 0)
{
lean_object* v_borrows_3455_; uint8_t v___x_3456_; 
v_borrows_3455_ = lean_ctor_get(v___x_3452_, 1);
lean_inc_ref(v_borrows_3455_);
lean_dec(v___x_3452_);
v___x_3456_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_3455_, v_fvarId_3443_);
lean_dec_ref(v_borrows_3455_);
if (v___x_3456_ == 0)
{
uint8_t v___x_3457_; 
lean_inc_ref(v_consumeParamPred_3405_);
v___x_3457_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParamAux(v_fvarId_3443_, v_args_3404_, v_consumeParamPred_3405_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = lean_unsigned_to_nat(1u);
v___x_3459_ = lean_nat_sub(v___x_3448_, v___x_3458_);
lean_dec(v___x_3448_);
lean_inc(v_fvarId_3443_);
v___x_3460_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3443_, v_b_3407_, v___x_3440_, v___x_3459_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
v___y_3421_ = v___x_3460_;
goto v___jp_3420_;
}
else
{
goto v___jp_3453_;
}
}
else
{
goto v___jp_3453_;
}
}
else
{
lean_dec(v___x_3452_);
goto v___jp_3453_;
}
v___jp_3453_:
{
lean_object* v___x_3454_; 
lean_inc(v_fvarId_3443_);
v___x_3454_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___lam__0(v_fvarId_3443_, v_b_3407_, v___x_3440_, v___x_3448_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
v___y_3421_ = v___x_3454_;
goto v___jp_3420_;
}
}
}
}
else
{
v_a_3416_ = v_b_3407_;
goto v___jp_3415_;
}
}
v___jp_3415_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = lean_unsigned_to_nat(1u);
v___x_3418_ = lean_nat_add(v_a_3406_, v___x_3417_);
lean_dec(v_a_3406_);
v_a_3406_ = v___x_3418_;
v_b_3407_ = v_a_3416_;
goto _start;
}
v___jp_3420_:
{
if (lean_obj_tag(v___y_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3431_; 
v_a_3422_ = lean_ctor_get(v___y_3421_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___y_3421_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3424_ = v___y_3421_;
v_isShared_3425_ = v_isSharedCheck_3431_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___y_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3431_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
if (lean_obj_tag(v_a_3422_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3428_; 
lean_dec(v_a_3406_);
lean_dec_ref(v_consumeParamPred_3405_);
v_a_3426_ = lean_ctor_get(v_a_3422_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v_a_3422_, 1);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v_a_3426_);
v___x_3428_ = v___x_3424_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
else
{
lean_object* v_a_3430_; 
lean_del_object(v___x_3424_);
v_a_3430_ = lean_ctor_get(v_a_3422_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v_a_3422_, 1);
v_a_3416_ = v_a_3430_;
goto v___jp_3415_;
}
}
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_dec(v_a_3406_);
lean_dec_ref(v_consumeParamPred_3405_);
v_a_3432_ = lean_ctor_get(v___y_3421_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___y_3421_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___y_3421_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___y_3421_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg___boxed(lean_object* v_upperBound_3461_, lean_object* v_args_3462_, lean_object* v_consumeParamPred_3463_, lean_object* v_a_3464_, lean_object* v_b_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v_upperBound_3461_, v_args_3462_, v_consumeParamPred_3463_, v_a_3464_, v_b_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec_ref(v_args_3462_);
lean_dec(v_upperBound_3461_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(lean_object* v_args_3474_, lean_object* v_consumeParamPred_3475_, lean_object* v_k_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3484_ = lean_unsigned_to_nat(0u);
v___x_3485_ = lean_array_get_size(v_args_3474_);
v___x_3486_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v___x_3485_, v_args_3474_, v_consumeParamPred_3475_, v___x_3484_, v_k_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux___boxed(lean_object* v_args_3487_, lean_object* v_consumeParamPred_3488_, lean_object* v_k_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3487_, v_consumeParamPred_3488_, v_k_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
lean_dec(v_a_3493_);
lean_dec_ref(v_a_3492_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
lean_dec_ref(v_args_3487_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(lean_object* v_upperBound_3498_, lean_object* v_args_3499_, lean_object* v_consumeParamPred_3500_, lean_object* v_inst_3501_, lean_object* v_R_3502_, lean_object* v_a_3503_, lean_object* v_b_3504_, lean_object* v_c_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___redArg(v_upperBound_3498_, v_args_3499_, v_consumeParamPred_3500_, v_a_3503_, v_b_3504_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0___boxed(lean_object* v_upperBound_3514_, lean_object* v_args_3515_, lean_object* v_consumeParamPred_3516_, lean_object* v_inst_3517_, lean_object* v_R_3518_, lean_object* v_a_3519_, lean_object* v_b_3520_, lean_object* v_c_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux_spec__0(v_upperBound_3514_, v_args_3515_, v_consumeParamPred_3516_, v_inst_3517_, v_R_3518_, v_a_3519_, v_b_3520_, v_c_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec_ref(v_args_3515_);
lean_dec(v_upperBound_3514_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(lean_object* v_args_3530_, lean_object* v_ps_3531_, lean_object* v_k_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v___f_3540_; lean_object* v___x_3541_; 
v___f_3540_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3540_, 0, v_ps_3531_);
v___x_3541_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3530_, v___f_3540_, v_k_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore___boxed(lean_object* v_args_3542_, lean_object* v_ps_3543_, lean_object* v_k_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_3542_, v_ps_3543_, v_k_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
lean_dec_ref(v_args_3542_);
return v_res_3552_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(lean_object* v_x_3553_){
_start:
{
uint8_t v___x_3554_; 
v___x_3554_ = 1;
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0___boxed(lean_object* v_x_3555_){
_start:
{
uint8_t v_res_3556_; lean_object* v_r_3557_; 
v_res_3556_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___lam__0(v_x_3555_);
lean_dec(v_x_3555_);
v_r_3557_ = lean_box(v_res_3556_);
return v_r_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(lean_object* v_args_3559_, lean_object* v_k_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v___f_3568_; lean_object* v___x_3569_; 
v___f_3568_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___closed__0));
v___x_3569_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeAux(v_args_3559_, v___f_3568_, v_k_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll___boxed(lean_object* v_args_3570_, lean_object* v_k_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_3570_, v_k_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec_ref(v_args_3570_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(lean_object* v_upperBound_3580_, lean_object* v_args_3581_, lean_object* v_ps_3582_, lean_object* v_a_3583_, lean_object* v_b_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v_a_3589_; uint8_t v___x_3593_; 
v___x_3593_ = lean_nat_dec_lt(v_a_3583_, v_upperBound_3580_);
if (v___x_3593_ == 0)
{
lean_object* v___x_3594_; 
lean_dec(v_a_3583_);
lean_dec_ref(v_ps_3582_);
v___x_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3594_, 0, v_b_3584_);
return v___x_3594_;
}
else
{
lean_object* v___x_3595_; 
v___x_3595_ = lean_array_fget_borrowed(v_args_3581_, v_a_3583_);
if (lean_obj_tag(v___x_3595_) == 0)
{
v_a_3589_ = v_b_3584_;
goto v___jp_3588_;
}
else
{
lean_object* v_fvarId_3596_; lean_object* v_varMap_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v_vars_3600_; uint8_t v___x_3601_; lean_object* v___x_3602_; uint8_t v_isPossibleRef_3603_; 
v_fvarId_3596_ = lean_ctor_get(v___x_3595_, 0);
v_varMap_3597_ = lean_ctor_get(v___y_3585_, 3);
v___x_3598_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3597_, v_fvarId_3596_);
v___x_3599_ = lean_st_ref_get(v___y_3586_);
v_vars_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc_ref(v_vars_3600_);
lean_dec(v___x_3599_);
v___x_3601_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_3600_, v_fvarId_3596_);
lean_dec_ref(v_vars_3600_);
v___x_3602_ = lean_st_ref_get(v___y_3586_);
v_isPossibleRef_3603_ = lean_ctor_get_uint8(v___x_3598_, sizeof(void*)*2);
lean_dec_ref(v___x_3598_);
if (v_isPossibleRef_3603_ == 0)
{
lean_dec(v___x_3602_);
v_a_3589_ = v_b_3584_;
goto v___jp_3588_;
}
else
{
uint8_t v___x_3604_; 
lean_inc(v_a_3583_);
v___x_3604_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isFirstOcc(v_args_3581_, v_a_3583_);
if (v___x_3604_ == 0)
{
lean_dec(v___x_3602_);
v_a_3589_ = v_b_3584_;
goto v___jp_3588_;
}
else
{
uint8_t v___x_3605_; 
lean_inc_ref(v_ps_3582_);
v___x_3605_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_isBorrowParam(v_fvarId_3596_, v_args_3581_, v_ps_3582_);
if (v___x_3605_ == 0)
{
lean_dec(v___x_3602_);
v_a_3589_ = v_b_3584_;
goto v___jp_3588_;
}
else
{
if (v___x_3601_ == 0)
{
lean_object* v_borrows_3606_; uint8_t v___x_3607_; 
v_borrows_3606_ = lean_ctor_get(v___x_3602_, 1);
lean_inc_ref(v_borrows_3606_);
lean_dec(v___x_3602_);
v___x_3607_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_3606_, v_fvarId_3596_);
lean_dec_ref(v_borrows_3606_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; 
lean_inc(v_fvarId_3596_);
v___x_3608_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_3596_, v_b_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
v_a_3589_ = v_a_3609_;
goto v___jp_3588_;
}
else
{
lean_dec(v_a_3583_);
lean_dec_ref(v_ps_3582_);
return v___x_3608_;
}
}
else
{
v_a_3589_ = v_b_3584_;
goto v___jp_3588_;
}
}
else
{
lean_dec(v___x_3602_);
v_a_3589_ = v_b_3584_;
goto v___jp_3588_;
}
}
}
}
}
}
v___jp_3588_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = lean_unsigned_to_nat(1u);
v___x_3591_ = lean_nat_add(v_a_3583_, v___x_3590_);
lean_dec(v_a_3583_);
v_a_3583_ = v___x_3591_;
v_b_3584_ = v_a_3589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg___boxed(lean_object* v_upperBound_3610_, lean_object* v_args_3611_, lean_object* v_ps_3612_, lean_object* v_a_3613_, lean_object* v_b_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v_upperBound_3610_, v_args_3611_, v_ps_3612_, v_a_3613_, v_b_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v_args_3611_);
lean_dec(v_upperBound_3610_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(lean_object* v_args_3619_, lean_object* v_ps_3620_, lean_object* v_k_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = lean_array_get_size(v_args_3619_);
v___x_3631_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v___x_3630_, v_args_3619_, v_ps_3620_, v___x_3629_, v_k_3621_, v_a_3622_, v_a_3623_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp___boxed(lean_object* v_args_3632_, lean_object* v_ps_3633_, lean_object* v_k_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(v_args_3632_, v_ps_3633_, v_k_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
lean_dec(v_a_3640_);
lean_dec_ref(v_a_3639_);
lean_dec(v_a_3638_);
lean_dec_ref(v_a_3637_);
lean_dec(v_a_3636_);
lean_dec_ref(v_a_3635_);
lean_dec_ref(v_args_3632_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(lean_object* v_upperBound_3643_, lean_object* v_args_3644_, lean_object* v_ps_3645_, lean_object* v_inst_3646_, lean_object* v_R_3647_, lean_object* v_a_3648_, lean_object* v_b_3649_, lean_object* v_c_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v___x_3658_; 
v___x_3658_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___redArg(v_upperBound_3643_, v_args_3644_, v_ps_3645_, v_a_3648_, v_b_3649_, v___y_3651_, v___y_3652_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0___boxed(lean_object* v_upperBound_3659_, lean_object* v_args_3660_, lean_object* v_ps_3661_, lean_object* v_inst_3662_, lean_object* v_R_3663_, lean_object* v_a_3664_, lean_object* v_b_3665_, lean_object* v_c_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp_spec__0(v_upperBound_3659_, v_args_3660_, v_ps_3661_, v_inst_3662_, v_R_3663_, v_a_3664_, v_b_3665_, v_c_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec_ref(v_args_3660_);
lean_dec(v_upperBound_3659_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(lean_object* v_fvarId_3675_, lean_object* v_k_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v_varMap_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v_borrows_3683_; uint8_t v___x_3684_; lean_object* v___x_3685_; uint8_t v_isPossibleRef_3686_; 
v_varMap_3680_ = lean_ctor_get(v_a_3677_, 3);
v___x_3681_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_3680_, v_fvarId_3675_);
v___x_3682_ = lean_st_ref_get(v_a_3678_);
v_borrows_3683_ = lean_ctor_get(v___x_3682_, 1);
lean_inc_ref(v_borrows_3683_);
lean_dec(v___x_3682_);
v___x_3684_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_3683_, v_fvarId_3675_);
lean_dec_ref(v_borrows_3683_);
v___x_3685_ = lean_st_ref_get(v_a_3678_);
v_isPossibleRef_3686_ = lean_ctor_get_uint8(v___x_3681_, sizeof(void*)*2);
lean_dec_ref(v___x_3681_);
if (v_isPossibleRef_3686_ == 0)
{
lean_object* v___x_3687_; 
lean_dec(v___x_3685_);
lean_dec(v_fvarId_3675_);
v___x_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3687_, 0, v_k_3676_);
return v___x_3687_;
}
else
{
if (v___x_3684_ == 0)
{
lean_object* v_vars_3688_; uint8_t v___x_3689_; 
v_vars_3688_ = lean_ctor_get(v___x_3685_, 0);
lean_inc_ref(v_vars_3688_);
lean_dec(v___x_3685_);
v___x_3689_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_vars_3688_, v_fvarId_3675_);
lean_dec_ref(v_vars_3688_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; 
v___x_3690_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec___redArg(v_fvarId_3675_, v_k_3676_, v_a_3677_);
return v___x_3690_;
}
else
{
lean_object* v___x_3691_; 
lean_dec(v_fvarId_3675_);
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v_k_3676_);
return v___x_3691_;
}
}
else
{
lean_object* v___x_3692_; 
lean_dec(v___x_3685_);
lean_dec(v_fvarId_3675_);
v___x_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3692_, 0, v_k_3676_);
return v___x_3692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg___boxed(lean_object* v_fvarId_3693_, lean_object* v_k_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3693_, v_k_3694_, v_a_3695_, v_a_3696_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(lean_object* v_fvarId_3699_, lean_object* v_k_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3699_, v_k_3700_, v_a_3701_, v_a_3702_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___boxed(lean_object* v_fvarId_3709_, lean_object* v_k_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded(v_fvarId_3709_, v_k_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_);
lean_dec(v_a_3716_);
lean_dec_ref(v_a_3715_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(lean_object* v_a_3719_, lean_object* v_x_3720_){
_start:
{
if (lean_obj_tag(v_x_3720_) == 0)
{
return v_x_3720_;
}
else
{
lean_object* v_key_3721_; lean_object* v_value_3722_; lean_object* v_tail_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3732_; 
v_key_3721_ = lean_ctor_get(v_x_3720_, 0);
v_value_3722_ = lean_ctor_get(v_x_3720_, 1);
v_tail_3723_ = lean_ctor_get(v_x_3720_, 2);
v_isSharedCheck_3732_ = !lean_is_exclusive(v_x_3720_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3725_ = v_x_3720_;
v_isShared_3726_ = v_isSharedCheck_3732_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_tail_3723_);
lean_inc(v_value_3722_);
lean_inc(v_key_3721_);
lean_dec(v_x_3720_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3732_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
uint8_t v___x_3727_; 
v___x_3727_ = l_Lean_instBEqFVarId_beq(v_key_3721_, v_a_3719_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; lean_object* v___x_3730_; 
v___x_3728_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3719_, v_tail_3723_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 2, v___x_3728_);
v___x_3730_ = v___x_3725_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_key_3721_);
lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_value_3722_);
lean_ctor_set(v_reuseFailAlloc_3731_, 2, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
else
{
lean_del_object(v___x_3725_);
lean_dec(v_value_3722_);
lean_dec(v_key_3721_);
return v_tail_3723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg___boxed(lean_object* v_a_3733_, lean_object* v_x_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3733_, v_x_3734_);
lean_dec(v_a_3733_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(lean_object* v_m_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v_size_3738_; lean_object* v_buckets_3739_; lean_object* v___x_3740_; uint64_t v___x_3741_; uint64_t v___x_3742_; uint64_t v___x_3743_; uint64_t v_fold_3744_; uint64_t v___x_3745_; uint64_t v___x_3746_; uint64_t v___x_3747_; size_t v___x_3748_; size_t v___x_3749_; size_t v___x_3750_; size_t v___x_3751_; size_t v___x_3752_; lean_object* v_bkt_3753_; uint8_t v___x_3754_; 
v_size_3738_ = lean_ctor_get(v_m_3736_, 0);
v_buckets_3739_ = lean_ctor_get(v_m_3736_, 1);
v___x_3740_ = lean_array_get_size(v_buckets_3739_);
v___x_3741_ = l_Lean_instHashableFVarId_hash(v_a_3737_);
v___x_3742_ = 32ULL;
v___x_3743_ = lean_uint64_shift_right(v___x_3741_, v___x_3742_);
v_fold_3744_ = lean_uint64_xor(v___x_3741_, v___x_3743_);
v___x_3745_ = 16ULL;
v___x_3746_ = lean_uint64_shift_right(v_fold_3744_, v___x_3745_);
v___x_3747_ = lean_uint64_xor(v_fold_3744_, v___x_3746_);
v___x_3748_ = lean_uint64_to_usize(v___x_3747_);
v___x_3749_ = lean_usize_of_nat(v___x_3740_);
v___x_3750_ = ((size_t)1ULL);
v___x_3751_ = lean_usize_sub(v___x_3749_, v___x_3750_);
v___x_3752_ = lean_usize_land(v___x_3748_, v___x_3751_);
v_bkt_3753_ = lean_array_uget_borrowed(v_buckets_3739_, v___x_3752_);
v___x_3754_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_3737_, v_bkt_3753_);
if (v___x_3754_ == 0)
{
return v_m_3736_;
}
else
{
lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3767_; 
lean_inc(v_bkt_3753_);
lean_inc_ref(v_buckets_3739_);
lean_inc(v_size_3738_);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_m_3736_);
if (v_isSharedCheck_3767_ == 0)
{
lean_object* v_unused_3768_; lean_object* v_unused_3769_; 
v_unused_3768_ = lean_ctor_get(v_m_3736_, 1);
lean_dec(v_unused_3768_);
v_unused_3769_ = lean_ctor_get(v_m_3736_, 0);
lean_dec(v_unused_3769_);
v___x_3756_ = v_m_3736_;
v_isShared_3757_ = v_isSharedCheck_3767_;
goto v_resetjp_3755_;
}
else
{
lean_dec(v_m_3736_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3767_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3758_; lean_object* v_buckets_x27_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3765_; 
v___x_3758_ = lean_box(0);
v_buckets_x27_3759_ = lean_array_uset(v_buckets_3739_, v___x_3752_, v___x_3758_);
v___x_3760_ = lean_unsigned_to_nat(1u);
v___x_3761_ = lean_nat_sub(v_size_3738_, v___x_3760_);
lean_dec(v_size_3738_);
v___x_3762_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3737_, v_bkt_3753_);
v___x_3763_ = lean_array_uset(v_buckets_x27_3759_, v___x_3752_, v___x_3762_);
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 1, v___x_3763_);
lean_ctor_set(v___x_3756_, 0, v___x_3761_);
v___x_3765_ = v___x_3756_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3761_);
lean_ctor_set(v_reuseFailAlloc_3766_, 1, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg___boxed(lean_object* v_m_3770_, lean_object* v_a_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_m_3770_, v_a_3771_);
lean_dec(v_a_3771_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(lean_object* v_as_3773_, size_t v_i_3774_, size_t v_stop_3775_, lean_object* v_b_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
uint8_t v___x_3780_; 
v___x_3780_ = lean_usize_dec_eq(v_i_3774_, v_stop_3775_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; lean_object* v_fvarId_3782_; lean_object* v___x_3783_; 
v___x_3781_ = lean_array_uget_borrowed(v_as_3773_, v_i_3774_);
v_fvarId_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_fvarId_3782_);
v___x_3783_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_3782_, v_b_3776_, v___y_3777_, v___y_3778_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3785_; lean_object* v_vars_3786_; lean_object* v_borrows_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3800_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v___x_3783_, 1);
v___x_3785_ = lean_st_ref_take(v___y_3778_);
v_vars_3786_ = lean_ctor_get(v___x_3785_, 0);
v_borrows_3787_ = lean_ctor_get(v___x_3785_, 1);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3789_ = v___x_3785_;
v_isShared_3790_ = v_isSharedCheck_3800_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_borrows_3787_);
lean_inc(v_vars_3786_);
lean_dec(v___x_3785_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3800_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v_vars_3791_; lean_object* v_borrows_3792_; lean_object* v___x_3794_; 
v_vars_3791_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_vars_3786_, v_fvarId_3782_);
v_borrows_3792_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_borrows_3787_, v_fvarId_3782_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 1, v_borrows_3792_);
lean_ctor_set(v___x_3789_, 0, v_vars_3791_);
v___x_3794_ = v___x_3789_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_vars_3791_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_borrows_3792_);
v___x_3794_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3795_; size_t v___x_3796_; size_t v___x_3797_; 
v___x_3795_ = lean_st_ref_put(v___y_3778_, v___x_3794_);
v___x_3796_ = ((size_t)1ULL);
v___x_3797_ = lean_usize_add(v_i_3774_, v___x_3796_);
v_i_3774_ = v___x_3797_;
v_b_3776_ = v_a_3784_;
goto _start;
}
}
}
else
{
return v___x_3783_;
}
}
else
{
lean_object* v___x_3801_; 
v___x_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3801_, 0, v_b_3776_);
return v___x_3801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg___boxed(lean_object* v_as_3802_, lean_object* v_i_3803_, lean_object* v_stop_3804_, lean_object* v_b_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
size_t v_i_boxed_3809_; size_t v_stop_boxed_3810_; lean_object* v_res_3811_; 
v_i_boxed_3809_ = lean_unbox_usize(v_i_3803_);
lean_dec(v_i_3803_);
v_stop_boxed_3810_ = lean_unbox_usize(v_stop_3804_);
lean_dec(v_stop_3804_);
v_res_3811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_as_3802_, v_i_boxed_3809_, v_stop_boxed_3810_, v_b_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec_ref(v_as_3802_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(lean_object* v_ps_3812_, lean_object* v_k_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v___x_3821_ = lean_unsigned_to_nat(0u);
v___x_3822_ = lean_array_get_size(v_ps_3812_);
v___x_3823_ = lean_nat_dec_lt(v___x_3821_, v___x_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3824_, 0, v_k_3813_);
return v___x_3824_;
}
else
{
size_t v___x_3825_; size_t v___x_3826_; lean_object* v___x_3827_; 
v___x_3825_ = ((size_t)0ULL);
v___x_3826_ = lean_usize_of_nat(v___x_3822_);
v___x_3827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_ps_3812_, v___x_3825_, v___x_3826_, v_k_3813_, v_a_3814_, v_a_3815_);
return v___x_3827_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams___boxed(lean_object* v_ps_3828_, lean_object* v_k_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_ps_3828_, v_k_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
lean_dec_ref(v_ps_3828_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(lean_object* v_00_u03b2_3838_, lean_object* v_m_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_m_3839_, v_a_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___boxed(lean_object* v_00_u03b2_3842_, lean_object* v_m_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0(v_00_u03b2_3842_, v_m_3843_, v_a_3844_);
lean_dec(v_a_3844_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1(lean_object* v_as_3846_, size_t v_i_3847_, size_t v_stop_3848_, lean_object* v_b_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___redArg(v_as_3846_, v_i_3847_, v_stop_3848_, v_b_3849_, v___y_3850_, v___y_3851_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1___boxed(lean_object* v_as_3858_, lean_object* v_i_3859_, lean_object* v_stop_3860_, lean_object* v_b_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
size_t v_i_boxed_3869_; size_t v_stop_boxed_3870_; lean_object* v_res_3871_; 
v_i_boxed_3869_ = lean_unbox_usize(v_i_3859_);
lean_dec(v_i_3859_);
v_stop_boxed_3870_ = lean_unbox_usize(v_stop_3860_);
lean_dec(v_stop_3860_);
v_res_3871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__1(v_as_3858_, v_i_boxed_3869_, v_stop_boxed_3870_, v_b_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec_ref(v_as_3858_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0(lean_object* v_00_u03b2_3872_, lean_object* v_a_3873_, lean_object* v_x_3874_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___redArg(v_a_3873_, v_x_3874_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3876_, lean_object* v_a_3877_, lean_object* v_x_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0_spec__0(v_00_u03b2_3876_, v_a_3877_, v_x_3878_);
lean_dec(v_a_3877_);
return v_res_3879_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(lean_object* v_msg_3881_){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0);
v___x_3883_ = lean_panic_fn_borrowed(v___x_3882_, v_msg_3881_);
return v___x_3883_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default___redArg();
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1(lean_object* v_msg_3885_){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1___closed__0);
v___x_3887_ = lean_panic_fn_borrowed(v___x_3886_, v_msg_3885_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(lean_object* v_msg_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v_toApplicative_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3961_; 
v___x_3896_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__0);
v___x_3897_ = l_StateRefT_x27_instMonad___redArg(v___x_3896_);
v_toApplicative_3898_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3961_ == 0)
{
lean_object* v_unused_3962_; 
v_unused_3962_ = lean_ctor_get(v___x_3897_, 1);
lean_dec(v_unused_3962_);
v___x_3900_ = v___x_3897_;
v_isShared_3901_ = v_isSharedCheck_3961_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_toApplicative_3898_);
lean_dec(v___x_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3961_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v_toFunctor_3902_; lean_object* v_toSeq_3903_; lean_object* v_toSeqLeft_3904_; lean_object* v_toSeqRight_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3959_; 
v_toFunctor_3902_ = lean_ctor_get(v_toApplicative_3898_, 0);
v_toSeq_3903_ = lean_ctor_get(v_toApplicative_3898_, 2);
v_toSeqLeft_3904_ = lean_ctor_get(v_toApplicative_3898_, 3);
v_toSeqRight_3905_ = lean_ctor_get(v_toApplicative_3898_, 4);
v_isSharedCheck_3959_ = !lean_is_exclusive(v_toApplicative_3898_);
if (v_isSharedCheck_3959_ == 0)
{
lean_object* v_unused_3960_; 
v_unused_3960_ = lean_ctor_get(v_toApplicative_3898_, 1);
lean_dec(v_unused_3960_);
v___x_3907_ = v_toApplicative_3898_;
v_isShared_3908_ = v_isSharedCheck_3959_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_toSeqRight_3905_);
lean_inc(v_toSeqLeft_3904_);
lean_inc(v_toSeq_3903_);
lean_inc(v_toFunctor_3902_);
lean_dec(v_toApplicative_3898_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3959_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___f_3909_; lean_object* v___f_3910_; lean_object* v___f_3911_; lean_object* v___f_3912_; lean_object* v___x_3913_; lean_object* v___f_3914_; lean_object* v___f_3915_; lean_object* v___f_3916_; lean_object* v___x_3918_; 
v___f_3909_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__1));
v___f_3910_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__2));
lean_inc_ref(v_toFunctor_3902_);
v___f_3911_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3911_, 0, v_toFunctor_3902_);
v___f_3912_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3912_, 0, v_toFunctor_3902_);
v___x_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___f_3911_);
lean_ctor_set(v___x_3913_, 1, v___f_3912_);
v___f_3914_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3914_, 0, v_toSeqRight_3905_);
v___f_3915_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3915_, 0, v_toSeqLeft_3904_);
v___f_3916_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3916_, 0, v_toSeq_3903_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 4, v___f_3914_);
lean_ctor_set(v___x_3907_, 3, v___f_3915_);
lean_ctor_set(v___x_3907_, 2, v___f_3916_);
lean_ctor_set(v___x_3907_, 1, v___f_3909_);
lean_ctor_set(v___x_3907_, 0, v___x_3913_);
v___x_3918_ = v___x_3907_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3913_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v___f_3909_);
lean_ctor_set(v_reuseFailAlloc_3958_, 2, v___f_3916_);
lean_ctor_set(v_reuseFailAlloc_3958_, 3, v___f_3915_);
lean_ctor_set(v_reuseFailAlloc_3958_, 4, v___f_3914_);
v___x_3918_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
lean_object* v___x_3920_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 1, v___f_3910_);
lean_ctor_set(v___x_3900_, 0, v___x_3918_);
v___x_3920_ = v___x_3900_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v___f_3910_);
v___x_3920_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3921_; lean_object* v_toApplicative_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3955_; 
v___x_3921_ = l_StateRefT_x27_instMonad___redArg(v___x_3920_);
v_toApplicative_3922_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3955_ == 0)
{
lean_object* v_unused_3956_; 
v_unused_3956_ = lean_ctor_get(v___x_3921_, 1);
lean_dec(v_unused_3956_);
v___x_3924_ = v___x_3921_;
v_isShared_3925_ = v_isSharedCheck_3955_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_toApplicative_3922_);
lean_dec(v___x_3921_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3955_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v_toFunctor_3926_; lean_object* v_toSeq_3927_; lean_object* v_toSeqLeft_3928_; lean_object* v_toSeqRight_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3953_; 
v_toFunctor_3926_ = lean_ctor_get(v_toApplicative_3922_, 0);
v_toSeq_3927_ = lean_ctor_get(v_toApplicative_3922_, 2);
v_toSeqLeft_3928_ = lean_ctor_get(v_toApplicative_3922_, 3);
v_toSeqRight_3929_ = lean_ctor_get(v_toApplicative_3922_, 4);
v_isSharedCheck_3953_ = !lean_is_exclusive(v_toApplicative_3922_);
if (v_isSharedCheck_3953_ == 0)
{
lean_object* v_unused_3954_; 
v_unused_3954_ = lean_ctor_get(v_toApplicative_3922_, 1);
lean_dec(v_unused_3954_);
v___x_3931_ = v_toApplicative_3922_;
v_isShared_3932_ = v_isSharedCheck_3953_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_toSeqRight_3929_);
lean_inc(v_toSeqLeft_3928_);
lean_inc(v_toSeq_3927_);
lean_inc(v_toFunctor_3926_);
lean_dec(v_toApplicative_3922_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3953_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___f_3933_; lean_object* v___f_3934_; lean_object* v___f_3935_; lean_object* v___f_3936_; lean_object* v___x_3937_; lean_object* v___f_3938_; lean_object* v___f_3939_; lean_object* v___f_3940_; lean_object* v___x_3942_; 
v___f_3933_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__3));
v___f_3934_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__1___closed__4));
lean_inc_ref(v_toFunctor_3926_);
v___f_3935_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3935_, 0, v_toFunctor_3926_);
v___f_3936_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3936_, 0, v_toFunctor_3926_);
v___x_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___f_3935_);
lean_ctor_set(v___x_3937_, 1, v___f_3936_);
v___f_3938_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3938_, 0, v_toSeqRight_3929_);
v___f_3939_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3939_, 0, v_toSeqLeft_3928_);
v___f_3940_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3940_, 0, v_toSeq_3927_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 4, v___f_3938_);
lean_ctor_set(v___x_3931_, 3, v___f_3939_);
lean_ctor_set(v___x_3931_, 2, v___f_3940_);
lean_ctor_set(v___x_3931_, 1, v___f_3933_);
lean_ctor_set(v___x_3931_, 0, v___x_3937_);
v___x_3942_ = v___x_3931_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3952_, 1, v___f_3933_);
lean_ctor_set(v_reuseFailAlloc_3952_, 2, v___f_3940_);
lean_ctor_set(v_reuseFailAlloc_3952_, 3, v___f_3939_);
lean_ctor_set(v_reuseFailAlloc_3952_, 4, v___f_3938_);
v___x_3942_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3944_; 
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 1, v___f_3934_);
lean_ctor_set(v___x_3924_, 0, v___x_3942_);
v___x_3944_ = v___x_3924_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_3951_, 1, v___f_3934_);
v___x_3944_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___f_3948_; lean_object* v___x_15568__overap_3949_; lean_object* v___x_3950_; 
v___x_3945_ = l_StateRefT_x27_instMonad___redArg(v___x_3944_);
v___x_3946_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0___closed__0);
v___x_3947_ = l_instInhabitedOfMonad___redArg(v___x_3945_, v___x_3946_);
v___f_3948_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3948_, 0, v___x_3947_);
v___x_15568__overap_3949_ = lean_panic_fn_borrowed(v___f_3948_, v_msg_3888_);
lean_dec_ref(v___f_3948_);
lean_inc(v___y_3894_);
lean_inc_ref(v___y_3893_);
lean_inc(v___y_3892_);
lean_inc_ref(v___y_3891_);
lean_inc(v___y_3890_);
lean_inc_ref(v___y_3889_);
v___x_3950_ = lean_apply_7(v___x_15568__overap_3949_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, lean_box(0));
return v___x_3950_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2___boxed(lean_object* v_msg_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v_msg_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
return v_res_3971_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2(void){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3974_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_3975_ = lean_unsigned_to_nat(9u);
v___x_3976_ = lean_unsigned_to_nat(625u);
v___x_3977_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__1));
v___x_3978_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__0));
v___x_3979_ = l_mkPanicMessageWithDecl(v___x_3978_, v___x_3977_, v___x_3976_, v___x_3975_, v___x_3974_);
return v___x_3979_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11(void){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3992_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__10));
v___x_3993_ = lean_unsigned_to_nat(14u);
v___x_3994_ = lean_unsigned_to_nat(22u);
v___x_3995_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__9));
v___x_3996_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__8));
v___x_3997_ = l_mkPanicMessageWithDecl(v___x_3996_, v___x_3995_, v___x_3994_, v___x_3993_, v___x_3992_);
return v___x_3997_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__13(void){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_3999_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_4000_ = lean_unsigned_to_nat(22u);
v___x_4001_ = lean_unsigned_to_nat(575u);
v___x_4002_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__12));
v___x_4003_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_4004_ = l_mkPanicMessageWithDecl(v___x_4003_, v___x_4002_, v___x_4001_, v___x_4000_, v___x_3999_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(lean_object* v_code_4005_, lean_object* v_decl_4006_, lean_object* v_k_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v_fvarId_4015_; lean_object* v_value_4016_; lean_object* v_k_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v_k_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___x_4091_; 
v_fvarId_4015_ = lean_ctor_get(v_decl_4006_, 0);
lean_inc_n(v_fvarId_4015_, 2);
v_value_4016_ = lean_ctor_get(v_decl_4006_, 3);
lean_inc(v_value_4016_);
v___x_4091_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_4015_, v_k_4007_, v_a_4008_, v_a_4009_);
switch(lean_obj_tag(v_value_4016_))
{
case 4:
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4134_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4094_ = v___x_4091_;
v_isShared_4095_ = v_isSharedCheck_4134_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4091_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4134_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v_fvarId_4096_; lean_object* v_args_4097_; lean_object* v___x_4099_; 
v_fvarId_4096_ = lean_ctor_get(v_value_4016_, 0);
v_args_4097_ = lean_ctor_get(v_value_4016_, 1);
lean_inc(v_fvarId_4096_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set_tag(v___x_4094_, 1);
lean_ctor_set(v___x_4094_, 0, v_fvarId_4096_);
v___x_4099_ = v___x_4094_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_fvarId_4096_);
v___x_4099_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
lean_object* v___x_4100_; lean_object* v___y_4102_; 
lean_inc_ref(v_args_4097_);
v___x_4100_ = lean_array_push(v_args_4097_, v___x_4099_);
if (lean_obj_tag(v_code_4005_) == 0)
{
lean_object* v_decl_4105_; lean_object* v_k_4106_; size_t v___x_4107_; size_t v___x_4108_; uint8_t v___x_4109_; 
v_decl_4105_ = lean_ctor_get(v_code_4005_, 0);
v_k_4106_ = lean_ctor_get(v_code_4005_, 1);
v___x_4107_ = lean_ptr_addr(v_k_4106_);
v___x_4108_ = lean_ptr_addr(v_a_4092_);
v___x_4109_ = lean_usize_dec_eq(v___x_4107_, v___x_4108_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
v_isSharedCheck_4116_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4116_ == 0)
{
lean_object* v_unused_4117_; lean_object* v_unused_4118_; 
v_unused_4117_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4117_);
v_unused_4118_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4118_);
v___x_4111_ = v_code_4005_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_dec(v_code_4005_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 1, v_a_4092_);
lean_ctor_set(v___x_4111_, 0, v_decl_4006_);
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4115_, 1, v_a_4092_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
v___y_4102_ = v___x_4114_;
goto v___jp_4101_;
}
}
}
else
{
size_t v___x_4119_; size_t v___x_4120_; uint8_t v___x_4121_; 
v___x_4119_ = lean_ptr_addr(v_decl_4105_);
v___x_4120_ = lean_ptr_addr(v_decl_4006_);
v___x_4121_ = lean_usize_dec_eq(v___x_4119_, v___x_4120_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4128_; 
v_isSharedCheck_4128_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4128_ == 0)
{
lean_object* v_unused_4129_; lean_object* v_unused_4130_; 
v_unused_4129_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4129_);
v_unused_4130_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4130_);
v___x_4123_ = v_code_4005_;
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
else
{
lean_dec(v_code_4005_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4126_; 
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 1, v_a_4092_);
lean_ctor_set(v___x_4123_, 0, v_decl_4006_);
v___x_4126_ = v___x_4123_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v_a_4092_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
v___y_4102_ = v___x_4126_;
goto v___jp_4101_;
}
}
}
else
{
lean_dec(v_a_4092_);
lean_dec_ref(v_decl_4006_);
v___y_4102_ = v_code_4005_;
goto v___jp_4101_;
}
}
}
else
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
lean_dec(v_a_4092_);
lean_dec_ref(v_decl_4006_);
lean_dec_ref(v_code_4005_);
v___x_4131_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4132_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4131_);
v___y_4102_ = v___x_4132_;
goto v___jp_4101_;
}
v___jp_4101_:
{
lean_object* v___x_4103_; 
v___x_4103_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v___x_4100_, v___y_4102_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
lean_dec_ref(v___x_4100_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_a_4104_);
lean_dec_ref_known(v___x_4103_, 1);
v_k_4018_ = v_a_4104_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
else
{
lean_dec_ref_known(v_value_4016_, 2);
lean_dec(v_fvarId_4015_);
return v___x_4103_;
}
}
}
}
}
case 5:
{
lean_object* v_a_4135_; lean_object* v_args_4136_; lean_object* v___y_4138_; 
v_a_4135_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4135_);
lean_dec_ref(v___x_4091_);
v_args_4136_ = lean_ctor_get(v_value_4016_, 1);
if (lean_obj_tag(v_code_4005_) == 0)
{
lean_object* v_decl_4141_; lean_object* v_k_4142_; size_t v___x_4143_; size_t v___x_4144_; uint8_t v___x_4145_; 
v_decl_4141_ = lean_ctor_get(v_code_4005_, 0);
v_k_4142_ = lean_ctor_get(v_code_4005_, 1);
v___x_4143_ = lean_ptr_addr(v_k_4142_);
v___x_4144_ = lean_ptr_addr(v_a_4135_);
v___x_4145_ = lean_usize_dec_eq(v___x_4143_, v___x_4144_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
v_isSharedCheck_4152_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4152_ == 0)
{
lean_object* v_unused_4153_; lean_object* v_unused_4154_; 
v_unused_4153_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4153_);
v_unused_4154_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4154_);
v___x_4147_ = v_code_4005_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_dec(v_code_4005_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 1, v_a_4135_);
lean_ctor_set(v___x_4147_, 0, v_decl_4006_);
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4151_, 1, v_a_4135_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
v___y_4138_ = v___x_4150_;
goto v___jp_4137_;
}
}
}
else
{
size_t v___x_4155_; size_t v___x_4156_; uint8_t v___x_4157_; 
v___x_4155_ = lean_ptr_addr(v_decl_4141_);
v___x_4156_ = lean_ptr_addr(v_decl_4006_);
v___x_4157_ = lean_usize_dec_eq(v___x_4155_, v___x_4156_);
if (v___x_4157_ == 0)
{
lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
v_isSharedCheck_4164_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4164_ == 0)
{
lean_object* v_unused_4165_; lean_object* v_unused_4166_; 
v_unused_4165_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4165_);
v_unused_4166_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4166_);
v___x_4159_ = v_code_4005_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_dec(v_code_4005_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 1, v_a_4135_);
lean_ctor_set(v___x_4159_, 0, v_decl_4006_);
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4163_, 1, v_a_4135_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
v___y_4138_ = v___x_4162_;
goto v___jp_4137_;
}
}
}
else
{
lean_dec(v_a_4135_);
lean_dec_ref(v_decl_4006_);
v___y_4138_ = v_code_4005_;
goto v___jp_4137_;
}
}
}
else
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
lean_dec(v_a_4135_);
lean_dec_ref(v_decl_4006_);
lean_dec_ref(v_code_4005_);
v___x_4167_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4168_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4167_);
v___y_4138_ = v___x_4168_;
goto v___jp_4137_;
}
v___jp_4137_:
{
lean_object* v___x_4139_; 
v___x_4139_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4136_, v___y_4138_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4139_, 1);
v_k_4018_ = v_a_4140_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
else
{
lean_dec_ref_known(v_value_4016_, 2);
lean_dec(v_fvarId_4015_);
return v___x_4139_;
}
}
}
case 6:
{
lean_object* v_a_4169_; lean_object* v_var_4170_; lean_object* v___x_4171_; lean_object* v_a_4172_; lean_object* v___x_4173_; lean_object* v_borrows_4174_; uint8_t v___x_4175_; 
v_a_4169_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4169_);
lean_dec_ref(v___x_4091_);
v_var_4170_ = lean_ctor_get(v_value_4016_, 1);
lean_inc(v_var_4170_);
v___x_4171_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4170_, v_a_4169_, v_a_4008_, v_a_4009_);
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref(v___x_4171_);
v___x_4173_ = lean_st_ref_get(v_a_4009_);
v_borrows_4174_ = lean_ctor_get(v___x_4173_, 1);
lean_inc_ref(v_borrows_4174_);
lean_dec(v___x_4173_);
v___x_4175_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4174_, v_fvarId_4015_);
lean_dec_ref(v_borrows_4174_);
if (v___x_4175_ == 0)
{
lean_object* v_varMap_4176_; lean_object* v___x_4177_; uint8_t v_isDefiniteRef_4178_; uint8_t v_persistent_4179_; lean_object* v___x_4180_; uint8_t v___y_4182_; 
v_varMap_4176_ = lean_ctor_get(v_a_4008_, 3);
v___x_4177_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_4176_, v_fvarId_4015_);
v_isDefiniteRef_4178_ = lean_ctor_get_uint8(v___x_4177_, sizeof(void*)*2 + 1);
v_persistent_4179_ = lean_ctor_get_uint8(v___x_4177_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_4177_);
v___x_4180_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_4178_ == 0)
{
uint8_t v___x_4184_; 
v___x_4184_ = 1;
v___y_4182_ = v___x_4184_;
goto v___jp_4181_;
}
else
{
v___y_4182_ = v___x_4175_;
goto v___jp_4181_;
}
v___jp_4181_:
{
lean_object* v___x_4183_; 
lean_inc(v_fvarId_4015_);
v___x_4183_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_4183_, 0, v_fvarId_4015_);
lean_ctor_set(v___x_4183_, 1, v___x_4180_);
lean_ctor_set(v___x_4183_, 2, v_a_4172_);
lean_ctor_set_uint8(v___x_4183_, sizeof(void*)*3, v___y_4182_);
lean_ctor_set_uint8(v___x_4183_, sizeof(void*)*3 + 1, v_persistent_4179_);
v_k_4056_ = v___x_4183_;
v___y_4057_ = v_a_4008_;
v___y_4058_ = v_a_4009_;
v___y_4059_ = v_a_4010_;
v___y_4060_ = v_a_4011_;
v___y_4061_ = v_a_4012_;
v___y_4062_ = v_a_4013_;
goto v___jp_4055_;
}
}
else
{
v_k_4056_ = v_a_4172_;
v___y_4057_ = v_a_4008_;
v___y_4058_ = v_a_4009_;
v___y_4059_ = v_a_4010_;
v___y_4060_ = v_a_4011_;
v___y_4061_ = v_a_4012_;
v___y_4062_ = v_a_4013_;
goto v___jp_4055_;
}
}
case 7:
{
lean_object* v_a_4185_; lean_object* v_var_4186_; lean_object* v___x_4187_; 
v_a_4185_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4185_);
lean_dec_ref(v___x_4091_);
v_var_4186_ = lean_ctor_get(v_value_4016_, 1);
lean_inc(v_var_4186_);
v___x_4187_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4186_, v_a_4185_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v_code_4005_) == 0)
{
lean_object* v_a_4188_; lean_object* v_decl_4189_; lean_object* v_k_4190_; size_t v___x_4191_; size_t v___x_4192_; uint8_t v___x_4193_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_a_4188_);
lean_dec_ref(v___x_4187_);
v_decl_4189_ = lean_ctor_get(v_code_4005_, 0);
v_k_4190_ = lean_ctor_get(v_code_4005_, 1);
v___x_4191_ = lean_ptr_addr(v_k_4190_);
v___x_4192_ = lean_ptr_addr(v_a_4188_);
v___x_4193_ = lean_usize_dec_eq(v___x_4191_, v___x_4192_);
if (v___x_4193_ == 0)
{
lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
v_isSharedCheck_4200_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4200_ == 0)
{
lean_object* v_unused_4201_; lean_object* v_unused_4202_; 
v_unused_4201_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4201_);
v_unused_4202_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4202_);
v___x_4195_ = v_code_4005_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_dec(v_code_4005_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 1, v_a_4188_);
lean_ctor_set(v___x_4195_, 0, v_decl_4006_);
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4199_, 1, v_a_4188_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
v_k_4018_ = v___x_4198_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
else
{
size_t v___x_4203_; size_t v___x_4204_; uint8_t v___x_4205_; 
v___x_4203_ = lean_ptr_addr(v_decl_4189_);
v___x_4204_ = lean_ptr_addr(v_decl_4006_);
v___x_4205_ = lean_usize_dec_eq(v___x_4203_, v___x_4204_);
if (v___x_4205_ == 0)
{
lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
v_isSharedCheck_4212_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4212_ == 0)
{
lean_object* v_unused_4213_; lean_object* v_unused_4214_; 
v_unused_4213_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4213_);
v_unused_4214_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4214_);
v___x_4207_ = v_code_4005_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_dec(v_code_4005_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 1, v_a_4188_);
lean_ctor_set(v___x_4207_, 0, v_decl_4006_);
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4211_, 1, v_a_4188_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
v_k_4018_ = v___x_4210_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
else
{
lean_dec(v_a_4188_);
lean_dec_ref(v_decl_4006_);
v_k_4018_ = v_code_4005_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
else
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
lean_dec_ref(v___x_4187_);
lean_dec_ref(v_decl_4006_);
lean_dec_ref(v_code_4005_);
v___x_4215_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4216_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4215_);
v_k_4018_ = v___x_4216_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
case 8:
{
lean_object* v_a_4217_; lean_object* v_var_4218_; lean_object* v___x_4219_; 
v_a_4217_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4217_);
lean_dec_ref(v___x_4091_);
v_var_4218_ = lean_ctor_get(v_value_4016_, 2);
lean_inc(v_var_4218_);
v___x_4219_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_var_4218_, v_a_4217_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v_code_4005_) == 0)
{
lean_object* v_a_4220_; lean_object* v_decl_4221_; lean_object* v_k_4222_; size_t v___x_4223_; size_t v___x_4224_; uint8_t v___x_4225_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref(v___x_4219_);
v_decl_4221_ = lean_ctor_get(v_code_4005_, 0);
v_k_4222_ = lean_ctor_get(v_code_4005_, 1);
v___x_4223_ = lean_ptr_addr(v_k_4222_);
v___x_4224_ = lean_ptr_addr(v_a_4220_);
v___x_4225_ = lean_usize_dec_eq(v___x_4223_, v___x_4224_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
v_isSharedCheck_4232_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4232_ == 0)
{
lean_object* v_unused_4233_; lean_object* v_unused_4234_; 
v_unused_4233_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4233_);
v_unused_4234_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4234_);
v___x_4227_ = v_code_4005_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_dec(v_code_4005_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 1, v_a_4220_);
lean_ctor_set(v___x_4227_, 0, v_decl_4006_);
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4231_, 1, v_a_4220_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
v_k_4018_ = v___x_4230_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
else
{
size_t v___x_4235_; size_t v___x_4236_; uint8_t v___x_4237_; 
v___x_4235_ = lean_ptr_addr(v_decl_4221_);
v___x_4236_ = lean_ptr_addr(v_decl_4006_);
v___x_4237_ = lean_usize_dec_eq(v___x_4235_, v___x_4236_);
if (v___x_4237_ == 0)
{
lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
v_isSharedCheck_4244_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4244_ == 0)
{
lean_object* v_unused_4245_; lean_object* v_unused_4246_; 
v_unused_4245_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4245_);
v_unused_4246_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4246_);
v___x_4239_ = v_code_4005_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_dec(v_code_4005_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 1, v_a_4220_);
lean_ctor_set(v___x_4239_, 0, v_decl_4006_);
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4243_, 1, v_a_4220_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
v_k_4018_ = v___x_4242_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
else
{
lean_dec(v_a_4220_);
lean_dec_ref(v_decl_4006_);
v_k_4018_ = v_code_4005_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
else
{
lean_object* v___x_4247_; lean_object* v___x_4248_; 
lean_dec_ref(v___x_4219_);
lean_dec_ref(v_decl_4006_);
lean_dec_ref(v_code_4005_);
v___x_4247_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4248_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4247_);
v_k_4018_ = v___x_4248_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
case 9:
{
lean_object* v_a_4249_; lean_object* v_fn_4250_; lean_object* v_args_4251_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___x_4263_; 
v_a_4249_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4249_);
lean_dec_ref(v___x_4091_);
v_fn_4250_ = lean_ctor_get(v_value_4016_, 0);
v_args_4251_ = lean_ctor_get(v_value_4016_, 1);
lean_inc(v_fn_4250_);
v___x_4263_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_4250_, v_a_4013_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; uint8_t v___x_4265_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v_value_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4315_; uint8_t v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4326_; uint8_t v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; uint8_t v___y_4330_; lean_object* v___y_4338_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
lean_inc(v_a_4264_);
lean_dec_ref_known(v___x_4263_, 1);
v___x_4265_ = 1;
if (lean_obj_tag(v_a_4264_) == 0)
{
lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4363_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11);
v___x_4364_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__1(v___x_4363_);
v___y_4338_ = v___x_4364_;
goto v___jp_4337_;
}
else
{
lean_object* v_val_4365_; 
v_val_4365_ = lean_ctor_get(v_a_4264_, 0);
lean_inc(v_val_4365_);
lean_dec_ref_known(v_a_4264_, 1);
v___y_4338_ = v_val_4365_;
goto v___jp_4337_;
}
v___jp_4266_:
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_4265_, v_decl_4006_, v_value_4269_, v___y_4273_);
if (lean_obj_tag(v___x_4276_) == 0)
{
if (lean_obj_tag(v_code_4005_) == 0)
{
lean_object* v_a_4277_; lean_object* v_decl_4278_; lean_object* v_k_4279_; size_t v___x_4280_; size_t v___x_4281_; uint8_t v___x_4282_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_a_4277_);
lean_dec_ref_known(v___x_4276_, 1);
v_decl_4278_ = lean_ctor_get(v_code_4005_, 0);
v_k_4279_ = lean_ctor_get(v_code_4005_, 1);
v___x_4280_ = lean_ptr_addr(v_k_4279_);
v___x_4281_ = lean_ptr_addr(v___y_4267_);
v___x_4282_ = lean_usize_dec_eq(v___x_4280_, v___x_4281_);
if (v___x_4282_ == 0)
{
lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
v_isSharedCheck_4289_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4289_ == 0)
{
lean_object* v_unused_4290_; lean_object* v_unused_4291_; 
v_unused_4290_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4290_);
v_unused_4291_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4291_);
v___x_4284_ = v_code_4005_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_dec(v_code_4005_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
lean_ctor_set(v___x_4284_, 1, v___y_4267_);
lean_ctor_set(v___x_4284_, 0, v_a_4277_);
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4277_);
lean_ctor_set(v_reuseFailAlloc_4288_, 1, v___y_4267_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
v___y_4253_ = v___y_4271_;
v___y_4254_ = v___y_4270_;
v___y_4255_ = v___y_4275_;
v___y_4256_ = v___y_4272_;
v___y_4257_ = v___y_4274_;
v___y_4258_ = v___y_4273_;
v___y_4259_ = v___y_4268_;
v___y_4260_ = v___x_4287_;
goto v___jp_4252_;
}
}
}
else
{
size_t v___x_4292_; size_t v___x_4293_; uint8_t v___x_4294_; 
v___x_4292_ = lean_ptr_addr(v_decl_4278_);
v___x_4293_ = lean_ptr_addr(v_a_4277_);
v___x_4294_ = lean_usize_dec_eq(v___x_4292_, v___x_4293_);
if (v___x_4294_ == 0)
{
lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
v_isSharedCheck_4301_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4301_ == 0)
{
lean_object* v_unused_4302_; lean_object* v_unused_4303_; 
v_unused_4302_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4302_);
v_unused_4303_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4303_);
v___x_4296_ = v_code_4005_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_dec(v_code_4005_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 1, v___y_4267_);
lean_ctor_set(v___x_4296_, 0, v_a_4277_);
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4277_);
lean_ctor_set(v_reuseFailAlloc_4300_, 1, v___y_4267_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
v___y_4253_ = v___y_4271_;
v___y_4254_ = v___y_4270_;
v___y_4255_ = v___y_4275_;
v___y_4256_ = v___y_4272_;
v___y_4257_ = v___y_4274_;
v___y_4258_ = v___y_4273_;
v___y_4259_ = v___y_4268_;
v___y_4260_ = v___x_4299_;
goto v___jp_4252_;
}
}
}
else
{
lean_dec(v_a_4277_);
lean_dec_ref(v___y_4267_);
v___y_4253_ = v___y_4271_;
v___y_4254_ = v___y_4270_;
v___y_4255_ = v___y_4275_;
v___y_4256_ = v___y_4272_;
v___y_4257_ = v___y_4274_;
v___y_4258_ = v___y_4273_;
v___y_4259_ = v___y_4268_;
v___y_4260_ = v_code_4005_;
goto v___jp_4252_;
}
}
}
else
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
lean_dec_ref_known(v___x_4276_, 1);
lean_dec_ref(v___y_4267_);
lean_dec_ref(v_code_4005_);
v___x_4304_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4305_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4304_);
v___y_4253_ = v___y_4271_;
v___y_4254_ = v___y_4270_;
v___y_4255_ = v___y_4275_;
v___y_4256_ = v___y_4272_;
v___y_4257_ = v___y_4274_;
v___y_4258_ = v___y_4273_;
v___y_4259_ = v___y_4268_;
v___y_4260_ = v___x_4305_;
goto v___jp_4252_;
}
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec_ref(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec_ref_known(v_value_4016_, 2);
lean_dec(v_fvarId_4015_);
lean_dec_ref(v_code_4005_);
v_a_4306_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4276_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4276_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
v___jp_4314_:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; uint8_t v___x_4321_; 
v___x_4319_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__3));
lean_inc_ref(v___y_4315_);
v___x_4320_ = l_Lean_Name_mkStr2(v___y_4315_, v___x_4319_);
v___x_4321_ = lean_name_eq(v_fn_4250_, v___x_4320_);
lean_dec(v___x_4320_);
if (v___x_4321_ == 0)
{
lean_inc_ref(v_value_4016_);
v___y_4267_ = v___y_4317_;
v___y_4268_ = v___y_4318_;
v_value_4269_ = v_value_4016_;
v___y_4270_ = v_a_4008_;
v___y_4271_ = v_a_4009_;
v___y_4272_ = v_a_4010_;
v___y_4273_ = v_a_4011_;
v___y_4274_ = v_a_4012_;
v___y_4275_ = v_a_4013_;
goto v___jp_4266_;
}
else
{
if (v___y_4316_ == 0)
{
lean_inc_ref(v_value_4016_);
v___y_4267_ = v___y_4317_;
v___y_4268_ = v___y_4318_;
v_value_4269_ = v_value_4016_;
v___y_4270_ = v_a_4008_;
v___y_4271_ = v_a_4009_;
v___y_4272_ = v_a_4010_;
v___y_4273_ = v_a_4011_;
v___y_4274_ = v_a_4012_;
v___y_4275_ = v_a_4013_;
goto v___jp_4266_;
}
else
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4322_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__3));
lean_inc_ref(v___y_4315_);
v___x_4323_ = l_Lean_Name_mkStr2(v___y_4315_, v___x_4322_);
lean_inc_ref(v_args_4251_);
v___x_4324_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4323_);
lean_ctor_set(v___x_4324_, 1, v_args_4251_);
v___y_4267_ = v___y_4317_;
v___y_4268_ = v___y_4318_;
v_value_4269_ = v___x_4324_;
v___y_4270_ = v_a_4008_;
v___y_4271_ = v_a_4009_;
v___y_4272_ = v_a_4010_;
v___y_4273_ = v_a_4011_;
v___y_4274_ = v_a_4012_;
v___y_4275_ = v_a_4013_;
goto v___jp_4266_;
}
}
}
v___jp_4325_:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
v___x_4331_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__2));
lean_inc_ref(v___y_4326_);
v___x_4332_ = l_Lean_Name_mkStr2(v___y_4326_, v___x_4331_);
v___x_4333_ = lean_name_eq(v_fn_4250_, v___x_4332_);
lean_dec(v___x_4332_);
if (v___x_4333_ == 0)
{
v___y_4315_ = v___y_4326_;
v___y_4316_ = v___y_4327_;
v___y_4317_ = v___y_4328_;
v___y_4318_ = v___y_4329_;
goto v___jp_4314_;
}
else
{
if (v___y_4330_ == 0)
{
v___y_4315_ = v___y_4326_;
v___y_4316_ = v___y_4327_;
v___y_4317_ = v___y_4328_;
v___y_4318_ = v___y_4329_;
goto v___jp_4314_;
}
else
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4334_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__4));
lean_inc_ref(v___y_4326_);
v___x_4335_ = l_Lean_Name_mkStr2(v___y_4326_, v___x_4334_);
lean_inc_ref(v_args_4251_);
v___x_4336_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
lean_ctor_set(v___x_4336_, 1, v_args_4251_);
v___y_4267_ = v___y_4328_;
v___y_4268_ = v___y_4329_;
v_value_4269_ = v___x_4336_;
v___y_4270_ = v_a_4008_;
v___y_4271_ = v_a_4009_;
v___y_4272_ = v_a_4010_;
v___y_4273_ = v_a_4011_;
v___y_4274_ = v_a_4012_;
v___y_4275_ = v_a_4013_;
goto v___jp_4266_;
}
}
}
v___jp_4337_:
{
lean_object* v_params_4339_; lean_object* v___x_4340_; 
v_params_4339_ = lean_ctor_get(v___y_4338_, 3);
lean_inc_ref_n(v_params_4339_, 2);
lean_dec_ref(v___y_4338_);
v___x_4340_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecAfterFullApp(v_args_4251_, v_params_4339_, v_a_4249_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4340_) == 0)
{
lean_object* v_a_4341_; lean_object* v___x_4342_; lean_object* v_borrows_4343_; uint8_t v___x_4344_; lean_object* v___x_4345_; lean_object* v_borrows_4346_; uint8_t v___x_4347_; lean_object* v___x_4348_; lean_object* v_borrows_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4361_; 
v_a_4341_ = lean_ctor_get(v___x_4340_, 0);
lean_inc(v_a_4341_);
lean_dec_ref_known(v___x_4340_, 1);
v___x_4342_ = lean_st_ref_get(v_a_4009_);
v_borrows_4343_ = lean_ctor_get(v___x_4342_, 1);
lean_inc_ref(v_borrows_4343_);
lean_dec(v___x_4342_);
v___x_4344_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4343_, v_fvarId_4015_);
lean_dec_ref(v_borrows_4343_);
v___x_4345_ = lean_st_ref_get(v_a_4009_);
v_borrows_4346_ = lean_ctor_get(v___x_4345_, 1);
lean_inc_ref(v_borrows_4346_);
lean_dec(v___x_4345_);
v___x_4347_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4346_, v_fvarId_4015_);
lean_dec_ref(v_borrows_4346_);
v___x_4348_ = lean_st_ref_get(v_a_4009_);
v_borrows_4349_ = lean_ctor_get(v___x_4348_, 1);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4361_ == 0)
{
lean_object* v_unused_4362_; 
v_unused_4362_ = lean_ctor_get(v___x_4348_, 0);
lean_dec(v_unused_4362_);
v___x_4351_ = v___x_4348_;
v_isShared_4352_ = v_isSharedCheck_4361_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_borrows_4349_);
lean_dec(v___x_4348_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4361_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
uint8_t v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; uint8_t v___x_4356_; 
v___x_4353_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_4349_, v_fvarId_4015_);
lean_dec_ref(v_borrows_4349_);
v___x_4354_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl___closed__0));
v___x_4355_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__5));
v___x_4356_ = lean_name_eq(v_fn_4250_, v___x_4355_);
if (v___x_4356_ == 0)
{
lean_del_object(v___x_4351_);
v___y_4326_ = v___x_4354_;
v___y_4327_ = v___x_4353_;
v___y_4328_ = v_a_4341_;
v___y_4329_ = v_params_4339_;
v___y_4330_ = v___x_4347_;
goto v___jp_4325_;
}
else
{
if (v___x_4344_ == 0)
{
lean_del_object(v___x_4351_);
v___y_4326_ = v___x_4354_;
v___y_4327_ = v___x_4353_;
v___y_4328_ = v_a_4341_;
v___y_4329_ = v_params_4339_;
v___y_4330_ = v___x_4347_;
goto v___jp_4325_;
}
else
{
lean_object* v___x_4357_; lean_object* v___x_4359_; 
v___x_4357_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__7));
lean_inc_ref(v_args_4251_);
if (v_isShared_4352_ == 0)
{
lean_ctor_set_tag(v___x_4351_, 9);
lean_ctor_set(v___x_4351_, 1, v_args_4251_);
lean_ctor_set(v___x_4351_, 0, v___x_4357_);
v___x_4359_ = v___x_4351_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4357_);
lean_ctor_set(v_reuseFailAlloc_4360_, 1, v_args_4251_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
v___y_4267_ = v_a_4341_;
v___y_4268_ = v_params_4339_;
v_value_4269_ = v___x_4359_;
v___y_4270_ = v_a_4008_;
v___y_4271_ = v_a_4009_;
v___y_4272_ = v_a_4010_;
v___y_4273_ = v_a_4011_;
v___y_4274_ = v_a_4012_;
v___y_4275_ = v_a_4013_;
goto v___jp_4266_;
}
}
}
}
}
else
{
lean_dec_ref(v_params_4339_);
lean_dec_ref_known(v_value_4016_, 2);
lean_dec(v_fvarId_4015_);
lean_dec_ref(v_decl_4006_);
lean_dec_ref(v_code_4005_);
return v___x_4340_;
}
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec_ref_known(v_value_4016_, 2);
lean_dec(v_a_4249_);
lean_dec(v_fvarId_4015_);
lean_dec_ref(v_decl_4006_);
lean_dec_ref(v_code_4005_);
v_a_4366_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4263_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4263_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
v___jp_4252_:
{
lean_object* v___x_4261_; 
v___x_4261_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_4251_, v___y_4259_, v___y_4260_, v___y_4254_, v___y_4253_, v___y_4256_, v___y_4258_, v___y_4257_, v___y_4255_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v___x_4261_, 1);
v_k_4018_ = v_a_4262_;
v___y_4019_ = v___y_4254_;
v___y_4020_ = v___y_4253_;
v___y_4021_ = v___y_4256_;
v___y_4022_ = v___y_4258_;
v___y_4023_ = v___y_4257_;
v___y_4024_ = v___y_4255_;
goto v___jp_4017_;
}
else
{
lean_dec_ref_known(v_value_4016_, 2);
lean_dec(v_fvarId_4015_);
return v___x_4261_;
}
}
}
case 10:
{
lean_object* v_a_4374_; lean_object* v_args_4375_; lean_object* v___y_4377_; 
v_a_4374_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4374_);
lean_dec_ref(v___x_4091_);
v_args_4375_ = lean_ctor_get(v_value_4016_, 1);
if (lean_obj_tag(v_code_4005_) == 0)
{
lean_object* v_decl_4380_; lean_object* v_k_4381_; size_t v___x_4382_; size_t v___x_4383_; uint8_t v___x_4384_; 
v_decl_4380_ = lean_ctor_get(v_code_4005_, 0);
v_k_4381_ = lean_ctor_get(v_code_4005_, 1);
v___x_4382_ = lean_ptr_addr(v_k_4381_);
v___x_4383_ = lean_ptr_addr(v_a_4374_);
v___x_4384_ = lean_usize_dec_eq(v___x_4382_, v___x_4383_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
v_isSharedCheck_4391_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4391_ == 0)
{
lean_object* v_unused_4392_; lean_object* v_unused_4393_; 
v_unused_4392_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4392_);
v_unused_4393_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4393_);
v___x_4386_ = v_code_4005_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_dec(v_code_4005_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4389_; 
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 1, v_a_4374_);
lean_ctor_set(v___x_4386_, 0, v_decl_4006_);
v___x_4389_ = v___x_4386_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v_a_4374_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
v___y_4377_ = v___x_4389_;
goto v___jp_4376_;
}
}
}
else
{
size_t v___x_4394_; size_t v___x_4395_; uint8_t v___x_4396_; 
v___x_4394_ = lean_ptr_addr(v_decl_4380_);
v___x_4395_ = lean_ptr_addr(v_decl_4006_);
v___x_4396_ = lean_usize_dec_eq(v___x_4394_, v___x_4395_);
if (v___x_4396_ == 0)
{
lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
v_isSharedCheck_4403_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4403_ == 0)
{
lean_object* v_unused_4404_; lean_object* v_unused_4405_; 
v_unused_4404_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4404_);
v_unused_4405_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4405_);
v___x_4398_ = v_code_4005_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_dec(v_code_4005_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 1, v_a_4374_);
lean_ctor_set(v___x_4398_, 0, v_decl_4006_);
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4402_, 1, v_a_4374_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
v___y_4377_ = v___x_4401_;
goto v___jp_4376_;
}
}
}
else
{
lean_dec(v_a_4374_);
lean_dec_ref(v_decl_4006_);
v___y_4377_ = v_code_4005_;
goto v___jp_4376_;
}
}
}
else
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
lean_dec(v_a_4374_);
lean_dec_ref(v_decl_4006_);
lean_dec_ref(v_code_4005_);
v___x_4406_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4407_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4406_);
v___y_4377_ = v___x_4407_;
goto v___jp_4376_;
}
v___jp_4376_:
{
lean_object* v___x_4378_; 
v___x_4378_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4375_, v___y_4377_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
lean_dec_ref_known(v___x_4378_, 1);
v_k_4018_ = v_a_4379_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
else
{
lean_dec_ref_known(v_value_4016_, 2);
lean_dec(v_fvarId_4015_);
return v___x_4378_;
}
}
}
case 12:
{
lean_object* v_a_4408_; lean_object* v_args_4409_; lean_object* v___y_4411_; 
v_a_4408_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4408_);
lean_dec_ref(v___x_4091_);
v_args_4409_ = lean_ctor_get(v_value_4016_, 2);
if (lean_obj_tag(v_code_4005_) == 0)
{
lean_object* v_decl_4414_; lean_object* v_k_4415_; size_t v___x_4416_; size_t v___x_4417_; uint8_t v___x_4418_; 
v_decl_4414_ = lean_ctor_get(v_code_4005_, 0);
v_k_4415_ = lean_ctor_get(v_code_4005_, 1);
v___x_4416_ = lean_ptr_addr(v_k_4415_);
v___x_4417_ = lean_ptr_addr(v_a_4408_);
v___x_4418_ = lean_usize_dec_eq(v___x_4416_, v___x_4417_);
if (v___x_4418_ == 0)
{
lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
v_isSharedCheck_4425_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4425_ == 0)
{
lean_object* v_unused_4426_; lean_object* v_unused_4427_; 
v_unused_4426_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4426_);
v_unused_4427_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4427_);
v___x_4420_ = v_code_4005_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_dec(v_code_4005_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 1, v_a_4408_);
lean_ctor_set(v___x_4420_, 0, v_decl_4006_);
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4424_, 1, v_a_4408_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
v___y_4411_ = v___x_4423_;
goto v___jp_4410_;
}
}
}
else
{
size_t v___x_4428_; size_t v___x_4429_; uint8_t v___x_4430_; 
v___x_4428_ = lean_ptr_addr(v_decl_4414_);
v___x_4429_ = lean_ptr_addr(v_decl_4006_);
v___x_4430_ = lean_usize_dec_eq(v___x_4428_, v___x_4429_);
if (v___x_4430_ == 0)
{
lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
v_isSharedCheck_4437_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4437_ == 0)
{
lean_object* v_unused_4438_; lean_object* v_unused_4439_; 
v_unused_4438_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4438_);
v_unused_4439_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4439_);
v___x_4432_ = v_code_4005_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_dec(v_code_4005_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 1, v_a_4408_);
lean_ctor_set(v___x_4432_, 0, v_decl_4006_);
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4436_, 1, v_a_4408_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
v___y_4411_ = v___x_4435_;
goto v___jp_4410_;
}
}
}
else
{
lean_dec(v_a_4408_);
lean_dec_ref(v_decl_4006_);
v___y_4411_ = v_code_4005_;
goto v___jp_4410_;
}
}
}
else
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
lean_dec(v_a_4408_);
lean_dec_ref(v_decl_4006_);
lean_dec_ref(v_code_4005_);
v___x_4440_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4441_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4440_);
v___y_4411_ = v___x_4441_;
goto v___jp_4410_;
}
v___jp_4410_:
{
lean_object* v___x_4412_; 
v___x_4412_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBeforeConsumeAll(v_args_4409_, v___y_4411_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v_k_4018_ = v_a_4413_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
else
{
lean_dec_ref_known(v_value_4016_, 3);
lean_dec(v_fvarId_4015_);
return v___x_4412_;
}
}
}
case 14:
{
lean_object* v_a_4442_; lean_object* v_fvarId_4443_; lean_object* v___x_4444_; 
v_a_4442_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4442_);
lean_dec_ref(v___x_4091_);
v_fvarId_4443_ = lean_ctor_get(v_value_4016_, 0);
lean_inc(v_fvarId_4443_);
v___x_4444_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecIfNeeded___redArg(v_fvarId_4443_, v_a_4442_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v_code_4005_) == 0)
{
lean_object* v_a_4445_; lean_object* v_decl_4446_; lean_object* v_k_4447_; size_t v___x_4448_; size_t v___x_4449_; uint8_t v___x_4450_; 
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_a_4445_);
lean_dec_ref(v___x_4444_);
v_decl_4446_ = lean_ctor_get(v_code_4005_, 0);
v_k_4447_ = lean_ctor_get(v_code_4005_, 1);
v___x_4448_ = lean_ptr_addr(v_k_4447_);
v___x_4449_ = lean_ptr_addr(v_a_4445_);
v___x_4450_ = lean_usize_dec_eq(v___x_4448_, v___x_4449_);
if (v___x_4450_ == 0)
{
lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
v_isSharedCheck_4457_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4457_ == 0)
{
lean_object* v_unused_4458_; lean_object* v_unused_4459_; 
v_unused_4458_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4458_);
v_unused_4459_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4459_);
v___x_4452_ = v_code_4005_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_dec(v_code_4005_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 1, v_a_4445_);
lean_ctor_set(v___x_4452_, 0, v_decl_4006_);
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4456_, 1, v_a_4445_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
v_k_4018_ = v___x_4455_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
else
{
size_t v___x_4460_; size_t v___x_4461_; uint8_t v___x_4462_; 
v___x_4460_ = lean_ptr_addr(v_decl_4446_);
v___x_4461_ = lean_ptr_addr(v_decl_4006_);
v___x_4462_ = lean_usize_dec_eq(v___x_4460_, v___x_4461_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4469_; 
v_isSharedCheck_4469_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4469_ == 0)
{
lean_object* v_unused_4470_; lean_object* v_unused_4471_; 
v_unused_4470_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4470_);
v_unused_4471_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4471_);
v___x_4464_ = v_code_4005_;
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
else
{
lean_dec(v_code_4005_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4467_; 
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 1, v_a_4445_);
lean_ctor_set(v___x_4464_, 0, v_decl_4006_);
v___x_4467_ = v___x_4464_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4468_, 1, v_a_4445_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
v_k_4018_ = v___x_4467_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
else
{
lean_dec(v_a_4445_);
lean_dec_ref(v_decl_4006_);
v_k_4018_ = v_code_4005_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
else
{
lean_object* v___x_4472_; lean_object* v___x_4473_; 
lean_dec_ref(v___x_4444_);
lean_dec_ref(v_decl_4006_);
lean_dec_ref(v_code_4005_);
v___x_4472_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4473_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4472_);
v_k_4018_ = v___x_4473_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
case 15:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
lean_dec_ref(v___x_4091_);
lean_dec_ref(v_decl_4006_);
lean_dec_ref(v_code_4005_);
v___x_4474_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__13, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__13);
v___x_4475_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v___x_4474_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_object* v_a_4476_; 
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
lean_inc(v_a_4476_);
lean_dec_ref_known(v___x_4475_, 1);
v_k_4018_ = v_a_4476_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
else
{
lean_dec_ref_known(v_value_4016_, 1);
lean_dec(v_fvarId_4015_);
return v___x_4475_;
}
}
default: 
{
if (lean_obj_tag(v_code_4005_) == 0)
{
lean_object* v_a_4477_; lean_object* v_decl_4478_; lean_object* v_k_4479_; size_t v___x_4480_; size_t v___x_4481_; uint8_t v___x_4482_; 
v_a_4477_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4477_);
lean_dec_ref(v___x_4091_);
v_decl_4478_ = lean_ctor_get(v_code_4005_, 0);
v_k_4479_ = lean_ctor_get(v_code_4005_, 1);
v___x_4480_ = lean_ptr_addr(v_k_4479_);
v___x_4481_ = lean_ptr_addr(v_a_4477_);
v___x_4482_ = lean_usize_dec_eq(v___x_4480_, v___x_4481_);
if (v___x_4482_ == 0)
{
lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4489_; 
v_isSharedCheck_4489_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4489_ == 0)
{
lean_object* v_unused_4490_; lean_object* v_unused_4491_; 
v_unused_4490_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4490_);
v_unused_4491_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4491_);
v___x_4484_ = v_code_4005_;
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
else
{
lean_dec(v_code_4005_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 1, v_a_4477_);
lean_ctor_set(v___x_4484_, 0, v_decl_4006_);
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4488_, 1, v_a_4477_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
v_k_4018_ = v___x_4487_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
else
{
size_t v___x_4492_; size_t v___x_4493_; uint8_t v___x_4494_; 
v___x_4492_ = lean_ptr_addr(v_decl_4478_);
v___x_4493_ = lean_ptr_addr(v_decl_4006_);
v___x_4494_ = lean_usize_dec_eq(v___x_4492_, v___x_4493_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
v_isSharedCheck_4501_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; lean_object* v_unused_4503_; 
v_unused_4502_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4502_);
v_unused_4503_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4503_);
v___x_4496_ = v_code_4005_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_dec(v_code_4005_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 1, v_a_4477_);
lean_ctor_set(v___x_4496_, 0, v_decl_4006_);
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v_a_4477_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
v_k_4018_ = v___x_4499_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
else
{
lean_dec(v_a_4477_);
lean_dec_ref(v_decl_4006_);
v_k_4018_ = v_code_4005_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
else
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
lean_dec_ref(v___x_4091_);
lean_dec_ref(v_decl_4006_);
lean_dec_ref(v_code_4005_);
v___x_4504_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4505_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4504_);
v_k_4018_ = v___x_4505_;
v___y_4019_ = v_a_4008_;
v___y_4020_ = v_a_4009_;
v___y_4021_ = v_a_4010_;
v___y_4022_ = v_a_4011_;
v___y_4023_ = v_a_4012_;
v___y_4024_ = v_a_4013_;
goto v___jp_4017_;
}
}
}
v___jp_4017_:
{
lean_object* v___x_4025_; 
v___x_4025_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue(v_value_4016_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4045_; 
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4045_ == 0)
{
lean_object* v_unused_4046_; 
v_unused_4046_ = lean_ctor_get(v___x_4025_, 0);
lean_dec(v_unused_4046_);
v___x_4027_ = v___x_4025_;
v_isShared_4028_ = v_isSharedCheck_4045_;
goto v_resetjp_4026_;
}
else
{
lean_dec(v___x_4025_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4045_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4029_; lean_object* v_vars_4030_; lean_object* v_borrows_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4044_; 
v___x_4029_ = lean_st_ref_take(v___y_4020_);
v_vars_4030_ = lean_ctor_get(v___x_4029_, 0);
v_borrows_4031_ = lean_ctor_get(v___x_4029_, 1);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4033_ = v___x_4029_;
v_isShared_4034_ = v_isSharedCheck_4044_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_borrows_4031_);
lean_inc(v_vars_4030_);
lean_dec(v___x_4029_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4044_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v_vars_4035_; lean_object* v_borrows_4036_; lean_object* v___x_4038_; 
v_vars_4035_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_vars_4030_, v_fvarId_4015_);
v_borrows_4036_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams_spec__0___redArg(v_borrows_4031_, v_fvarId_4015_);
lean_dec(v_fvarId_4015_);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 1, v_borrows_4036_);
lean_ctor_set(v___x_4033_, 0, v_vars_4035_);
v___x_4038_ = v___x_4033_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_vars_4035_);
lean_ctor_set(v_reuseFailAlloc_4043_, 1, v_borrows_4036_);
v___x_4038_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
lean_object* v___x_4039_; lean_object* v___x_4041_; 
v___x_4039_ = lean_st_ref_put(v___y_4020_, v___x_4038_);
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 0, v_k_4018_);
v___x_4041_ = v___x_4027_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_k_4018_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_dec_ref(v_k_4018_);
lean_dec(v_fvarId_4015_);
v_a_4047_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4025_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4025_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
v___jp_4055_:
{
if (lean_obj_tag(v_code_4005_) == 0)
{
lean_object* v_decl_4063_; lean_object* v_k_4064_; size_t v___x_4065_; size_t v___x_4066_; uint8_t v___x_4067_; 
v_decl_4063_ = lean_ctor_get(v_code_4005_, 0);
v_k_4064_ = lean_ctor_get(v_code_4005_, 1);
v___x_4065_ = lean_ptr_addr(v_k_4064_);
v___x_4066_ = lean_ptr_addr(v_k_4056_);
v___x_4067_ = lean_usize_dec_eq(v___x_4065_, v___x_4066_);
if (v___x_4067_ == 0)
{
lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
v_isSharedCheck_4074_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4074_ == 0)
{
lean_object* v_unused_4075_; lean_object* v_unused_4076_; 
v_unused_4075_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4075_);
v_unused_4076_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4076_);
v___x_4069_ = v_code_4005_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_dec(v_code_4005_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 1, v_k_4056_);
lean_ctor_set(v___x_4069_, 0, v_decl_4006_);
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4073_, 1, v_k_4056_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
v_k_4018_ = v___x_4072_;
v___y_4019_ = v___y_4057_;
v___y_4020_ = v___y_4058_;
v___y_4021_ = v___y_4059_;
v___y_4022_ = v___y_4060_;
v___y_4023_ = v___y_4061_;
v___y_4024_ = v___y_4062_;
goto v___jp_4017_;
}
}
}
else
{
size_t v___x_4077_; size_t v___x_4078_; uint8_t v___x_4079_; 
v___x_4077_ = lean_ptr_addr(v_decl_4063_);
v___x_4078_ = lean_ptr_addr(v_decl_4006_);
v___x_4079_ = lean_usize_dec_eq(v___x_4077_, v___x_4078_);
if (v___x_4079_ == 0)
{
lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
v_isSharedCheck_4086_ = !lean_is_exclusive(v_code_4005_);
if (v_isSharedCheck_4086_ == 0)
{
lean_object* v_unused_4087_; lean_object* v_unused_4088_; 
v_unused_4087_ = lean_ctor_get(v_code_4005_, 1);
lean_dec(v_unused_4087_);
v_unused_4088_ = lean_ctor_get(v_code_4005_, 0);
lean_dec(v_unused_4088_);
v___x_4081_ = v_code_4005_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_dec(v_code_4005_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 1, v_k_4056_);
lean_ctor_set(v___x_4081_, 0, v_decl_4006_);
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_decl_4006_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v_k_4056_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
v_k_4018_ = v___x_4084_;
v___y_4019_ = v___y_4057_;
v___y_4020_ = v___y_4058_;
v___y_4021_ = v___y_4059_;
v___y_4022_ = v___y_4060_;
v___y_4023_ = v___y_4061_;
v___y_4024_ = v___y_4062_;
goto v___jp_4017_;
}
}
}
else
{
lean_dec_ref(v_k_4056_);
lean_dec_ref(v_decl_4006_);
v_k_4018_ = v_code_4005_;
v___y_4019_ = v___y_4057_;
v___y_4020_ = v___y_4058_;
v___y_4021_ = v___y_4059_;
v___y_4022_ = v___y_4060_;
v___y_4023_ = v___y_4061_;
v___y_4024_ = v___y_4062_;
goto v___jp_4017_;
}
}
}
else
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
lean_dec_ref(v_k_4056_);
lean_dec_ref(v_decl_4006_);
lean_dec_ref(v_code_4005_);
v___x_4089_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__2);
v___x_4090_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__0(v___x_4089_);
v_k_4018_ = v___x_4090_;
v___y_4019_ = v___y_4057_;
v___y_4020_ = v___y_4058_;
v___y_4021_ = v___y_4059_;
v___y_4022_ = v___y_4060_;
v___y_4023_ = v___y_4061_;
v___y_4024_ = v___y_4062_;
goto v___jp_4017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___boxed(lean_object* v_code_4506_, lean_object* v_decl_4507_, lean_object* v_k_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(v_code_4506_, v_decl_4507_, v_k_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
return v_res_4516_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0(void){
_start:
{
lean_object* v___x_4517_; 
v___x_4517_ = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___redArg();
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5(lean_object* v_msg_4518_){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4519_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5___closed__0);
v___x_4520_ = lean_panic_fn_borrowed(v___x_4519_, v_msg_4518_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(lean_object* v_a_4521_, lean_object* v_b_4522_, lean_object* v_x_4523_){
_start:
{
if (lean_obj_tag(v_x_4523_) == 0)
{
lean_dec(v_b_4522_);
lean_dec(v_a_4521_);
return v_x_4523_;
}
else
{
lean_object* v_key_4524_; lean_object* v_value_4525_; lean_object* v_tail_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4538_; 
v_key_4524_ = lean_ctor_get(v_x_4523_, 0);
v_value_4525_ = lean_ctor_get(v_x_4523_, 1);
v_tail_4526_ = lean_ctor_get(v_x_4523_, 2);
v_isSharedCheck_4538_ = !lean_is_exclusive(v_x_4523_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4528_ = v_x_4523_;
v_isShared_4529_ = v_isSharedCheck_4538_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_tail_4526_);
lean_inc(v_value_4525_);
lean_inc(v_key_4524_);
lean_dec(v_x_4523_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4538_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
uint8_t v___x_4530_; 
v___x_4530_ = l_Lean_instBEqFVarId_beq(v_key_4524_, v_a_4521_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; lean_object* v___x_4533_; 
v___x_4531_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(v_a_4521_, v_b_4522_, v_tail_4526_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 2, v___x_4531_);
v___x_4533_ = v___x_4528_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_key_4524_);
lean_ctor_set(v_reuseFailAlloc_4534_, 1, v_value_4525_);
lean_ctor_set(v_reuseFailAlloc_4534_, 2, v___x_4531_);
v___x_4533_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
return v___x_4533_;
}
}
else
{
lean_object* v___x_4536_; 
lean_dec(v_value_4525_);
lean_dec(v_key_4524_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 1, v_b_4522_);
lean_ctor_set(v___x_4528_, 0, v_a_4521_);
v___x_4536_ = v___x_4528_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4521_);
lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_b_4522_);
lean_ctor_set(v_reuseFailAlloc_4537_, 2, v_tail_4526_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(lean_object* v_m_4539_, lean_object* v_a_4540_, lean_object* v_b_4541_){
_start:
{
lean_object* v_size_4542_; lean_object* v_buckets_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4586_; 
v_size_4542_ = lean_ctor_get(v_m_4539_, 0);
v_buckets_4543_ = lean_ctor_get(v_m_4539_, 1);
v_isSharedCheck_4586_ = !lean_is_exclusive(v_m_4539_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4545_ = v_m_4539_;
v_isShared_4546_ = v_isSharedCheck_4586_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_buckets_4543_);
lean_inc(v_size_4542_);
lean_dec(v_m_4539_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4586_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4547_; uint64_t v___x_4548_; uint64_t v___x_4549_; uint64_t v___x_4550_; uint64_t v_fold_4551_; uint64_t v___x_4552_; uint64_t v___x_4553_; uint64_t v___x_4554_; size_t v___x_4555_; size_t v___x_4556_; size_t v___x_4557_; size_t v___x_4558_; size_t v___x_4559_; lean_object* v_bkt_4560_; uint8_t v___x_4561_; 
v___x_4547_ = lean_array_get_size(v_buckets_4543_);
v___x_4548_ = l_Lean_instHashableFVarId_hash(v_a_4540_);
v___x_4549_ = 32ULL;
v___x_4550_ = lean_uint64_shift_right(v___x_4548_, v___x_4549_);
v_fold_4551_ = lean_uint64_xor(v___x_4548_, v___x_4550_);
v___x_4552_ = 16ULL;
v___x_4553_ = lean_uint64_shift_right(v_fold_4551_, v___x_4552_);
v___x_4554_ = lean_uint64_xor(v_fold_4551_, v___x_4553_);
v___x_4555_ = lean_uint64_to_usize(v___x_4554_);
v___x_4556_ = lean_usize_of_nat(v___x_4547_);
v___x_4557_ = ((size_t)1ULL);
v___x_4558_ = lean_usize_sub(v___x_4556_, v___x_4557_);
v___x_4559_ = lean_usize_land(v___x_4555_, v___x_4558_);
v_bkt_4560_ = lean_array_uget_borrowed(v_buckets_4543_, v___x_4559_);
v___x_4561_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__0___redArg(v_a_4540_, v_bkt_4560_);
if (v___x_4561_ == 0)
{
lean_object* v___x_4562_; lean_object* v_size_x27_4563_; lean_object* v___x_4564_; lean_object* v_buckets_x27_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; uint8_t v___x_4571_; 
v___x_4562_ = lean_unsigned_to_nat(1u);
v_size_x27_4563_ = lean_nat_add(v_size_4542_, v___x_4562_);
lean_dec(v_size_4542_);
lean_inc(v_bkt_4560_);
v___x_4564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4564_, 0, v_a_4540_);
lean_ctor_set(v___x_4564_, 1, v_b_4541_);
lean_ctor_set(v___x_4564_, 2, v_bkt_4560_);
v_buckets_x27_4565_ = lean_array_uset(v_buckets_4543_, v___x_4559_, v___x_4564_);
v___x_4566_ = lean_unsigned_to_nat(4u);
v___x_4567_ = lean_nat_mul(v_size_x27_4563_, v___x_4566_);
v___x_4568_ = lean_unsigned_to_nat(3u);
v___x_4569_ = lean_nat_div(v___x_4567_, v___x_4568_);
lean_dec(v___x_4567_);
v___x_4570_ = lean_array_get_size(v_buckets_x27_4565_);
v___x_4571_ = lean_nat_dec_le(v___x_4569_, v___x_4570_);
lean_dec(v___x_4569_);
if (v___x_4571_ == 0)
{
lean_object* v_val_4572_; lean_object* v___x_4574_; 
v_val_4572_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0_spec__1___redArg(v_buckets_x27_4565_);
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 1, v_val_4572_);
lean_ctor_set(v___x_4545_, 0, v_size_x27_4563_);
v___x_4574_ = v___x_4545_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_size_x27_4563_);
lean_ctor_set(v_reuseFailAlloc_4575_, 1, v_val_4572_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
else
{
lean_object* v___x_4577_; 
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 1, v_buckets_x27_4565_);
lean_ctor_set(v___x_4545_, 0, v_size_x27_4563_);
v___x_4577_ = v___x_4545_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_size_x27_4563_);
lean_ctor_set(v_reuseFailAlloc_4578_, 1, v_buckets_x27_4565_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
else
{
lean_object* v___x_4579_; lean_object* v_buckets_x27_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4584_; 
lean_inc(v_bkt_4560_);
v___x_4579_ = lean_box(0);
v_buckets_x27_4580_ = lean_array_uset(v_buckets_4543_, v___x_4559_, v___x_4579_);
v___x_4581_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(v_a_4540_, v_b_4541_, v_bkt_4560_);
v___x_4582_ = lean_array_uset(v_buckets_x27_4580_, v___x_4559_, v___x_4581_);
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 1, v___x_4582_);
v___x_4584_ = v___x_4545_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_size_4542_);
lean_ctor_set(v_reuseFailAlloc_4585_, 1, v___x_4582_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__2(lean_object* v_a_4587_, lean_object* v_a_4588_){
_start:
{
if (lean_obj_tag(v_a_4587_) == 0)
{
lean_object* v___x_4589_; 
v___x_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4589_, 0, v_a_4588_);
return v___x_4589_;
}
else
{
lean_object* v_key_4590_; lean_object* v_value_4591_; lean_object* v_tail_4592_; lean_object* v_r_4593_; 
v_key_4590_ = lean_ctor_get(v_a_4587_, 0);
lean_inc(v_key_4590_);
v_value_4591_ = lean_ctor_get(v_a_4587_, 1);
lean_inc(v_value_4591_);
v_tail_4592_ = lean_ctor_get(v_a_4587_, 2);
lean_inc(v_tail_4592_);
lean_dec_ref_known(v_a_4587_, 3);
v_r_4593_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(v_a_4588_, v_key_4590_, v_value_4591_);
v_a_4587_ = v_tail_4592_;
v_a_4588_ = v_r_4593_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(lean_object* v_as_4595_, size_t v_sz_4596_, size_t v_i_4597_, lean_object* v_b_4598_){
_start:
{
uint8_t v___x_4599_; 
v___x_4599_ = lean_usize_dec_lt(v_i_4597_, v_sz_4596_);
if (v___x_4599_ == 0)
{
return v_b_4598_;
}
else
{
lean_object* v_a_4600_; lean_object* v___x_4601_; 
v_a_4600_ = lean_array_uget_borrowed(v_as_4595_, v_i_4597_);
lean_inc(v_a_4600_);
v___x_4601_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__2(v_a_4600_, v_b_4598_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v_a_4602_; 
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_a_4602_);
lean_dec_ref_known(v___x_4601_, 1);
return v_a_4602_;
}
else
{
lean_object* v_a_4603_; size_t v___x_4604_; size_t v___x_4605_; 
v_a_4603_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_a_4603_);
lean_dec_ref_known(v___x_4601_, 1);
v___x_4604_ = ((size_t)1ULL);
v___x_4605_ = lean_usize_add(v_i_4597_, v___x_4604_);
v_i_4597_ = v___x_4605_;
v_b_4598_ = v_a_4603_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3___boxed(lean_object* v_as_4607_, lean_object* v_sz_4608_, lean_object* v_i_4609_, lean_object* v_b_4610_){
_start:
{
size_t v_sz_boxed_4611_; size_t v_i_boxed_4612_; lean_object* v_res_4613_; 
v_sz_boxed_4611_ = lean_unbox_usize(v_sz_4608_);
lean_dec(v_sz_4608_);
v_i_boxed_4612_ = lean_unbox_usize(v_i_4609_);
lean_dec(v_i_4609_);
v_res_4613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(v_as_4607_, v_sz_boxed_4611_, v_i_boxed_4612_, v_b_4610_);
lean_dec_ref(v_as_4607_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(lean_object* v_m_4614_, lean_object* v_l_4615_){
_start:
{
lean_object* v_buckets_4616_; size_t v_sz_4617_; size_t v___x_4618_; lean_object* v___x_4619_; 
v_buckets_4616_ = lean_ctor_get(v_l_4615_, 1);
v_sz_4617_ = lean_array_size(v_buckets_4616_);
v___x_4618_ = ((size_t)0ULL);
v___x_4619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__3(v_buckets_4616_, v_sz_4617_, v___x_4618_, v_m_4614_);
return v___x_4619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1___boxed(lean_object* v_m_4620_, lean_object* v_l_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_m_4620_, v_l_4621_);
lean_dec_ref(v_l_4621_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(lean_object* v_a_4623_, lean_object* v_a_4624_){
_start:
{
if (lean_obj_tag(v_a_4623_) == 0)
{
lean_object* v___x_4625_; 
v___x_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4625_, 0, v_a_4624_);
return v___x_4625_;
}
else
{
lean_object* v_key_4626_; lean_object* v_value_4627_; lean_object* v_tail_4628_; lean_object* v_r_4629_; 
v_key_4626_ = lean_ctor_get(v_a_4623_, 0);
lean_inc(v_key_4626_);
v_value_4627_ = lean_ctor_get(v_a_4623_, 1);
lean_inc(v_value_4627_);
v_tail_4628_ = lean_ctor_get(v_a_4623_, 2);
lean_inc(v_tail_4628_);
lean_dec_ref_known(v_a_4623_, 3);
v_r_4629_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go_spec__0___redArg(v_a_4624_, v_key_4626_, v_value_4627_);
v_a_4623_ = v_tail_4628_;
v_a_4624_ = v_r_4629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(lean_object* v_as_4631_, size_t v_sz_4632_, size_t v_i_4633_, lean_object* v_b_4634_){
_start:
{
uint8_t v___x_4635_; 
v___x_4635_ = lean_usize_dec_lt(v_i_4633_, v_sz_4632_);
if (v___x_4635_ == 0)
{
return v_b_4634_;
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4637_; 
v_a_4636_ = lean_array_uget_borrowed(v_as_4631_, v_i_4633_);
lean_inc(v_a_4636_);
v___x_4637_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__0(v_a_4636_, v_b_4634_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_a_4638_);
lean_dec_ref_known(v___x_4637_, 1);
return v_a_4638_;
}
else
{
lean_object* v_a_4639_; size_t v___x_4640_; size_t v___x_4641_; 
v_a_4639_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_a_4639_);
lean_dec_ref_known(v___x_4637_, 1);
v___x_4640_ = ((size_t)1ULL);
v___x_4641_ = lean_usize_add(v_i_4633_, v___x_4640_);
v_i_4633_ = v___x_4641_;
v_b_4634_ = v_a_4639_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2___boxed(lean_object* v_as_4643_, lean_object* v_sz_4644_, lean_object* v_i_4645_, lean_object* v_b_4646_){
_start:
{
size_t v_sz_boxed_4647_; size_t v_i_boxed_4648_; lean_object* v_res_4649_; 
v_sz_boxed_4647_ = lean_unbox_usize(v_sz_4644_);
lean_dec(v_sz_4644_);
v_i_boxed_4648_ = lean_unbox_usize(v_i_4645_);
lean_dec(v_i_4645_);
v_res_4649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_as_4643_, v_sz_boxed_4647_, v_i_boxed_4648_, v_b_4646_);
lean_dec_ref(v_as_4643_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(lean_object* v_as_4650_, size_t v_i_4651_, size_t v_stop_4652_, lean_object* v_b_4653_){
_start:
{
lean_object* v___y_4655_; lean_object* v___y_4656_; uint8_t v___x_4661_; 
v___x_4661_ = lean_usize_dec_eq(v_i_4651_, v_stop_4652_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; lean_object* v_snd_4663_; lean_object* v_vars_4664_; lean_object* v_borrows_4665_; lean_object* v_vars_4666_; lean_object* v_borrows_4667_; lean_object* v___y_4669_; lean_object* v_size_4678_; lean_object* v_buckets_4679_; lean_object* v_size_4680_; uint8_t v___x_4681_; 
v___x_4662_ = lean_array_uget_borrowed(v_as_4650_, v_i_4651_);
v_snd_4663_ = lean_ctor_get(v___x_4662_, 1);
v_vars_4664_ = lean_ctor_get(v_b_4653_, 0);
lean_inc_ref(v_vars_4664_);
v_borrows_4665_ = lean_ctor_get(v_b_4653_, 1);
lean_inc_ref(v_borrows_4665_);
lean_dec_ref(v_b_4653_);
v_vars_4666_ = lean_ctor_get(v_snd_4663_, 0);
v_borrows_4667_ = lean_ctor_get(v_snd_4663_, 1);
v_size_4678_ = lean_ctor_get(v_vars_4664_, 0);
v_buckets_4679_ = lean_ctor_get(v_vars_4664_, 1);
v_size_4680_ = lean_ctor_get(v_vars_4666_, 0);
v___x_4681_ = lean_nat_dec_le(v_size_4678_, v_size_4680_);
if (v___x_4681_ == 0)
{
lean_object* v___x_4682_; 
v___x_4682_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_vars_4664_, v_vars_4666_);
v___y_4669_ = v___x_4682_;
goto v___jp_4668_;
}
else
{
size_t v_sz_4683_; size_t v___x_4684_; lean_object* v___x_4685_; 
lean_inc_ref(v_buckets_4679_);
lean_dec_ref(v_vars_4664_);
v_sz_4683_ = lean_array_size(v_buckets_4679_);
v___x_4684_ = ((size_t)0ULL);
lean_inc_ref(v_vars_4666_);
v___x_4685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_buckets_4679_, v_sz_4683_, v___x_4684_, v_vars_4666_);
lean_dec_ref(v_buckets_4679_);
v___y_4669_ = v___x_4685_;
goto v___jp_4668_;
}
v___jp_4668_:
{
lean_object* v_size_4670_; lean_object* v_buckets_4671_; lean_object* v_size_4672_; uint8_t v___x_4673_; 
v_size_4670_ = lean_ctor_get(v_borrows_4665_, 0);
v_buckets_4671_ = lean_ctor_get(v_borrows_4665_, 1);
v_size_4672_ = lean_ctor_get(v_borrows_4667_, 0);
v___x_4673_ = lean_nat_dec_le(v_size_4670_, v_size_4672_);
if (v___x_4673_ == 0)
{
lean_object* v___x_4674_; 
v___x_4674_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1(v_borrows_4665_, v_borrows_4667_);
v___y_4655_ = v___y_4669_;
v___y_4656_ = v___x_4674_;
goto v___jp_4654_;
}
else
{
size_t v_sz_4675_; size_t v___x_4676_; lean_object* v___x_4677_; 
lean_inc_ref(v_buckets_4671_);
lean_dec_ref(v_borrows_4665_);
v_sz_4675_ = lean_array_size(v_buckets_4671_);
v___x_4676_ = ((size_t)0ULL);
lean_inc_ref(v_borrows_4667_);
v___x_4677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__2(v_buckets_4671_, v_sz_4675_, v___x_4676_, v_borrows_4667_);
lean_dec_ref(v_buckets_4671_);
v___y_4655_ = v___y_4669_;
v___y_4656_ = v___x_4677_;
goto v___jp_4654_;
}
}
}
else
{
return v_b_4653_;
}
v___jp_4654_:
{
lean_object* v___x_4657_; size_t v___x_4658_; size_t v___x_4659_; 
v___x_4657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4657_, 0, v___y_4655_);
lean_ctor_set(v___x_4657_, 1, v___y_4656_);
v___x_4658_ = ((size_t)1ULL);
v___x_4659_ = lean_usize_add(v_i_4651_, v___x_4658_);
v_i_4651_ = v___x_4659_;
v_b_4653_ = v___x_4657_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8___boxed(lean_object* v_as_4686_, lean_object* v_i_4687_, lean_object* v_stop_4688_, lean_object* v_b_4689_){
_start:
{
size_t v_i_boxed_4690_; size_t v_stop_boxed_4691_; lean_object* v_res_4692_; 
v_i_boxed_4690_ = lean_unbox_usize(v_i_4687_);
lean_dec(v_i_4687_);
v_stop_boxed_4691_ = lean_unbox_usize(v_stop_4688_);
lean_dec(v_stop_4688_);
v_res_4692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_as_4686_, v_i_boxed_4690_, v_stop_boxed_4691_, v_b_4689_);
lean_dec_ref(v_as_4686_);
return v_res_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(lean_object* v_as_4693_, size_t v_i_4694_, size_t v_stop_4695_, lean_object* v_b_4696_){
_start:
{
lean_object* v___y_4698_; uint8_t v___x_4702_; 
v___x_4702_ = lean_usize_dec_eq(v_i_4694_, v_stop_4695_);
if (v___x_4702_ == 0)
{
lean_object* v_resetTargets_4703_; lean_object* v_unconditionalBorrows_4704_; lean_object* v_derivedValMap_4705_; lean_object* v_varMap_4706_; lean_object* v_jpLiveVarMap_4707_; lean_object* v_idx_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4729_; 
v_resetTargets_4703_ = lean_ctor_get(v_b_4696_, 0);
v_unconditionalBorrows_4704_ = lean_ctor_get(v_b_4696_, 1);
v_derivedValMap_4705_ = lean_ctor_get(v_b_4696_, 2);
v_varMap_4706_ = lean_ctor_get(v_b_4696_, 3);
v_jpLiveVarMap_4707_ = lean_ctor_get(v_b_4696_, 4);
v_idx_4708_ = lean_ctor_get(v_b_4696_, 5);
v_isSharedCheck_4729_ = !lean_is_exclusive(v_b_4696_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4710_ = v_b_4696_;
v_isShared_4711_ = v_isSharedCheck_4729_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_idx_4708_);
lean_inc(v_jpLiveVarMap_4707_);
lean_inc(v_varMap_4706_);
lean_inc(v_derivedValMap_4705_);
lean_inc(v_unconditionalBorrows_4704_);
lean_inc(v_resetTargets_4703_);
lean_dec(v_b_4696_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4729_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4712_; lean_object* v_fvarId_4713_; lean_object* v_type_4714_; uint8_t v_borrow_4715_; uint8_t v___x_4716_; uint8_t v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v_varMap_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v_ctx_4724_; 
v___x_4712_ = lean_array_uget_borrowed(v_as_4693_, v_i_4694_);
v_fvarId_4713_ = lean_ctor_get(v___x_4712_, 0);
v_type_4714_ = lean_ctor_get(v___x_4712_, 2);
v_borrow_4715_ = lean_ctor_get_uint8(v___x_4712_, sizeof(void*)*3);
v___x_4716_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_4714_);
v___x_4717_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_4714_);
v___x_4718_ = lean_box(0);
lean_inc(v_idx_4708_);
v___x_4719_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_4719_, 0, v_idx_4708_);
lean_ctor_set(v___x_4719_, 1, v___x_4718_);
lean_ctor_set_uint8(v___x_4719_, sizeof(void*)*2, v___x_4716_);
lean_ctor_set_uint8(v___x_4719_, sizeof(void*)*2 + 1, v___x_4717_);
lean_ctor_set_uint8(v___x_4719_, sizeof(void*)*2 + 2, v___x_4702_);
lean_inc(v_fvarId_4713_);
v_varMap_4720_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_4713_, v___x_4719_, v_varMap_4706_);
v___x_4721_ = lean_unsigned_to_nat(1u);
v___x_4722_ = lean_nat_add(v_idx_4708_, v___x_4721_);
lean_dec(v_idx_4708_);
if (v_isShared_4711_ == 0)
{
lean_ctor_set(v___x_4710_, 5, v___x_4722_);
lean_ctor_set(v___x_4710_, 3, v_varMap_4720_);
v_ctx_4724_ = v___x_4710_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_resetTargets_4703_);
lean_ctor_set(v_reuseFailAlloc_4728_, 1, v_unconditionalBorrows_4704_);
lean_ctor_set(v_reuseFailAlloc_4728_, 2, v_derivedValMap_4705_);
lean_ctor_set(v_reuseFailAlloc_4728_, 3, v_varMap_4720_);
lean_ctor_set(v_reuseFailAlloc_4728_, 4, v_jpLiveVarMap_4707_);
lean_ctor_set(v_reuseFailAlloc_4728_, 5, v___x_4722_);
v_ctx_4724_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
lean_object* v___x_4725_; lean_object* v_ctx_4726_; 
v___x_4725_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue___closed__0));
lean_inc(v_fvarId_4713_);
v_ctx_4726_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue(v_ctx_4724_, v___x_4725_, v_fvarId_4713_);
if (v_borrow_4715_ == 0)
{
v___y_4698_ = v_ctx_4726_;
goto v___jp_4697_;
}
else
{
if (v___x_4716_ == 0)
{
v___y_4698_ = v_ctx_4726_;
goto v___jp_4697_;
}
else
{
lean_object* v___x_4727_; 
lean_inc(v_fvarId_4713_);
v___x_4727_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addUnconditionalBorrow(v_ctx_4726_, v_fvarId_4713_);
v___y_4698_ = v___x_4727_;
goto v___jp_4697_;
}
}
}
}
}
else
{
return v_b_4696_;
}
v___jp_4697_:
{
size_t v___x_4699_; size_t v___x_4700_; 
v___x_4699_ = ((size_t)1ULL);
v___x_4700_ = lean_usize_add(v_i_4694_, v___x_4699_);
v_i_4694_ = v___x_4700_;
v_b_4696_ = v___y_4698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3___boxed(lean_object* v_as_4730_, lean_object* v_i_4731_, lean_object* v_stop_4732_, lean_object* v_b_4733_){
_start:
{
size_t v_i_boxed_4734_; size_t v_stop_boxed_4735_; lean_object* v_res_4736_; 
v_i_boxed_4734_ = lean_unbox_usize(v_i_4731_);
lean_dec(v_i_4731_);
v_stop_boxed_4735_ = lean_unbox_usize(v_stop_4732_);
lean_dec(v_stop_4732_);
v_res_4736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_as_4730_, v_i_boxed_4734_, v_stop_boxed_4735_, v_b_4733_);
lean_dec_ref(v_as_4730_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4_spec__7(lean_object* v_msg_4737_){
_start:
{
lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4738_ = l_Lean_Compiler_LCNF_instInhabitedLiveVars_default;
v___x_4739_ = lean_panic_fn_borrowed(v___x_4738_, v_msg_4737_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(lean_object* v_t_4740_, lean_object* v_k_4741_){
_start:
{
if (lean_obj_tag(v_t_4740_) == 0)
{
lean_object* v_k_4742_; lean_object* v_v_4743_; lean_object* v_l_4744_; lean_object* v_r_4745_; uint8_t v___x_4746_; 
v_k_4742_ = lean_ctor_get(v_t_4740_, 1);
v_v_4743_ = lean_ctor_get(v_t_4740_, 2);
v_l_4744_ = lean_ctor_get(v_t_4740_, 3);
v_r_4745_ = lean_ctor_get(v_t_4740_, 4);
v___x_4746_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4741_, v_k_4742_);
switch(v___x_4746_)
{
case 0:
{
v_t_4740_ = v_l_4744_;
goto _start;
}
case 1:
{
lean_inc(v_v_4743_);
return v_v_4743_;
}
default: 
{
v_t_4740_ = v_r_4745_;
goto _start;
}
}
}
else
{
lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4749_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDescendants___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs_spec__1_spec__1_spec__2___closed__3);
v___x_4750_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4_spec__7(v___x_4749_);
return v___x_4750_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4___boxed(lean_object* v_t_4751_, lean_object* v_k_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(v_t_4751_, v_k_4752_);
lean_dec(v_k_4752_);
lean_dec(v_t_4751_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(lean_object* v_discr_4754_, size_t v_sz_4755_, size_t v_i_4756_, lean_object* v_bs_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_){
_start:
{
uint8_t v___x_4765_; 
v___x_4765_ = lean_usize_dec_lt(v_i_4756_, v_sz_4755_);
if (v___x_4765_ == 0)
{
lean_object* v___x_4766_; 
lean_dec(v_discr_4754_);
v___x_4766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4766_, 0, v_bs_4757_);
return v___x_4766_;
}
else
{
lean_object* v_v_4767_; lean_object* v_fst_4768_; lean_object* v_snd_4769_; lean_object* v___x_4770_; lean_object* v_bs_x27_4771_; lean_object* v_a_4773_; 
v_v_4767_ = lean_array_uget_borrowed(v_bs_4757_, v_i_4756_);
v_fst_4768_ = lean_ctor_get(v_v_4767_, 0);
lean_inc(v_fst_4768_);
v_snd_4769_ = lean_ctor_get(v_v_4767_, 1);
lean_inc(v_snd_4769_);
v___x_4770_ = lean_unsigned_to_nat(0u);
v_bs_x27_4771_ = lean_array_uset(v_bs_4757_, v_i_4756_, v___x_4770_);
if (lean_obj_tag(v_fst_4768_) == 1)
{
lean_object* v_info_4778_; lean_object* v_code_4779_; lean_object* v_resetTargets_4780_; lean_object* v_unconditionalBorrows_4781_; lean_object* v_derivedValMap_4782_; lean_object* v_varMap_4783_; lean_object* v_jpLiveVarMap_4784_; lean_object* v_idx_4785_; lean_object* v___y_4787_; lean_object* v___x_4802_; 
v_info_4778_ = lean_ctor_get(v_fst_4768_, 0);
v_code_4779_ = lean_ctor_get(v_fst_4768_, 1);
v_resetTargets_4780_ = lean_ctor_get(v___y_4758_, 0);
v_unconditionalBorrows_4781_ = lean_ctor_get(v___y_4758_, 1);
v_derivedValMap_4782_ = lean_ctor_get(v___y_4758_, 2);
v_varMap_4783_ = lean_ctor_get(v___y_4758_, 3);
v_jpLiveVarMap_4784_ = lean_ctor_get(v___y_4758_, 4);
v_idx_4785_ = lean_ctor_get(v___y_4758_, 5);
v___x_4802_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_varMap_4783_, v_discr_4754_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_inc(v_varMap_4783_);
v___y_4787_ = v_varMap_4783_;
goto v___jp_4786_;
}
else
{
lean_object* v_val_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4824_; 
v_val_4803_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4805_ = v___x_4802_;
v_isShared_4806_ = v_isSharedCheck_4824_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_val_4803_);
lean_dec(v___x_4802_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4824_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
uint8_t v_persistent_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4821_; 
v_persistent_4807_ = lean_ctor_get_uint8(v_val_4803_, sizeof(void*)*2 + 2);
v_isSharedCheck_4821_ = !lean_is_exclusive(v_val_4803_);
if (v_isSharedCheck_4821_ == 0)
{
lean_object* v_unused_4822_; lean_object* v_unused_4823_; 
v_unused_4822_ = lean_ctor_get(v_val_4803_, 1);
lean_dec(v_unused_4822_);
v_unused_4823_ = lean_ctor_get(v_val_4803_, 0);
lean_dec(v_unused_4823_);
v___x_4809_ = v_val_4803_;
v_isShared_4810_ = v_isSharedCheck_4821_;
goto v_resetjp_4808_;
}
else
{
lean_dec(v_val_4803_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4821_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
uint8_t v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4815_; 
v___x_4811_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_info_4778_);
v___x_4812_ = lean_unsigned_to_nat(1u);
v___x_4813_ = lean_nat_add(v_idx_4785_, v___x_4812_);
lean_inc_ref(v_info_4778_);
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 0, v_info_4778_);
v___x_4815_ = v___x_4805_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_info_4778_);
v___x_4815_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
lean_object* v___x_4817_; 
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 1, v___x_4815_);
lean_ctor_set(v___x_4809_, 0, v___x_4813_);
v___x_4817_ = v___x_4809_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4813_);
lean_ctor_set(v_reuseFailAlloc_4819_, 1, v___x_4815_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, sizeof(void*)*2 + 2, v_persistent_4807_);
v___x_4817_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
lean_object* v___x_4818_; 
lean_ctor_set_uint8(v___x_4817_, sizeof(void*)*2, v___x_4811_);
lean_ctor_set_uint8(v___x_4817_, sizeof(void*)*2 + 1, v___x_4811_);
lean_inc(v_varMap_4783_);
lean_inc(v_discr_4754_);
v___x_4818_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_4754_, v___x_4817_, v_varMap_4783_);
v___y_4787_ = v___x_4818_;
goto v___jp_4786_;
}
}
}
}
}
v___jp_4786_:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4788_ = lean_unsigned_to_nat(1u);
v___x_4789_ = lean_nat_add(v_idx_4785_, v___x_4788_);
lean_inc(v_jpLiveVarMap_4784_);
lean_inc(v_derivedValMap_4782_);
lean_inc(v_unconditionalBorrows_4781_);
lean_inc_ref(v_resetTargets_4780_);
v___x_4790_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4790_, 0, v_resetTargets_4780_);
lean_ctor_set(v___x_4790_, 1, v_unconditionalBorrows_4781_);
lean_ctor_set(v___x_4790_, 2, v_derivedValMap_4782_);
lean_ctor_set(v___x_4790_, 3, v___y_4787_);
lean_ctor_set(v___x_4790_, 4, v_jpLiveVarMap_4784_);
lean_ctor_set(v___x_4790_, 5, v___x_4789_);
lean_inc_ref(v_code_4779_);
v___x_4791_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_snd_4769_, v_code_4779_, v___x_4790_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
lean_dec_ref_known(v___x_4790_, 6);
lean_dec(v_snd_4769_);
if (lean_obj_tag(v___x_4791_) == 0)
{
lean_object* v_a_4792_; lean_object* v___x_4793_; 
v_a_4792_ = lean_ctor_get(v___x_4791_, 0);
lean_inc(v_a_4792_);
lean_dec_ref_known(v___x_4791_, 1);
v___x_4793_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_fst_4768_, v_a_4792_);
v_a_4773_ = v___x_4793_;
goto v___jp_4772_;
}
else
{
lean_object* v_a_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4801_; 
lean_dec_ref_known(v_fst_4768_, 2);
lean_dec_ref(v_bs_x27_4771_);
lean_dec(v_discr_4754_);
v_a_4794_ = lean_ctor_get(v___x_4791_, 0);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4796_ = v___x_4791_;
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_a_4794_);
lean_dec(v___x_4791_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4799_; 
if (v_isShared_4797_ == 0)
{
v___x_4799_ = v___x_4796_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_a_4794_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
}
}
else
{
lean_object* v_code_4825_; lean_object* v___x_4826_; 
v_code_4825_ = lean_ctor_get(v_fst_4768_, 0);
lean_inc_ref(v_code_4825_);
v___x_4826_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addPrologForAlt(v_snd_4769_, v_code_4825_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
lean_dec(v_snd_4769_);
if (lean_obj_tag(v___x_4826_) == 0)
{
lean_object* v_a_4827_; lean_object* v___x_4828_; 
v_a_4827_ = lean_ctor_get(v___x_4826_, 0);
lean_inc(v_a_4827_);
lean_dec_ref_known(v___x_4826_, 1);
v___x_4828_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_fst_4768_, v_a_4827_);
v_a_4773_ = v___x_4828_;
goto v___jp_4772_;
}
else
{
lean_object* v_a_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4836_; 
lean_dec_ref_known(v_fst_4768_, 1);
lean_dec_ref(v_bs_x27_4771_);
lean_dec(v_discr_4754_);
v_a_4829_ = lean_ctor_get(v___x_4826_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4826_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4831_ = v___x_4826_;
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_a_4829_);
lean_dec(v___x_4826_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4834_; 
if (v_isShared_4832_ == 0)
{
v___x_4834_ = v___x_4831_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
v___jp_4772_:
{
size_t v___x_4774_; size_t v___x_4775_; lean_object* v___x_4776_; 
v___x_4774_ = ((size_t)1ULL);
v___x_4775_ = lean_usize_add(v_i_4756_, v___x_4774_);
v___x_4776_ = lean_array_uset(v_bs_x27_4771_, v_i_4756_, v_a_4773_);
v_i_4756_ = v___x_4775_;
v_bs_4757_ = v___x_4776_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7___boxed(lean_object* v_discr_4837_, lean_object* v_sz_4838_, lean_object* v_i_4839_, lean_object* v_bs_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
size_t v_sz_boxed_4848_; size_t v_i_boxed_4849_; lean_object* v_res_4850_; 
v_sz_boxed_4848_ = lean_unbox_usize(v_sz_4838_);
lean_dec(v_sz_4838_);
v_i_boxed_4849_ = lean_unbox_usize(v_i_4839_);
lean_dec(v_i_4839_);
v_res_4850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(v_discr_4837_, v_sz_boxed_4848_, v_i_boxed_4849_, v_bs_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_);
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
lean_dec(v___y_4844_);
lean_dec_ref(v___y_4843_);
lean_dec(v___y_4842_);
lean_dec_ref(v___y_4841_);
return v_res_4850_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1(void){
_start:
{
lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4852_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__2));
v___x_4853_ = lean_unsigned_to_nat(59u);
v___x_4854_ = lean_unsigned_to_nat(655u);
v___x_4855_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__0));
v___x_4856_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets_go___closed__0));
v___x_4857_ = l_mkPanicMessageWithDecl(v___x_4856_, v___x_4855_, v___x_4854_, v___x_4853_, v___x_4852_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(lean_object* v_code_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_){
_start:
{
switch(lean_obj_tag(v_code_4858_))
{
case 0:
{
lean_object* v_decl_4866_; lean_object* v_k_4867_; lean_object* v_fvarId_4868_; lean_object* v_type_4869_; lean_object* v_value_4870_; lean_object* v___y_4872_; 
v_decl_4866_ = lean_ctor_get(v_code_4858_, 0);
lean_inc_ref(v_decl_4866_);
v_k_4867_ = lean_ctor_get(v_code_4858_, 1);
v_fvarId_4868_ = lean_ctor_get(v_decl_4866_, 0);
v_type_4869_ = lean_ctor_get(v_decl_4866_, 2);
v_value_4870_ = lean_ctor_get(v_decl_4866_, 3);
if (lean_obj_tag(v_value_4870_) == 5)
{
lean_object* v_i_4891_; lean_object* v___x_4892_; 
v_i_4891_ = lean_ctor_get(v_value_4870_, 0);
lean_inc_ref(v_i_4891_);
v___x_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4892_, 0, v_i_4891_);
v___y_4872_ = v___x_4892_;
goto v___jp_4871_;
}
else
{
lean_object* v___x_4893_; 
v___x_4893_ = lean_box(0);
v___y_4872_ = v___x_4893_;
goto v___jp_4871_;
}
v___jp_4871_:
{
lean_object* v_resetTargets_4873_; lean_object* v_unconditionalBorrows_4874_; lean_object* v_derivedValMap_4875_; lean_object* v_varMap_4876_; lean_object* v_jpLiveVarMap_4877_; lean_object* v_idx_4878_; uint8_t v___x_4879_; uint8_t v___x_4880_; uint8_t v___x_4881_; lean_object* v_varInfo_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v_ctx_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
v_resetTargets_4873_ = lean_ctor_get(v_a_4859_, 0);
v_unconditionalBorrows_4874_ = lean_ctor_get(v_a_4859_, 1);
v_derivedValMap_4875_ = lean_ctor_get(v_a_4859_, 2);
v_varMap_4876_ = lean_ctor_get(v_a_4859_, 3);
v_jpLiveVarMap_4877_ = lean_ctor_get(v_a_4859_, 4);
v_idx_4878_ = lean_ctor_get(v_a_4859_, 5);
v___x_4879_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_4869_);
v___x_4880_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isDefiniteRef(v_type_4869_);
v___x_4881_ = l_Lean_Compiler_LCNF_LetValue_isPersistent(v_value_4870_);
lean_inc(v_idx_4878_);
v_varInfo_4882_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_varInfo_4882_, 0, v_idx_4878_);
lean_ctor_set(v_varInfo_4882_, 1, v___y_4872_);
lean_ctor_set_uint8(v_varInfo_4882_, sizeof(void*)*2, v___x_4879_);
lean_ctor_set_uint8(v_varInfo_4882_, sizeof(void*)*2 + 1, v___x_4880_);
lean_ctor_set_uint8(v_varInfo_4882_, sizeof(void*)*2 + 2, v___x_4881_);
lean_inc(v_varMap_4876_);
lean_inc(v_fvarId_4868_);
v___x_4883_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_4868_, v_varInfo_4882_, v_varMap_4876_);
v___x_4884_ = lean_unsigned_to_nat(1u);
v___x_4885_ = lean_nat_add(v_idx_4878_, v___x_4884_);
lean_inc(v_jpLiveVarMap_4877_);
lean_inc(v_derivedValMap_4875_);
lean_inc(v_unconditionalBorrows_4874_);
lean_inc_ref(v_resetTargets_4873_);
v_ctx_4886_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_ctx_4886_, 0, v_resetTargets_4873_);
lean_ctor_set(v_ctx_4886_, 1, v_unconditionalBorrows_4874_);
lean_ctor_set(v_ctx_4886_, 2, v_derivedValMap_4875_);
lean_ctor_set(v_ctx_4886_, 3, v___x_4883_);
lean_ctor_set(v_ctx_4886_, 4, v_jpLiveVarMap_4877_);
lean_ctor_set(v_ctx_4886_, 5, v___x_4885_);
lean_inc_ref(v_decl_4866_);
v___x_4887_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetDecl(v_ctx_4886_, v_decl_4866_);
lean_inc_ref(v_k_4867_);
v___x_4888_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_4867_, v___x_4887_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v___x_4890_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc(v_a_4889_);
lean_dec_ref_known(v___x_4888_, 1);
v___x_4890_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc(v_code_4858_, v_decl_4866_, v_a_4889_, v___x_4887_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
lean_dec_ref(v___x_4887_);
return v___x_4890_;
}
else
{
lean_dec_ref(v___x_4887_);
lean_dec_ref_known(v_code_4858_, 2);
lean_dec_ref(v_decl_4866_);
return v___x_4888_;
}
}
}
case 2:
{
lean_object* v_decl_4894_; lean_object* v_k_4895_; lean_object* v_fst_4897_; lean_object* v_snd_4898_; lean_object* v_params_4947_; lean_object* v_type_4948_; lean_object* v_value_4949_; uint8_t v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; uint8_t v___x_4953_; 
v_decl_4894_ = lean_ctor_get(v_code_4858_, 0);
v_k_4895_ = lean_ctor_get(v_code_4858_, 1);
v_params_4947_ = lean_ctor_get(v_decl_4894_, 2);
v_type_4948_ = lean_ctor_get(v_decl_4894_, 3);
v_value_4949_ = lean_ctor_get(v_decl_4894_, 4);
v___x_4950_ = 1;
v___x_4951_ = lean_unsigned_to_nat(0u);
v___x_4952_ = lean_array_get_size(v_params_4947_);
v___x_4953_ = lean_nat_dec_lt(v___x_4951_, v___x_4952_);
if (v___x_4953_ == 0)
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4954_ = lean_st_ref_get(v_a_4860_);
v___x_4955_ = lean_st_ref_take(v_a_4860_);
lean_dec(v___x_4955_);
v___x_4956_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_4957_ = lean_st_ref_put(v_a_4860_, v___x_4956_);
lean_inc_ref(v_value_4949_);
v___x_4958_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_value_4949_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4960_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4959_);
lean_dec_ref_known(v___x_4958_, 1);
v___x_4960_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_4947_, v_a_4959_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; lean_object* v___x_4962_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
lean_inc_ref(v_params_4947_);
lean_inc_ref(v_type_4948_);
lean_inc_ref(v_decl_4894_);
v___x_4962_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_4950_, v_decl_4894_, v_type_4948_, v_params_4947_, v_a_4961_, v_a_4862_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_a_4963_);
lean_dec_ref_known(v___x_4962_, 1);
v___x_4964_ = lean_st_ref_get(v_a_4860_);
v___x_4965_ = lean_st_ref_take(v_a_4860_);
lean_dec(v___x_4965_);
v___x_4966_ = lean_st_ref_put(v_a_4860_, v___x_4954_);
v_fst_4897_ = v_a_4963_;
v_snd_4898_ = v___x_4964_;
goto v___jp_4896_;
}
else
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4974_; 
lean_dec(v___x_4954_);
lean_dec_ref_known(v_code_4858_, 2);
v_a_4967_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4962_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4962_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4972_; 
if (v_isShared_4970_ == 0)
{
v___x_4972_ = v___x_4969_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4967_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
}
else
{
lean_dec(v___x_4954_);
lean_dec_ref_known(v_code_4858_, 2);
return v___x_4960_;
}
}
else
{
lean_dec(v___x_4954_);
lean_dec_ref_known(v_code_4858_, 2);
return v___x_4958_;
}
}
else
{
size_t v___x_4975_; size_t v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4975_ = ((size_t)0ULL);
v___x_4976_ = lean_usize_of_nat(v___x_4952_);
lean_inc_ref(v_a_4859_);
v___x_4977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_params_4947_, v___x_4975_, v___x_4976_, v_a_4859_);
v___x_4978_ = lean_st_ref_get(v_a_4860_);
v___x_4979_ = lean_st_ref_take(v_a_4860_);
lean_dec(v___x_4979_);
v___x_4980_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_4981_ = lean_st_ref_put(v_a_4860_, v___x_4980_);
lean_inc_ref(v_value_4949_);
v___x_4982_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_value_4949_, v___x_4977_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4984_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
lean_inc(v_a_4983_);
lean_dec_ref_known(v___x_4982_, 1);
v___x_4984_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_4947_, v_a_4983_, v___x_4977_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
lean_dec_ref(v___x_4977_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v_a_4985_; lean_object* v___x_4986_; 
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
lean_inc(v_a_4985_);
lean_dec_ref_known(v___x_4984_, 1);
lean_inc_ref(v_params_4947_);
lean_inc_ref(v_type_4948_);
lean_inc_ref(v_decl_4894_);
v___x_4986_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_4950_, v_decl_4894_, v_type_4948_, v_params_4947_, v_a_4985_, v_a_4862_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4986_, 1);
v___x_4988_ = lean_st_ref_get(v_a_4860_);
v___x_4989_ = lean_st_ref_take(v_a_4860_);
lean_dec(v___x_4989_);
v___x_4990_ = lean_st_ref_put(v_a_4860_, v___x_4978_);
v_fst_4897_ = v_a_4987_;
v_snd_4898_ = v___x_4988_;
goto v___jp_4896_;
}
else
{
lean_object* v_a_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_4998_; 
lean_dec(v___x_4978_);
lean_dec_ref_known(v_code_4858_, 2);
v_a_4991_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4993_ = v___x_4986_;
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_a_4991_);
lean_dec(v___x_4986_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v___x_4996_; 
if (v_isShared_4994_ == 0)
{
v___x_4996_ = v___x_4993_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_a_4991_);
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
lean_dec(v___x_4978_);
lean_dec_ref_known(v_code_4858_, 2);
return v___x_4984_;
}
}
else
{
lean_dec(v___x_4978_);
lean_dec_ref(v___x_4977_);
lean_dec_ref_known(v_code_4858_, 2);
return v___x_4982_;
}
}
v___jp_4896_:
{
lean_object* v_fvarId_4899_; lean_object* v_resetTargets_4900_; lean_object* v_unconditionalBorrows_4901_; lean_object* v_derivedValMap_4902_; lean_object* v_varMap_4903_; lean_object* v_jpLiveVarMap_4904_; lean_object* v_idx_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; 
v_fvarId_4899_ = lean_ctor_get(v_fst_4897_, 0);
v_resetTargets_4900_ = lean_ctor_get(v_a_4859_, 0);
v_unconditionalBorrows_4901_ = lean_ctor_get(v_a_4859_, 1);
v_derivedValMap_4902_ = lean_ctor_get(v_a_4859_, 2);
v_varMap_4903_ = lean_ctor_get(v_a_4859_, 3);
v_jpLiveVarMap_4904_ = lean_ctor_get(v_a_4859_, 4);
v_idx_4905_ = lean_ctor_get(v_a_4859_, 5);
lean_inc(v_jpLiveVarMap_4904_);
lean_inc(v_fvarId_4899_);
v___x_4906_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_4899_, v_snd_4898_, v_jpLiveVarMap_4904_);
lean_inc(v_idx_4905_);
lean_inc(v_varMap_4903_);
lean_inc(v_derivedValMap_4902_);
lean_inc(v_unconditionalBorrows_4901_);
lean_inc_ref(v_resetTargets_4900_);
v___x_4907_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4907_, 0, v_resetTargets_4900_);
lean_ctor_set(v___x_4907_, 1, v_unconditionalBorrows_4901_);
lean_ctor_set(v___x_4907_, 2, v_derivedValMap_4902_);
lean_ctor_set(v___x_4907_, 3, v_varMap_4903_);
lean_ctor_set(v___x_4907_, 4, v___x_4906_);
lean_ctor_set(v___x_4907_, 5, v_idx_4905_);
lean_inc_ref(v_k_4895_);
v___x_4908_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_4895_, v___x_4907_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
lean_dec_ref_known(v___x_4907_, 6);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4946_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4911_ = v___x_4908_;
v_isShared_4912_ = v_isSharedCheck_4946_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_a_4909_);
lean_dec(v___x_4908_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4946_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
size_t v___x_4913_; size_t v___x_4914_; uint8_t v___x_4915_; 
v___x_4913_ = lean_ptr_addr(v_k_4895_);
v___x_4914_ = lean_ptr_addr(v_a_4909_);
v___x_4915_ = lean_usize_dec_eq(v___x_4913_, v___x_4914_);
if (v___x_4915_ == 0)
{
lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4925_; 
v_isSharedCheck_4925_ = !lean_is_exclusive(v_code_4858_);
if (v_isSharedCheck_4925_ == 0)
{
lean_object* v_unused_4926_; lean_object* v_unused_4927_; 
v_unused_4926_ = lean_ctor_get(v_code_4858_, 1);
lean_dec(v_unused_4926_);
v_unused_4927_ = lean_ctor_get(v_code_4858_, 0);
lean_dec(v_unused_4927_);
v___x_4917_ = v_code_4858_;
v_isShared_4918_ = v_isSharedCheck_4925_;
goto v_resetjp_4916_;
}
else
{
lean_dec(v_code_4858_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4925_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
lean_ctor_set(v___x_4917_, 1, v_a_4909_);
lean_ctor_set(v___x_4917_, 0, v_fst_4897_);
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_fst_4897_);
lean_ctor_set(v_reuseFailAlloc_4924_, 1, v_a_4909_);
v___x_4920_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
lean_object* v___x_4922_; 
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 0, v___x_4920_);
v___x_4922_ = v___x_4911_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v___x_4920_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
else
{
size_t v___x_4928_; size_t v___x_4929_; uint8_t v___x_4930_; 
v___x_4928_ = lean_ptr_addr(v_decl_4894_);
v___x_4929_ = lean_ptr_addr(v_fst_4897_);
v___x_4930_ = lean_usize_dec_eq(v___x_4928_, v___x_4929_);
if (v___x_4930_ == 0)
{
lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4940_; 
v_isSharedCheck_4940_ = !lean_is_exclusive(v_code_4858_);
if (v_isSharedCheck_4940_ == 0)
{
lean_object* v_unused_4941_; lean_object* v_unused_4942_; 
v_unused_4941_ = lean_ctor_get(v_code_4858_, 1);
lean_dec(v_unused_4941_);
v_unused_4942_ = lean_ctor_get(v_code_4858_, 0);
lean_dec(v_unused_4942_);
v___x_4932_ = v_code_4858_;
v_isShared_4933_ = v_isSharedCheck_4940_;
goto v_resetjp_4931_;
}
else
{
lean_dec(v_code_4858_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4940_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 1, v_a_4909_);
lean_ctor_set(v___x_4932_, 0, v_fst_4897_);
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_fst_4897_);
lean_ctor_set(v_reuseFailAlloc_4939_, 1, v_a_4909_);
v___x_4935_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4937_; 
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 0, v___x_4935_);
v___x_4937_ = v___x_4911_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v___x_4935_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
}
else
{
lean_object* v___x_4944_; 
lean_dec(v_a_4909_);
lean_dec_ref(v_fst_4897_);
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 0, v_code_4858_);
v___x_4944_ = v___x_4911_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_code_4858_);
v___x_4944_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
return v___x_4944_;
}
}
}
}
}
else
{
lean_dec_ref(v_fst_4897_);
lean_dec_ref_known(v_code_4858_, 2);
return v___x_4908_;
}
}
}
case 3:
{
lean_object* v_fvarId_4999_; lean_object* v_args_5000_; lean_object* v_jpLiveVarMap_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
v_fvarId_4999_ = lean_ctor_get(v_code_4858_, 0);
v_args_5000_ = lean_ctor_get(v_code_4858_, 1);
lean_inc_ref(v_args_5000_);
v_jpLiveVarMap_5001_ = lean_ctor_get(v_a_4859_, 4);
v___x_5002_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__4(v_jpLiveVarMap_5001_, v_fvarId_4999_);
v___x_5003_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_5002_, v_a_4859_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; uint8_t v___x_5007_; lean_object* v___x_5008_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc(v_a_5004_);
lean_dec_ref_known(v___x_5003_, 1);
v___x_5005_ = lean_st_ref_take(v_a_4860_);
lean_dec(v___x_5005_);
v___x_5006_ = lean_st_ref_put(v_a_4860_, v_a_5004_);
v___x_5007_ = 1;
v___x_5008_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(v___x_5007_, v_fvarId_4999_, v_a_4862_);
if (lean_obj_tag(v___x_5008_) == 0)
{
lean_object* v_a_5009_; lean_object* v___y_5011_; 
v_a_5009_ = lean_ctor_get(v___x_5008_, 0);
lean_inc(v_a_5009_);
lean_dec_ref_known(v___x_5008_, 1);
if (lean_obj_tag(v_a_5009_) == 0)
{
lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5032_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc___closed__11);
v___x_5033_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__5(v___x_5032_);
v___y_5011_ = v___x_5033_;
goto v___jp_5010_;
}
else
{
lean_object* v_val_5034_; 
v_val_5034_ = lean_ctor_get(v_a_5009_, 0);
lean_inc(v_val_5034_);
lean_dec_ref_known(v_a_5009_, 1);
v___y_5011_ = v_val_5034_;
goto v___jp_5010_;
}
v___jp_5010_:
{
lean_object* v_params_5012_; lean_object* v___x_5013_; 
v_params_5012_ = lean_ctor_get(v___y_5011_, 2);
lean_inc_ref(v_params_5012_);
lean_dec_ref(v___y_5011_);
v___x_5013_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addIncBefore(v_args_5000_, v_params_5012_, v_code_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
if (lean_obj_tag(v___x_5013_) == 0)
{
lean_object* v_a_5014_; lean_object* v___x_5015_; 
v_a_5014_ = lean_ctor_get(v___x_5013_, 0);
lean_inc(v_a_5014_);
lean_dec_ref_known(v___x_5013_, 1);
v___x_5015_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useArgs(v_args_5000_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
lean_dec_ref(v_args_5000_);
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5022_; 
v_isSharedCheck_5022_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5022_ == 0)
{
lean_object* v_unused_5023_; 
v_unused_5023_ = lean_ctor_get(v___x_5015_, 0);
lean_dec(v_unused_5023_);
v___x_5017_ = v___x_5015_;
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
else
{
lean_dec(v___x_5015_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5020_; 
if (v_isShared_5018_ == 0)
{
lean_ctor_set(v___x_5017_, 0, v_a_5014_);
v___x_5020_ = v___x_5017_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5014_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
}
else
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
lean_dec(v_a_5014_);
v_a_5024_ = lean_ctor_get(v___x_5015_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_5015_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5026_ = v___x_5015_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_5015_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5024_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
else
{
lean_dec_ref(v_args_5000_);
return v___x_5013_;
}
}
}
else
{
lean_object* v_a_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5042_; 
lean_dec_ref(v_args_5000_);
lean_dec_ref_known(v_code_4858_, 2);
v_a_5035_ = lean_ctor_get(v___x_5008_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5037_ = v___x_5008_;
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_a_5035_);
lean_dec(v___x_5008_);
v___x_5037_ = lean_box(0);
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
v_resetjp_5036_:
{
lean_object* v___x_5040_; 
if (v_isShared_5038_ == 0)
{
v___x_5040_ = v___x_5037_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5035_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
return v___x_5040_;
}
}
}
}
else
{
lean_object* v_a_5043_; lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5050_; 
lean_dec_ref(v_args_5000_);
lean_dec_ref_known(v_code_4858_, 2);
v_a_5043_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5050_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5050_ == 0)
{
v___x_5045_ = v___x_5003_;
v_isShared_5046_ = v_isSharedCheck_5050_;
goto v_resetjp_5044_;
}
else
{
lean_inc(v_a_5043_);
lean_dec(v___x_5003_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5050_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
lean_object* v___x_5048_; 
if (v_isShared_5046_ == 0)
{
v___x_5048_ = v___x_5045_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_a_5043_);
v___x_5048_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
return v___x_5048_;
}
}
}
}
case 4:
{
lean_object* v_cases_5051_; lean_object* v_typeName_5052_; lean_object* v_resultType_5053_; lean_object* v_discr_5054_; lean_object* v_alts_5055_; size_t v_sz_5056_; size_t v___x_5057_; lean_object* v___x_5058_; 
v_cases_5051_ = lean_ctor_get(v_code_4858_, 0);
v_typeName_5052_ = lean_ctor_get(v_cases_5051_, 0);
v_resultType_5053_ = lean_ctor_get(v_cases_5051_, 1);
v_discr_5054_ = lean_ctor_get(v_cases_5051_, 2);
v_alts_5055_ = lean_ctor_get(v_cases_5051_, 3);
v_sz_5056_ = lean_array_size(v_alts_5055_);
v___x_5057_ = ((size_t)0ULL);
lean_inc_ref(v_alts_5055_);
lean_inc_ref(v_cases_5051_);
v___x_5058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(v_cases_5051_, v_sz_5056_, v___x_5057_, v_alts_5055_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_object* v_a_5059_; lean_object* v___y_5061_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; uint8_t v___x_5109_; 
v_a_5059_ = lean_ctor_get(v___x_5058_, 0);
lean_inc(v_a_5059_);
lean_dec_ref_known(v___x_5058_, 1);
v___x_5106_ = lean_unsigned_to_nat(0u);
v___x_5107_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5108_ = lean_array_get_size(v_a_5059_);
v___x_5109_ = lean_nat_dec_lt(v___x_5106_, v___x_5108_);
if (v___x_5109_ == 0)
{
v___y_5061_ = v___x_5107_;
goto v___jp_5060_;
}
else
{
size_t v___x_5110_; lean_object* v___x_5111_; 
v___x_5110_ = lean_usize_of_nat(v___x_5108_);
v___x_5111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__8(v_a_5059_, v___x_5057_, v___x_5110_, v___x_5107_);
v___y_5061_ = v___x_5111_;
goto v___jp_5060_;
}
v___jp_5060_:
{
lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5062_ = lean_st_ref_take(v_a_4860_);
lean_dec(v___x_5062_);
v___x_5063_ = lean_st_ref_put(v_a_4860_, v___y_5061_);
lean_inc(v_discr_5054_);
v___x_5064_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_discr_5054_, v_a_4859_, v_a_4860_);
if (lean_obj_tag(v___x_5064_) == 0)
{
size_t v_sz_5065_; lean_object* v___x_5066_; 
lean_dec_ref_known(v___x_5064_, 1);
v_sz_5065_ = lean_array_size(v_a_5059_);
lean_inc(v_discr_5054_);
v___x_5066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__7(v_discr_5054_, v_sz_5065_, v___x_5057_, v_a_5059_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
if (lean_obj_tag(v___x_5066_) == 0)
{
lean_object* v_a_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5089_; 
v_a_5067_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5069_ = v___x_5066_;
v_isShared_5070_ = v_isSharedCheck_5089_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_a_5067_);
lean_dec(v___x_5066_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5089_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
size_t v___x_5071_; size_t v___x_5072_; uint8_t v___x_5073_; 
v___x_5071_ = lean_ptr_addr(v_alts_5055_);
v___x_5072_ = lean_ptr_addr(v_a_5067_);
v___x_5073_ = lean_usize_dec_eq(v___x_5071_, v___x_5072_);
if (v___x_5073_ == 0)
{
lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5084_; 
lean_inc(v_discr_5054_);
lean_inc_ref(v_resultType_5053_);
lean_inc(v_typeName_5052_);
v_isSharedCheck_5084_ = !lean_is_exclusive(v_code_4858_);
if (v_isSharedCheck_5084_ == 0)
{
lean_object* v_unused_5085_; 
v_unused_5085_ = lean_ctor_get(v_code_4858_, 0);
lean_dec(v_unused_5085_);
v___x_5075_ = v_code_4858_;
v_isShared_5076_ = v_isSharedCheck_5084_;
goto v_resetjp_5074_;
}
else
{
lean_dec(v_code_4858_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5084_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5077_; lean_object* v___x_5079_; 
v___x_5077_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5077_, 0, v_typeName_5052_);
lean_ctor_set(v___x_5077_, 1, v_resultType_5053_);
lean_ctor_set(v___x_5077_, 2, v_discr_5054_);
lean_ctor_set(v___x_5077_, 3, v_a_5067_);
if (v_isShared_5076_ == 0)
{
lean_ctor_set(v___x_5075_, 0, v___x_5077_);
v___x_5079_ = v___x_5075_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v___x_5077_);
v___x_5079_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
lean_object* v___x_5081_; 
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 0, v___x_5079_);
v___x_5081_ = v___x_5069_;
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
lean_object* v___x_5087_; 
lean_dec(v_a_5067_);
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 0, v_code_4858_);
v___x_5087_ = v___x_5069_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_code_4858_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
}
else
{
lean_object* v_a_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5097_; 
lean_dec_ref_known(v_code_4858_, 1);
v_a_5090_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5092_ = v___x_5066_;
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_a_5090_);
lean_dec(v___x_5066_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5095_; 
if (v_isShared_5093_ == 0)
{
v___x_5095_ = v___x_5092_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5090_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
}
}
else
{
lean_object* v_a_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5105_; 
lean_dec(v_a_5059_);
lean_dec_ref_known(v_code_4858_, 1);
v_a_5098_ = lean_ctor_get(v___x_5064_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5100_ = v___x_5064_;
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_a_5098_);
lean_dec(v___x_5064_);
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
}
else
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
lean_dec_ref_known(v_code_4858_, 1);
v_a_5112_ = lean_ctor_get(v___x_5058_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5114_ = v___x_5058_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_5058_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5115_ == 0)
{
v___x_5117_ = v___x_5114_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5112_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v_fvarId_5120_ = lean_ctor_get(v_code_4858_, 0);
v___x_5121_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5122_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_5121_, v_a_4859_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v_varMap_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
lean_inc(v_a_5123_);
lean_dec_ref_known(v___x_5122_, 1);
v___x_5124_ = lean_st_ref_take(v_a_4860_);
lean_dec(v___x_5124_);
v___x_5125_ = lean_st_ref_put(v_a_4860_, v_a_5123_);
v_varMap_5126_ = lean_ctor_get(v_a_4859_, 3);
v___x_5127_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDec_spec__0(v_varMap_5126_, v_fvarId_5120_);
lean_inc(v_fvarId_5120_);
v___x_5128_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_5120_, v_a_4859_, v_a_4860_);
if (lean_obj_tag(v___x_5128_) == 0)
{
lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5152_; 
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5152_ == 0)
{
lean_object* v_unused_5153_; 
v_unused_5153_ = lean_ctor_get(v___x_5128_, 0);
lean_dec(v_unused_5153_);
v___x_5130_ = v___x_5128_;
v_isShared_5131_ = v_isSharedCheck_5152_;
goto v_resetjp_5129_;
}
else
{
lean_dec(v___x_5128_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5152_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v___x_5132_; uint8_t v_isPossibleRef_5133_; 
v___x_5132_ = lean_st_ref_get(v_a_4860_);
v_isPossibleRef_5133_ = lean_ctor_get_uint8(v___x_5127_, sizeof(void*)*2);
if (v_isPossibleRef_5133_ == 0)
{
lean_object* v___x_5135_; 
lean_dec(v___x_5132_);
lean_dec_ref(v___x_5127_);
if (v_isShared_5131_ == 0)
{
lean_ctor_set(v___x_5130_, 0, v_code_4858_);
v___x_5135_ = v___x_5130_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_code_4858_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
else
{
uint8_t v_isDefiniteRef_5137_; uint8_t v_persistent_5138_; lean_object* v_borrows_5139_; uint8_t v___x_5140_; 
v_isDefiniteRef_5137_ = lean_ctor_get_uint8(v___x_5127_, sizeof(void*)*2 + 1);
v_persistent_5138_ = lean_ctor_get_uint8(v___x_5127_, sizeof(void*)*2 + 2);
lean_dec_ref(v___x_5127_);
v_borrows_5139_ = lean_ctor_get(v___x_5132_, 1);
lean_inc_ref(v_borrows_5139_);
lean_dec(v___x_5132_);
v___x_5140_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedValue_spec__2___redArg(v_borrows_5139_, v_fvarId_5120_);
lean_dec_ref(v_borrows_5139_);
if (v___x_5140_ == 0)
{
lean_object* v___x_5142_; 
if (v_isShared_5131_ == 0)
{
lean_ctor_set(v___x_5130_, 0, v_code_4858_);
v___x_5142_ = v___x_5130_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_code_4858_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
else
{
lean_object* v___x_5144_; uint8_t v___y_5146_; 
lean_inc(v_fvarId_5120_);
v___x_5144_ = lean_unsigned_to_nat(1u);
if (v_isDefiniteRef_5137_ == 0)
{
v___y_5146_ = v___x_5140_;
goto v___jp_5145_;
}
else
{
uint8_t v___x_5151_; 
v___x_5151_ = 0;
v___y_5146_ = v___x_5151_;
goto v___jp_5145_;
}
v___jp_5145_:
{
lean_object* v___x_5147_; lean_object* v___x_5149_; 
v___x_5147_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_5147_, 0, v_fvarId_5120_);
lean_ctor_set(v___x_5147_, 1, v___x_5144_);
lean_ctor_set(v___x_5147_, 2, v_code_4858_);
lean_ctor_set_uint8(v___x_5147_, sizeof(void*)*3, v___y_5146_);
lean_ctor_set_uint8(v___x_5147_, sizeof(void*)*3 + 1, v_persistent_5138_);
if (v_isShared_5131_ == 0)
{
lean_ctor_set(v___x_5130_, 0, v___x_5147_);
v___x_5149_ = v___x_5130_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v___x_5147_);
v___x_5149_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
return v___x_5149_;
}
}
}
}
}
}
else
{
lean_object* v_a_5154_; lean_object* v___x_5156_; uint8_t v_isShared_5157_; uint8_t v_isSharedCheck_5161_; 
lean_dec_ref(v___x_5127_);
lean_dec_ref_known(v_code_4858_, 1);
v_a_5154_ = lean_ctor_get(v___x_5128_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5156_ = v___x_5128_;
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
else
{
lean_inc(v_a_5154_);
lean_dec(v___x_5128_);
v___x_5156_ = lean_box(0);
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
v_resetjp_5155_:
{
lean_object* v___x_5159_; 
if (v_isShared_5157_ == 0)
{
v___x_5159_ = v___x_5156_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v_a_5154_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
}
}
}
}
else
{
lean_object* v_a_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5169_; 
lean_dec_ref_known(v_code_4858_, 1);
v_a_5162_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5164_ = v___x_5122_;
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_a_5162_);
lean_dec(v___x_5122_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v___x_5167_; 
if (v_isShared_5165_ == 0)
{
v___x_5167_ = v___x_5164_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5162_);
v___x_5167_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
return v___x_5167_;
}
}
}
}
case 6:
{
lean_object* v___x_5170_; lean_object* v___x_5171_; 
v___x_5170_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5171_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addBorrows___redArg(v___x_5170_, v_a_4859_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5181_; 
v_a_5172_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5174_ = v___x_5171_;
v_isShared_5175_ = v_isSharedCheck_5181_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5171_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5181_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5179_; 
v___x_5176_ = lean_st_ref_take(v_a_4860_);
lean_dec(v___x_5176_);
v___x_5177_ = lean_st_ref_put(v_a_4860_, v_a_5172_);
if (v_isShared_5175_ == 0)
{
lean_ctor_set(v___x_5174_, 0, v_code_4858_);
v___x_5179_ = v___x_5174_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_code_4858_);
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
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
lean_dec_ref_known(v_code_4858_, 1);
v_a_5182_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5184_ = v___x_5171_;
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_5171_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5187_; 
if (v_isShared_5185_ == 0)
{
v___x_5187_ = v___x_5184_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5182_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
case 8:
{
lean_object* v_fvarId_5190_; lean_object* v_i_5191_; lean_object* v_y_5192_; lean_object* v_k_5193_; lean_object* v___x_5194_; 
v_fvarId_5190_ = lean_ctor_get(v_code_4858_, 0);
v_i_5191_ = lean_ctor_get(v_code_4858_, 1);
v_y_5192_ = lean_ctor_get(v_code_4858_, 2);
v_k_5193_ = lean_ctor_get(v_code_4858_, 3);
lean_inc_ref(v_k_5193_);
v___x_5194_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5193_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
if (lean_obj_tag(v___x_5194_) == 0)
{
lean_object* v_a_5195_; lean_object* v___x_5196_; 
v_a_5195_ = lean_ctor_get(v___x_5194_, 0);
lean_inc(v_a_5195_);
lean_dec_ref_known(v___x_5194_, 1);
lean_inc(v_fvarId_5190_);
v___x_5196_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_5190_, v_a_4859_, v_a_4860_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5220_; 
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5220_ == 0)
{
lean_object* v_unused_5221_; 
v_unused_5221_ = lean_ctor_get(v___x_5196_, 0);
lean_dec(v_unused_5221_);
v___x_5198_ = v___x_5196_;
v_isShared_5199_ = v_isSharedCheck_5220_;
goto v_resetjp_5197_;
}
else
{
lean_dec(v___x_5196_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5220_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
size_t v___x_5200_; size_t v___x_5201_; uint8_t v___x_5202_; 
v___x_5200_ = lean_ptr_addr(v_k_5193_);
v___x_5201_ = lean_ptr_addr(v_a_5195_);
v___x_5202_ = lean_usize_dec_eq(v___x_5200_, v___x_5201_);
if (v___x_5202_ == 0)
{
lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5212_; 
lean_inc(v_y_5192_);
lean_inc(v_i_5191_);
lean_inc(v_fvarId_5190_);
v_isSharedCheck_5212_ = !lean_is_exclusive(v_code_4858_);
if (v_isSharedCheck_5212_ == 0)
{
lean_object* v_unused_5213_; lean_object* v_unused_5214_; lean_object* v_unused_5215_; lean_object* v_unused_5216_; 
v_unused_5213_ = lean_ctor_get(v_code_4858_, 3);
lean_dec(v_unused_5213_);
v_unused_5214_ = lean_ctor_get(v_code_4858_, 2);
lean_dec(v_unused_5214_);
v_unused_5215_ = lean_ctor_get(v_code_4858_, 1);
lean_dec(v_unused_5215_);
v_unused_5216_ = lean_ctor_get(v_code_4858_, 0);
lean_dec(v_unused_5216_);
v___x_5204_ = v_code_4858_;
v_isShared_5205_ = v_isSharedCheck_5212_;
goto v_resetjp_5203_;
}
else
{
lean_dec(v_code_4858_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5212_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5207_; 
if (v_isShared_5205_ == 0)
{
lean_ctor_set(v___x_5204_, 3, v_a_5195_);
v___x_5207_ = v___x_5204_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v_fvarId_5190_);
lean_ctor_set(v_reuseFailAlloc_5211_, 1, v_i_5191_);
lean_ctor_set(v_reuseFailAlloc_5211_, 2, v_y_5192_);
lean_ctor_set(v_reuseFailAlloc_5211_, 3, v_a_5195_);
v___x_5207_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
lean_object* v___x_5209_; 
if (v_isShared_5199_ == 0)
{
lean_ctor_set(v___x_5198_, 0, v___x_5207_);
v___x_5209_ = v___x_5198_;
goto v_reusejp_5208_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v___x_5207_);
v___x_5209_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5208_;
}
v_reusejp_5208_:
{
return v___x_5209_;
}
}
}
}
else
{
lean_object* v___x_5218_; 
lean_dec(v_a_5195_);
if (v_isShared_5199_ == 0)
{
lean_ctor_set(v___x_5198_, 0, v_code_4858_);
v___x_5218_ = v___x_5198_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_code_4858_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
return v___x_5218_;
}
}
}
}
else
{
lean_object* v_a_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5229_; 
lean_dec(v_a_5195_);
lean_dec_ref_known(v_code_4858_, 4);
v_a_5222_ = lean_ctor_get(v___x_5196_, 0);
v_isSharedCheck_5229_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5224_ = v___x_5196_;
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_a_5222_);
lean_dec(v___x_5196_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
lean_object* v___x_5227_; 
if (v_isShared_5225_ == 0)
{
v___x_5227_ = v___x_5224_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5222_);
v___x_5227_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
return v___x_5227_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_4858_, 4);
return v___x_5194_;
}
}
case 9:
{
lean_object* v_fvarId_5230_; lean_object* v_i_5231_; lean_object* v_offset_5232_; lean_object* v_y_5233_; lean_object* v_ty_5234_; lean_object* v_k_5235_; lean_object* v___x_5236_; 
v_fvarId_5230_ = lean_ctor_get(v_code_4858_, 0);
v_i_5231_ = lean_ctor_get(v_code_4858_, 1);
v_offset_5232_ = lean_ctor_get(v_code_4858_, 2);
v_y_5233_ = lean_ctor_get(v_code_4858_, 3);
v_ty_5234_ = lean_ctor_get(v_code_4858_, 4);
v_k_5235_ = lean_ctor_get(v_code_4858_, 5);
lean_inc_ref(v_k_5235_);
v___x_5236_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_k_5235_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
if (lean_obj_tag(v___x_5236_) == 0)
{
lean_object* v_a_5237_; lean_object* v___x_5238_; 
v_a_5237_ = lean_ctor_get(v___x_5236_, 0);
lean_inc(v_a_5237_);
lean_dec_ref_known(v___x_5236_, 1);
lean_inc(v_fvarId_5230_);
v___x_5238_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useVar___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_useLetValue_spec__0___redArg(v_fvarId_5230_, v_a_4859_, v_a_4860_);
if (lean_obj_tag(v___x_5238_) == 0)
{
lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5264_; 
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5238_);
if (v_isSharedCheck_5264_ == 0)
{
lean_object* v_unused_5265_; 
v_unused_5265_ = lean_ctor_get(v___x_5238_, 0);
lean_dec(v_unused_5265_);
v___x_5240_ = v___x_5238_;
v_isShared_5241_ = v_isSharedCheck_5264_;
goto v_resetjp_5239_;
}
else
{
lean_dec(v___x_5238_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5264_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
size_t v___x_5242_; size_t v___x_5243_; uint8_t v___x_5244_; 
v___x_5242_ = lean_ptr_addr(v_k_5235_);
v___x_5243_ = lean_ptr_addr(v_a_5237_);
v___x_5244_ = lean_usize_dec_eq(v___x_5242_, v___x_5243_);
if (v___x_5244_ == 0)
{
lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5254_; 
lean_inc_ref(v_ty_5234_);
lean_inc(v_y_5233_);
lean_inc(v_offset_5232_);
lean_inc(v_i_5231_);
lean_inc(v_fvarId_5230_);
v_isSharedCheck_5254_ = !lean_is_exclusive(v_code_4858_);
if (v_isSharedCheck_5254_ == 0)
{
lean_object* v_unused_5255_; lean_object* v_unused_5256_; lean_object* v_unused_5257_; lean_object* v_unused_5258_; lean_object* v_unused_5259_; lean_object* v_unused_5260_; 
v_unused_5255_ = lean_ctor_get(v_code_4858_, 5);
lean_dec(v_unused_5255_);
v_unused_5256_ = lean_ctor_get(v_code_4858_, 4);
lean_dec(v_unused_5256_);
v_unused_5257_ = lean_ctor_get(v_code_4858_, 3);
lean_dec(v_unused_5257_);
v_unused_5258_ = lean_ctor_get(v_code_4858_, 2);
lean_dec(v_unused_5258_);
v_unused_5259_ = lean_ctor_get(v_code_4858_, 1);
lean_dec(v_unused_5259_);
v_unused_5260_ = lean_ctor_get(v_code_4858_, 0);
lean_dec(v_unused_5260_);
v___x_5246_ = v_code_4858_;
v_isShared_5247_ = v_isSharedCheck_5254_;
goto v_resetjp_5245_;
}
else
{
lean_dec(v_code_4858_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5254_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
lean_object* v___x_5249_; 
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 5, v_a_5237_);
v___x_5249_ = v___x_5246_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_fvarId_5230_);
lean_ctor_set(v_reuseFailAlloc_5253_, 1, v_i_5231_);
lean_ctor_set(v_reuseFailAlloc_5253_, 2, v_offset_5232_);
lean_ctor_set(v_reuseFailAlloc_5253_, 3, v_y_5233_);
lean_ctor_set(v_reuseFailAlloc_5253_, 4, v_ty_5234_);
lean_ctor_set(v_reuseFailAlloc_5253_, 5, v_a_5237_);
v___x_5249_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
lean_object* v___x_5251_; 
if (v_isShared_5241_ == 0)
{
lean_ctor_set(v___x_5240_, 0, v___x_5249_);
v___x_5251_ = v___x_5240_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
}
else
{
lean_object* v___x_5262_; 
lean_dec(v_a_5237_);
if (v_isShared_5241_ == 0)
{
lean_ctor_set(v___x_5240_, 0, v_code_4858_);
v___x_5262_ = v___x_5240_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_code_4858_);
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
else
{
lean_object* v_a_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5273_; 
lean_dec(v_a_5237_);
lean_dec_ref_known(v_code_4858_, 6);
v_a_5266_ = lean_ctor_get(v___x_5238_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v___x_5238_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5268_ = v___x_5238_;
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_a_5266_);
lean_dec(v___x_5238_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
lean_object* v___x_5271_; 
if (v_isShared_5269_ == 0)
{
v___x_5271_ = v___x_5268_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
v___x_5271_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
return v___x_5271_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_4858_, 6);
return v___x_5236_;
}
}
default: 
{
lean_object* v___x_5274_; lean_object* v___x_5275_; 
lean_dec_ref(v_code_4858_);
v___x_5274_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___closed__1);
v___x_5275_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_LetDecl_explicitRc_spec__2(v___x_5274_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_);
return v___x_5275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(lean_object* v_cases_5276_, size_t v_sz_5277_, size_t v_i_5278_, lean_object* v_bs_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_){
_start:
{
uint8_t v___x_5287_; 
v___x_5287_ = lean_usize_dec_lt(v_i_5278_, v_sz_5277_);
if (v___x_5287_ == 0)
{
lean_object* v___x_5288_; 
lean_dec_ref(v_cases_5276_);
v___x_5288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5288_, 0, v_bs_5279_);
return v___x_5288_;
}
else
{
lean_object* v_v_5289_; lean_object* v___x_5290_; lean_object* v_bs_x27_5291_; lean_object* v___x_5292_; lean_object* v_a_5294_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; 
v_v_5289_ = lean_array_uget(v_bs_5279_, v_i_5278_);
v___x_5290_ = lean_unsigned_to_nat(0u);
v_bs_x27_5291_ = lean_array_uset(v_bs_5279_, v_i_5278_, v___x_5290_);
v___x_5292_ = lean_st_ref_get(v___y_5281_);
v___x_5303_ = lean_st_ref_take(v___y_5281_);
lean_dec(v___x_5303_);
v___x_5304_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5305_ = lean_st_ref_put(v___y_5281_, v___x_5304_);
if (lean_obj_tag(v_v_5289_) == 1)
{
lean_object* v_info_5306_; lean_object* v_code_5307_; lean_object* v_discr_5308_; lean_object* v_resetTargets_5309_; lean_object* v_unconditionalBorrows_5310_; lean_object* v_derivedValMap_5311_; lean_object* v_varMap_5312_; lean_object* v_jpLiveVarMap_5313_; lean_object* v_idx_5314_; lean_object* v___y_5316_; lean_object* v___x_5331_; 
v_info_5306_ = lean_ctor_get(v_v_5289_, 0);
v_code_5307_ = lean_ctor_get(v_v_5289_, 1);
v_discr_5308_ = lean_ctor_get(v_cases_5276_, 2);
v_resetTargets_5309_ = lean_ctor_get(v___y_5280_, 0);
v_unconditionalBorrows_5310_ = lean_ctor_get(v___y_5280_, 1);
v_derivedValMap_5311_ = lean_ctor_get(v___y_5280_, 2);
v_varMap_5312_ = lean_ctor_get(v___y_5280_, 3);
v_jpLiveVarMap_5313_ = lean_ctor_get(v___y_5280_, 4);
v_idx_5314_ = lean_ctor_get(v___y_5280_, 5);
v___x_5331_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Context_addDerivedLetValue_spec__0___redArg(v_varMap_5312_, v_discr_5308_);
if (lean_obj_tag(v___x_5331_) == 0)
{
lean_inc(v_varMap_5312_);
v___y_5316_ = v_varMap_5312_;
goto v___jp_5315_;
}
else
{
lean_object* v_val_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5353_; 
v_val_5332_ = lean_ctor_get(v___x_5331_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5331_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5334_ = v___x_5331_;
v_isShared_5335_ = v_isSharedCheck_5353_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_val_5332_);
lean_dec(v___x_5331_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5353_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
uint8_t v_persistent_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5350_; 
v_persistent_5336_ = lean_ctor_get_uint8(v_val_5332_, sizeof(void*)*2 + 2);
v_isSharedCheck_5350_ = !lean_is_exclusive(v_val_5332_);
if (v_isSharedCheck_5350_ == 0)
{
lean_object* v_unused_5351_; lean_object* v_unused_5352_; 
v_unused_5351_ = lean_ctor_get(v_val_5332_, 1);
lean_dec(v_unused_5351_);
v_unused_5352_ = lean_ctor_get(v_val_5332_, 0);
lean_dec(v_unused_5352_);
v___x_5338_ = v_val_5332_;
v_isShared_5339_ = v_isSharedCheck_5350_;
goto v_resetjp_5337_;
}
else
{
lean_dec(v_val_5332_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5350_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
uint8_t v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5344_; 
v___x_5340_ = l_Lean_Compiler_LCNF_CtorInfo_isRef(v_info_5306_);
v___x_5341_ = lean_unsigned_to_nat(1u);
v___x_5342_ = lean_nat_add(v_idx_5314_, v___x_5341_);
lean_inc_ref(v_info_5306_);
if (v_isShared_5335_ == 0)
{
lean_ctor_set(v___x_5334_, 0, v_info_5306_);
v___x_5344_ = v___x_5334_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_info_5306_);
v___x_5344_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
lean_object* v___x_5346_; 
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 1, v___x_5344_);
lean_ctor_set(v___x_5338_, 0, v___x_5342_);
v___x_5346_ = v___x_5338_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v___x_5342_);
lean_ctor_set(v_reuseFailAlloc_5348_, 1, v___x_5344_);
lean_ctor_set_uint8(v_reuseFailAlloc_5348_, sizeof(void*)*2 + 2, v_persistent_5336_);
v___x_5346_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
lean_object* v___x_5347_; 
lean_ctor_set_uint8(v___x_5346_, sizeof(void*)*2, v___x_5340_);
lean_ctor_set_uint8(v___x_5346_, sizeof(void*)*2 + 1, v___x_5340_);
lean_inc(v_varMap_5312_);
lean_inc(v_discr_5308_);
v___x_5347_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_5308_, v___x_5346_, v_varMap_5312_);
v___y_5316_ = v___x_5347_;
goto v___jp_5315_;
}
}
}
}
}
v___jp_5315_:
{
lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; 
v___x_5317_ = lean_unsigned_to_nat(1u);
v___x_5318_ = lean_nat_add(v_idx_5314_, v___x_5317_);
lean_inc(v_jpLiveVarMap_5313_);
lean_inc(v_derivedValMap_5311_);
lean_inc(v_unconditionalBorrows_5310_);
lean_inc_ref(v_resetTargets_5309_);
v___x_5319_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5319_, 0, v_resetTargets_5309_);
lean_ctor_set(v___x_5319_, 1, v_unconditionalBorrows_5310_);
lean_ctor_set(v___x_5319_, 2, v_derivedValMap_5311_);
lean_ctor_set(v___x_5319_, 3, v___y_5316_);
lean_ctor_set(v___x_5319_, 4, v_jpLiveVarMap_5313_);
lean_ctor_set(v___x_5319_, 5, v___x_5318_);
lean_inc_ref(v_code_5307_);
v___x_5320_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5307_, v___x_5319_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_);
lean_dec_ref_known(v___x_5319_, 6);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v_a_5321_; lean_object* v___x_5322_; 
v_a_5321_ = lean_ctor_get(v___x_5320_, 0);
lean_inc(v_a_5321_);
lean_dec_ref_known(v___x_5320_, 1);
v___x_5322_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_5289_, v_a_5321_);
v_a_5294_ = v___x_5322_;
goto v___jp_5293_;
}
else
{
lean_object* v_a_5323_; lean_object* v___x_5325_; uint8_t v_isShared_5326_; uint8_t v_isSharedCheck_5330_; 
lean_dec_ref_known(v_v_5289_, 2);
lean_dec(v___x_5292_);
lean_dec_ref(v_bs_x27_5291_);
lean_dec_ref(v_cases_5276_);
v_a_5323_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5330_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5330_ == 0)
{
v___x_5325_ = v___x_5320_;
v_isShared_5326_ = v_isSharedCheck_5330_;
goto v_resetjp_5324_;
}
else
{
lean_inc(v_a_5323_);
lean_dec(v___x_5320_);
v___x_5325_ = lean_box(0);
v_isShared_5326_ = v_isSharedCheck_5330_;
goto v_resetjp_5324_;
}
v_resetjp_5324_:
{
lean_object* v___x_5328_; 
if (v_isShared_5326_ == 0)
{
v___x_5328_ = v___x_5325_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_a_5323_);
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
}
else
{
lean_object* v_code_5354_; lean_object* v___x_5355_; 
v_code_5354_ = lean_ctor_get(v_v_5289_, 0);
lean_inc_ref(v_code_5354_);
v___x_5355_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5354_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_);
if (lean_obj_tag(v___x_5355_) == 0)
{
lean_object* v_a_5356_; lean_object* v___x_5357_; 
v_a_5356_ = lean_ctor_get(v___x_5355_, 0);
lean_inc(v_a_5356_);
lean_dec_ref_known(v___x_5355_, 1);
v___x_5357_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_5289_, v_a_5356_);
v_a_5294_ = v___x_5357_;
goto v___jp_5293_;
}
else
{
lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
lean_dec_ref_known(v_v_5289_, 1);
lean_dec(v___x_5292_);
lean_dec_ref(v_bs_x27_5291_);
lean_dec_ref(v_cases_5276_);
v_a_5358_ = lean_ctor_get(v___x_5355_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5360_ = v___x_5355_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5355_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
}
v___jp_5293_:
{
lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; size_t v___x_5299_; size_t v___x_5300_; lean_object* v___x_5301_; 
v___x_5295_ = lean_st_ref_get(v___y_5281_);
v___x_5296_ = lean_st_ref_take(v___y_5281_);
lean_dec(v___x_5296_);
v___x_5297_ = lean_st_ref_put(v___y_5281_, v___x_5292_);
v___x_5298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5298_, 0, v_a_5294_);
lean_ctor_set(v___x_5298_, 1, v___x_5295_);
v___x_5299_ = ((size_t)1ULL);
v___x_5300_ = lean_usize_add(v_i_5278_, v___x_5299_);
v___x_5301_ = lean_array_uset(v_bs_x27_5291_, v_i_5278_, v___x_5298_);
v_i_5278_ = v___x_5300_;
v_bs_5279_ = v___x_5301_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6___boxed(lean_object* v_cases_5366_, lean_object* v_sz_5367_, lean_object* v_i_5368_, lean_object* v_bs_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_){
_start:
{
size_t v_sz_boxed_5377_; size_t v_i_boxed_5378_; lean_object* v_res_5379_; 
v_sz_boxed_5377_ = lean_unbox_usize(v_sz_5367_);
lean_dec(v_sz_5367_);
v_i_boxed_5378_ = lean_unbox_usize(v_i_5368_);
lean_dec(v_i_5368_);
v_res_5379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__6(v_cases_5366_, v_sz_boxed_5377_, v_i_boxed_5378_, v_bs_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_);
lean_dec(v___y_5375_);
lean_dec_ref(v___y_5374_);
lean_dec(v___y_5373_);
lean_dec_ref(v___y_5372_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
return v_res_5379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc___boxed(lean_object* v_code_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_){
_start:
{
lean_object* v_res_5388_; 
v_res_5388_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5380_, v_a_5381_, v_a_5382_, v_a_5383_, v_a_5384_, v_a_5385_, v_a_5386_);
lean_dec(v_a_5386_);
lean_dec_ref(v_a_5385_);
lean_dec(v_a_5384_);
lean_dec_ref(v_a_5383_);
lean_dec(v_a_5382_);
lean_dec_ref(v_a_5381_);
return v_res_5388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1(lean_object* v_00_u03b2_5389_, lean_object* v_m_5390_, lean_object* v_a_5391_, lean_object* v_b_5392_){
_start:
{
lean_object* v___x_5393_; 
v___x_5393_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1___redArg(v_m_5390_, v_a_5391_, v_b_5392_);
return v___x_5393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_5394_, lean_object* v_a_5395_, lean_object* v_b_5396_, lean_object* v_x_5397_){
_start:
{
lean_object* v___x_5398_; 
v___x_5398_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__1_spec__1_spec__3___redArg(v_a_5395_, v_b_5396_, v_x_5397_);
return v___x_5398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(lean_object* v_decl_5399_, lean_object* v_code_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_){
_start:
{
lean_object* v_toSignature_5408_; lean_object* v_params_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; uint8_t v___x_5412_; 
v_toSignature_5408_ = lean_ctor_get(v_decl_5399_, 0);
v_params_5409_ = lean_ctor_get(v_toSignature_5408_, 3);
v___x_5410_ = lean_unsigned_to_nat(0u);
v___x_5411_ = lean_array_get_size(v_params_5409_);
v___x_5412_ = lean_nat_dec_lt(v___x_5410_, v___x_5411_);
if (v___x_5412_ == 0)
{
lean_object* v___x_5413_; 
v___x_5413_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_);
if (lean_obj_tag(v___x_5413_) == 0)
{
lean_object* v_a_5414_; lean_object* v___x_5415_; 
v_a_5414_ = lean_ctor_get(v___x_5413_, 0);
lean_inc(v_a_5414_);
lean_dec_ref_known(v___x_5413_, 1);
v___x_5415_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5409_, v_a_5414_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_);
return v___x_5415_;
}
else
{
return v___x_5413_;
}
}
else
{
size_t v___x_5416_; size_t v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5416_ = ((size_t)0ULL);
v___x_5417_ = lean_usize_of_nat(v___x_5411_);
lean_inc_ref(v_a_5401_);
v___x_5418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc_spec__3(v_params_5409_, v___x_5416_, v___x_5417_, v_a_5401_);
v___x_5419_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Code_explicitRc(v_code_5400_, v___x_5418_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v_a_5420_; lean_object* v___x_5421_; 
v_a_5420_ = lean_ctor_get(v___x_5419_, 0);
lean_inc(v_a_5420_);
lean_dec_ref_known(v___x_5419_, 1);
v___x_5421_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_addDecForDeadParams(v_params_5409_, v_a_5420_, v___x_5418_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_);
lean_dec_ref(v___x_5418_);
return v___x_5421_;
}
else
{
lean_dec_ref(v___x_5418_);
return v___x_5419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go___boxed(lean_object* v_decl_5422_, lean_object* v_code_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_, lean_object* v_a_5429_, lean_object* v_a_5430_){
_start:
{
lean_object* v_res_5431_; 
v_res_5431_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(v_decl_5422_, v_code_5423_, v_a_5424_, v_a_5425_, v_a_5426_, v_a_5427_, v_a_5428_, v_a_5429_);
lean_dec(v_a_5429_);
lean_dec_ref(v_a_5428_);
lean_dec(v_a_5427_);
lean_dec_ref(v_a_5426_);
lean_dec(v_a_5425_);
lean_dec_ref(v_a_5424_);
lean_dec_ref(v_decl_5422_);
return v_res_5431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(lean_object* v_f_5432_, lean_object* v_v_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_){
_start:
{
if (lean_obj_tag(v_v_5433_) == 0)
{
lean_object* v_code_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5463_; 
v_code_5439_ = lean_ctor_get(v_v_5433_, 0);
v_isSharedCheck_5463_ = !lean_is_exclusive(v_v_5433_);
if (v_isSharedCheck_5463_ == 0)
{
v___x_5441_ = v_v_5433_;
v_isShared_5442_ = v_isSharedCheck_5463_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_code_5439_);
lean_dec(v_v_5433_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5463_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v___x_5443_; 
lean_inc(v___y_5437_);
lean_inc_ref(v___y_5436_);
lean_inc(v___y_5435_);
lean_inc_ref(v___y_5434_);
v___x_5443_ = lean_apply_6(v_f_5432_, v_code_5439_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, lean_box(0));
if (lean_obj_tag(v___x_5443_) == 0)
{
lean_object* v_a_5444_; lean_object* v___x_5446_; uint8_t v_isShared_5447_; uint8_t v_isSharedCheck_5454_; 
v_a_5444_ = lean_ctor_get(v___x_5443_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___x_5443_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5446_ = v___x_5443_;
v_isShared_5447_ = v_isSharedCheck_5454_;
goto v_resetjp_5445_;
}
else
{
lean_inc(v_a_5444_);
lean_dec(v___x_5443_);
v___x_5446_ = lean_box(0);
v_isShared_5447_ = v_isSharedCheck_5454_;
goto v_resetjp_5445_;
}
v_resetjp_5445_:
{
lean_object* v___x_5449_; 
if (v_isShared_5442_ == 0)
{
lean_ctor_set(v___x_5441_, 0, v_a_5444_);
v___x_5449_ = v___x_5441_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5444_);
v___x_5449_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
lean_object* v___x_5451_; 
if (v_isShared_5447_ == 0)
{
lean_ctor_set(v___x_5446_, 0, v___x_5449_);
v___x_5451_ = v___x_5446_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v___x_5449_);
v___x_5451_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
return v___x_5451_;
}
}
}
}
else
{
lean_object* v_a_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5462_; 
lean_del_object(v___x_5441_);
v_a_5455_ = lean_ctor_get(v___x_5443_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5443_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5457_ = v___x_5443_;
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_a_5455_);
lean_dec(v___x_5443_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v___x_5460_; 
if (v_isShared_5458_ == 0)
{
v___x_5460_ = v___x_5457_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5455_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
}
}
else
{
lean_object* v___x_5464_; 
lean_dec_ref(v_f_5432_);
v___x_5464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5464_, 0, v_v_5433_);
return v___x_5464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg___boxed(lean_object* v_f_5465_, lean_object* v_v_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_){
_start:
{
lean_object* v_res_5472_; 
v_res_5472_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v_f_5465_, v_v_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_);
lean_dec(v___y_5470_);
lean_dec_ref(v___y_5469_);
lean_dec(v___y_5468_);
lean_dec_ref(v___y_5467_);
return v_res_5472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(uint8_t v_pu_5473_, lean_object* v_f_5474_, lean_object* v_v_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_){
_start:
{
lean_object* v___x_5481_; 
v___x_5481_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v_f_5474_, v_v_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_);
return v___x_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___boxed(lean_object* v_pu_5482_, lean_object* v_f_5483_, lean_object* v_v_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_){
_start:
{
uint8_t v_pu_boxed_5490_; lean_object* v_res_5491_; 
v_pu_boxed_5490_ = lean_unbox(v_pu_5482_);
v_res_5491_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0(v_pu_boxed_5490_, v_f_5483_, v_v_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_);
lean_dec(v___y_5488_);
lean_dec_ref(v___y_5487_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
return v_res_5491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(lean_object* v_decl_5492_, lean_object* v_code_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_){
_start:
{
lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; 
lean_inc_ref(v_code_5493_);
v___x_5499_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_collectResetTargets(v_code_5493_);
v___x_5500_ = lean_box(0);
v___x_5501_ = lean_box(1);
v___x_5502_ = lean_unsigned_to_nat(0u);
v___x_5503_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5503_, 0, v___x_5499_);
lean_ctor_set(v___x_5503_, 1, v___x_5500_);
lean_ctor_set(v___x_5503_, 2, v___x_5501_);
lean_ctor_set(v___x_5503_, 3, v___x_5501_);
lean_ctor_set(v___x_5503_, 4, v___x_5501_);
lean_ctor_set(v___x_5503_, 5, v___x_5502_);
v___x_5504_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2, &l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2_once, _init_l_Lean_Compiler_LCNF_instInhabitedLiveVars_default___closed__2);
v___x_5505_ = lean_st_mk_ref(v___x_5504_);
v___x_5506_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_go(v_decl_5492_, v_code_5493_, v___x_5503_, v___x_5505_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_);
lean_dec_ref_known(v___x_5503_, 6);
if (lean_obj_tag(v___x_5506_) == 0)
{
lean_object* v_a_5507_; lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5515_; 
v_a_5507_ = lean_ctor_get(v___x_5506_, 0);
v_isSharedCheck_5515_ = !lean_is_exclusive(v___x_5506_);
if (v_isSharedCheck_5515_ == 0)
{
v___x_5509_ = v___x_5506_;
v_isShared_5510_ = v_isSharedCheck_5515_;
goto v_resetjp_5508_;
}
else
{
lean_inc(v_a_5507_);
lean_dec(v___x_5506_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5515_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v___x_5511_; lean_object* v___x_5513_; 
v___x_5511_ = lean_st_ref_get(v___x_5505_);
lean_dec(v___x_5505_);
lean_dec(v___x_5511_);
if (v_isShared_5510_ == 0)
{
v___x_5513_ = v___x_5509_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_a_5507_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
}
else
{
lean_dec(v___x_5505_);
return v___x_5506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0___boxed(lean_object* v_decl_5516_, lean_object* v_code_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_){
_start:
{
lean_object* v_res_5523_; 
v_res_5523_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0(v_decl_5516_, v_code_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
lean_dec_ref(v_decl_5516_);
return v_res_5523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(lean_object* v_decl_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_){
_start:
{
lean_object* v_toSignature_5530_; lean_object* v_value_5531_; uint8_t v_recursive_5532_; lean_object* v_inlineAttr_x3f_5533_; lean_object* v___f_5534_; lean_object* v___x_5535_; 
v_toSignature_5530_ = lean_ctor_get(v_decl_5524_, 0);
lean_inc_ref(v_toSignature_5530_);
v_value_5531_ = lean_ctor_get(v_decl_5524_, 1);
lean_inc_ref(v_value_5531_);
v_recursive_5532_ = lean_ctor_get_uint8(v_decl_5524_, sizeof(void*)*3);
v_inlineAttr_x3f_5533_ = lean_ctor_get(v_decl_5524_, 2);
lean_inc(v_inlineAttr_x3f_5533_);
v___f_5534_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5534_, 0, v_decl_5524_);
v___x_5535_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc_spec__0___redArg(v___f_5534_, v_value_5531_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_);
if (lean_obj_tag(v___x_5535_) == 0)
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5544_; 
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5544_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5544_ == 0)
{
v___x_5538_ = v___x_5535_;
v_isShared_5539_ = v_isSharedCheck_5544_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5535_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5544_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5540_; lean_object* v___x_5542_; 
v___x_5540_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_5540_, 0, v_toSignature_5530_);
lean_ctor_set(v___x_5540_, 1, v_a_5536_);
lean_ctor_set(v___x_5540_, 2, v_inlineAttr_x3f_5533_);
lean_ctor_set_uint8(v___x_5540_, sizeof(void*)*3, v_recursive_5532_);
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 0, v___x_5540_);
v___x_5542_ = v___x_5538_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v___x_5540_);
v___x_5542_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
return v___x_5542_;
}
}
}
else
{
lean_object* v_a_5545_; lean_object* v___x_5547_; uint8_t v_isShared_5548_; uint8_t v_isSharedCheck_5552_; 
lean_dec(v_inlineAttr_x3f_5533_);
lean_dec_ref(v_toSignature_5530_);
v_a_5545_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5552_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5547_ = v___x_5535_;
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
else
{
lean_inc(v_a_5545_);
lean_dec(v___x_5535_);
v___x_5547_ = lean_box(0);
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
v_resetjp_5546_:
{
lean_object* v___x_5550_; 
if (v_isShared_5548_ == 0)
{
v___x_5550_ = v___x_5547_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_a_5545_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
return v___x_5550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc___boxed(lean_object* v_decl_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_){
_start:
{
lean_object* v_res_5559_; 
v_res_5559_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(v_decl_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
lean_dec(v_a_5557_);
lean_dec_ref(v_a_5556_);
lean_dec(v_a_5555_);
lean_dec_ref(v_a_5554_);
return v_res_5559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(size_t v_sz_5560_, size_t v_i_5561_, lean_object* v_bs_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_){
_start:
{
uint8_t v___x_5568_; 
v___x_5568_ = lean_usize_dec_lt(v_i_5561_, v_sz_5560_);
if (v___x_5568_ == 0)
{
lean_object* v___x_5569_; 
v___x_5569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5569_, 0, v_bs_5562_);
return v___x_5569_;
}
else
{
lean_object* v_v_5570_; lean_object* v___x_5571_; lean_object* v_bs_x27_5572_; lean_object* v___x_5573_; 
v_v_5570_ = lean_array_uget(v_bs_5562_, v_i_5561_);
v___x_5571_ = lean_unsigned_to_nat(0u);
v_bs_x27_5572_ = lean_array_uset(v_bs_5562_, v_i_5561_, v___x_5571_);
v___x_5573_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_Decl_explicitRc(v_v_5570_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_);
if (lean_obj_tag(v___x_5573_) == 0)
{
lean_object* v_a_5574_; size_t v___x_5575_; size_t v___x_5576_; lean_object* v___x_5577_; 
v_a_5574_ = lean_ctor_get(v___x_5573_, 0);
lean_inc(v_a_5574_);
lean_dec_ref_known(v___x_5573_, 1);
v___x_5575_ = ((size_t)1ULL);
v___x_5576_ = lean_usize_add(v_i_5561_, v___x_5575_);
v___x_5577_ = lean_array_uset(v_bs_x27_5572_, v_i_5561_, v_a_5574_);
v_i_5561_ = v___x_5576_;
v_bs_5562_ = v___x_5577_;
goto _start;
}
else
{
lean_object* v_a_5579_; lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5586_; 
lean_dec_ref(v_bs_x27_5572_);
v_a_5579_ = lean_ctor_get(v___x_5573_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v___x_5573_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5581_ = v___x_5573_;
v_isShared_5582_ = v_isSharedCheck_5586_;
goto v_resetjp_5580_;
}
else
{
lean_inc(v_a_5579_);
lean_dec(v___x_5573_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5586_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
lean_object* v___x_5584_; 
if (v_isShared_5582_ == 0)
{
v___x_5584_ = v___x_5581_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5579_);
v___x_5584_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
return v___x_5584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0___boxed(lean_object* v_sz_5587_, lean_object* v_i_5588_, lean_object* v_bs_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_){
_start:
{
size_t v_sz_boxed_5595_; size_t v_i_boxed_5596_; lean_object* v_res_5597_; 
v_sz_boxed_5595_ = lean_unbox_usize(v_sz_5587_);
lean_dec(v_sz_5587_);
v_i_boxed_5596_ = lean_unbox_usize(v_i_5588_);
lean_dec(v_i_5588_);
v_res_5597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(v_sz_boxed_5595_, v_i_boxed_5596_, v_bs_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
lean_dec(v___y_5593_);
lean_dec_ref(v___y_5592_);
lean_dec(v___y_5591_);
lean_dec_ref(v___y_5590_);
return v_res_5597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc(lean_object* v_decls_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_, lean_object* v_a_5602_){
_start:
{
size_t v_sz_5604_; size_t v___x_5605_; lean_object* v___x_5606_; 
v_sz_5604_ = lean_array_size(v_decls_5598_);
v___x_5605_ = ((size_t)0ULL);
v___x_5606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_runExplicitRc_spec__0(v_sz_5604_, v___x_5605_, v_decls_5598_, v_a_5599_, v_a_5600_, v_a_5601_, v_a_5602_);
return v___x_5606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runExplicitRc___boxed(lean_object* v_decls_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_){
_start:
{
lean_object* v_res_5613_; 
v_res_5613_ = l_Lean_Compiler_LCNF_runExplicitRc(v_decls_5607_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_);
lean_dec(v_a_5611_);
lean_dec_ref(v_a_5610_);
lean_dec(v_a_5609_);
lean_dec_ref(v_a_5608_);
return v_res_5613_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_explicitRc___closed__3(void){
_start:
{
lean_object* v___x_5618_; lean_object* v___x_5619_; uint8_t v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; 
v___x_5618_ = lean_unsigned_to_nat(0u);
v___x_5619_ = ((lean_object*)(l_Lean_Compiler_LCNF_explicitRc___closed__2));
v___x_5620_ = 2;
v___x_5621_ = ((lean_object*)(l_Lean_Compiler_LCNF_explicitRc___closed__1));
v___x_5622_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_5621_, v___x_5620_, v___x_5619_, v___x_5618_);
return v___x_5622_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_explicitRc(void){
_start:
{
lean_object* v___x_5623_; 
v___x_5623_ = lean_obj_once(&l_Lean_Compiler_LCNF_explicitRc___closed__3, &l_Lean_Compiler_LCNF_explicitRc___closed__3_once, _init_l_Lean_Compiler_LCNF_explicitRc___closed__3);
return v___x_5623_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; 
v___x_5679_ = lean_unsigned_to_nat(3791338971u);
v___x_5680_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5681_ = l_Lean_Name_num___override(v___x_5680_, v___x_5679_);
return v___x_5681_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; 
v___x_5683_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5684_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5685_ = l_Lean_Name_str___override(v___x_5684_, v___x_5683_);
return v___x_5685_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; 
v___x_5687_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5688_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5689_ = l_Lean_Name_str___override(v___x_5688_, v___x_5687_);
return v___x_5689_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5690_ = lean_unsigned_to_nat(2u);
v___x_5691_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5692_ = l_Lean_Name_num___override(v___x_5691_, v___x_5690_);
return v___x_5692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5694_; uint8_t v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; 
v___x_5694_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_));
v___x_5695_ = 1;
v___x_5696_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_);
v___x_5697_ = l_Lean_registerTraceClass(v___x_5694_, v___x_5695_, v___x_5696_);
return v___x_5697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2____boxed(lean_object* v_a_5698_){
_start:
{
lean_object* v_res_5699_; 
v_res_5699_ = l___private_Lean_Compiler_LCNF_ExplicitRC_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExplicitRC_3791338971____hygCtx___hyg_2_();
return v_res_5699_;
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
