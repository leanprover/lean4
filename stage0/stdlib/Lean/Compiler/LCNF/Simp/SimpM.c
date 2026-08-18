// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.SimpM
// Imports: public import Lean.Compiler.ImplementedByAttr public import Lean.Compiler.LCNF.Renaming public import Lean.Compiler.LCNF.ElimDead public import Lean.Compiler.LCNF.AlphaEqv public import Lean.Compiler.LCNF.PrettyPrinter public import Lean.Compiler.LCNF.Simp.JpCases public import Lean.Compiler.LCNF.Simp.FunDeclInfo public import Lean.Compiler.LCNF.Simp.Config
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_sizeLe(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1;
static const lean_closure_object l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "function `"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` has been recursively inlined more than #"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 156, .m_capacity = 156, .m_length = 155, .m_data = ", consider removing the attribute `[inline_if_reduce]` from this declaration or increasing the limit using `set_option compiler.maxRecInlineIfReduce <num>`"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inline"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__8_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__6_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__7_value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__8_value),LEAN_SCALAR_PTR_LITERAL(186, 182, 14, 42, 67, 101, 187, 98)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__11_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "...\n"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "maximum recursion depth reached in the code generator\nfunction inline stack:\n"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_betaReduce___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_betaReduce___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0(lean_object* v_00_u03b1_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___y_2_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed(lean_object* v_00_u03b1_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0(v_00_u03b1_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1(lean_object* v_00_u03b1_23_, lean_object* v_00_u03b2_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; 
lean_inc(v___y_33_);
lean_inc_ref(v___y_32_);
lean_inc(v___y_31_);
lean_inc_ref(v___y_30_);
lean_inc_ref(v___y_29_);
lean_inc(v___y_28_);
lean_inc_ref(v___y_27_);
v___x_35_ = lean_apply_8(v___y_25_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, lean_box(0));
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v_a_36_; lean_object* v___x_37_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_a_36_);
lean_dec_ref_known(v___x_35_, 1);
lean_inc(v___y_33_);
lean_inc_ref(v___y_32_);
lean_inc(v___y_31_);
lean_inc_ref(v___y_30_);
lean_inc_ref(v___y_29_);
lean_inc(v___y_28_);
lean_inc_ref(v___y_27_);
v___x_37_ = lean_apply_9(v___y_26_, v_a_36_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, lean_box(0));
return v___x_37_;
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
lean_dec_ref(v___y_26_);
v_a_38_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_35_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_35_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed(lean_object* v_00_u03b1_46_, lean_object* v_00_u03b2_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1(v_00_u03b1_46_, v_00_u03b2_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_58_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_instMonadEIO(lean_box(0));
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0, &l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0);
v___x_61_ = l_StateRefT_x27_instMonad___redArg(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM(void){
_start:
{
lean_object* v___x_68_; lean_object* v_toApplicative_69_; lean_object* v_toFunctor_70_; lean_object* v_toSeq_71_; lean_object* v_toSeqLeft_72_; lean_object* v_toSeqRight_73_; lean_object* v___f_74_; lean_object* v___f_75_; lean_object* v___f_76_; lean_object* v___f_77_; lean_object* v___x_78_; lean_object* v___f_79_; lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v_toApplicative_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_143_; 
v___x_68_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1, &l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1);
v_toApplicative_69_ = lean_ctor_get(v___x_68_, 0);
v_toFunctor_70_ = lean_ctor_get(v_toApplicative_69_, 0);
v_toSeq_71_ = lean_ctor_get(v_toApplicative_69_, 2);
v_toSeqLeft_72_ = lean_ctor_get(v_toApplicative_69_, 3);
v_toSeqRight_73_ = lean_ctor_get(v_toApplicative_69_, 4);
v___f_74_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2));
v___f_75_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3));
lean_inc_ref_n(v_toFunctor_70_, 2);
v___f_76_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_76_, 0, v_toFunctor_70_);
v___f_77_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_77_, 0, v_toFunctor_70_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___f_76_);
lean_ctor_set(v___x_78_, 1, v___f_77_);
lean_inc(v_toSeqRight_73_);
v___f_79_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_79_, 0, v_toSeqRight_73_);
lean_inc(v_toSeqLeft_72_);
v___f_80_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_80_, 0, v_toSeqLeft_72_);
lean_inc(v_toSeq_71_);
v___f_81_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_81_, 0, v_toSeq_71_);
v___x_82_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_82_, 0, v___x_78_);
lean_ctor_set(v___x_82_, 1, v___f_74_);
lean_ctor_set(v___x_82_, 2, v___f_81_);
lean_ctor_set(v___x_82_, 3, v___f_80_);
lean_ctor_set(v___x_82_, 4, v___f_79_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___f_75_);
v___x_84_ = l_StateRefT_x27_instMonad___redArg(v___x_83_);
v_toApplicative_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v___x_84_, 1);
lean_dec(v_unused_144_);
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_143_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_toApplicative_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_143_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_toFunctor_89_; lean_object* v_toSeq_90_; lean_object* v_toSeqLeft_91_; lean_object* v_toSeqRight_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_141_; 
v_toFunctor_89_ = lean_ctor_get(v_toApplicative_85_, 0);
v_toSeq_90_ = lean_ctor_get(v_toApplicative_85_, 2);
v_toSeqLeft_91_ = lean_ctor_get(v_toApplicative_85_, 3);
v_toSeqRight_92_ = lean_ctor_get(v_toApplicative_85_, 4);
v_isSharedCheck_141_ = !lean_is_exclusive(v_toApplicative_85_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; 
v_unused_142_ = lean_ctor_get(v_toApplicative_85_, 1);
lean_dec(v_unused_142_);
v___x_94_ = v_toApplicative_85_;
v_isShared_95_ = v_isSharedCheck_141_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_toSeqRight_92_);
lean_inc(v_toSeqLeft_91_);
lean_inc(v_toSeq_90_);
lean_inc(v_toFunctor_89_);
lean_dec(v_toApplicative_85_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_141_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___f_96_; lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___x_100_; lean_object* v___f_101_; lean_object* v___f_102_; lean_object* v___f_103_; lean_object* v___x_105_; 
v___f_96_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4));
v___f_97_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5));
lean_inc_ref(v_toFunctor_89_);
v___f_98_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_98_, 0, v_toFunctor_89_);
v___f_99_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_99_, 0, v_toFunctor_89_);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v___f_98_);
lean_ctor_set(v___x_100_, 1, v___f_99_);
v___f_101_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_101_, 0, v_toSeqRight_92_);
v___f_102_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_102_, 0, v_toSeqLeft_91_);
v___f_103_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_103_, 0, v_toSeq_90_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 4, v___f_101_);
lean_ctor_set(v___x_94_, 3, v___f_102_);
lean_ctor_set(v___x_94_, 2, v___f_103_);
lean_ctor_set(v___x_94_, 1, v___f_96_);
lean_ctor_set(v___x_94_, 0, v___x_100_);
v___x_105_ = v___x_94_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___f_96_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v___f_103_);
lean_ctor_set(v_reuseFailAlloc_140_, 3, v___f_102_);
lean_ctor_set(v_reuseFailAlloc_140_, 4, v___f_101_);
v___x_105_ = v_reuseFailAlloc_140_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_107_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 1, v___f_97_);
lean_ctor_set(v___x_87_, 0, v___x_105_);
v___x_107_ = v___x_87_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___f_97_);
v___x_107_ = v_reuseFailAlloc_139_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_toApplicative_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_137_; 
v___x_108_ = l_ReaderT_instMonad___redArg(v___x_107_);
v___x_109_ = l_StateRefT_x27_instMonad___redArg(v___x_108_);
v_toApplicative_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; 
v_unused_138_ = lean_ctor_get(v___x_109_, 1);
lean_dec(v_unused_138_);
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_137_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_toApplicative_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_137_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_toFunctor_114_; lean_object* v_toSeq_115_; lean_object* v_toSeqLeft_116_; lean_object* v_toSeqRight_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_135_; 
v_toFunctor_114_ = lean_ctor_get(v_toApplicative_110_, 0);
v_toSeq_115_ = lean_ctor_get(v_toApplicative_110_, 2);
v_toSeqLeft_116_ = lean_ctor_get(v_toApplicative_110_, 3);
v_toSeqRight_117_ = lean_ctor_get(v_toApplicative_110_, 4);
v_isSharedCheck_135_ = !lean_is_exclusive(v_toApplicative_110_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; 
v_unused_136_ = lean_ctor_get(v_toApplicative_110_, 1);
lean_dec(v_unused_136_);
v___x_119_ = v_toApplicative_110_;
v_isShared_120_ = v_isSharedCheck_135_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_toSeqRight_117_);
lean_inc(v_toSeqLeft_116_);
lean_inc(v_toSeq_115_);
lean_inc(v_toFunctor_114_);
lean_dec(v_toApplicative_110_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_135_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___f_121_; lean_object* v___f_122_; lean_object* v___f_123_; lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___f_126_; lean_object* v___f_127_; lean_object* v___f_128_; lean_object* v___x_130_; 
v___f_121_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6));
v___f_122_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7));
lean_inc_ref(v_toFunctor_114_);
v___f_123_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_123_, 0, v_toFunctor_114_);
v___f_124_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_124_, 0, v_toFunctor_114_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___f_123_);
lean_ctor_set(v___x_125_, 1, v___f_124_);
v___f_126_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_126_, 0, v_toSeqRight_117_);
v___f_127_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_127_, 0, v_toSeqLeft_116_);
v___f_128_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_128_, 0, v_toSeq_115_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 4, v___f_126_);
lean_ctor_set(v___x_119_, 3, v___f_127_);
lean_ctor_set(v___x_119_, 2, v___f_128_);
lean_ctor_set(v___x_119_, 1, v___f_121_);
lean_ctor_set(v___x_119_, 0, v___x_125_);
v___x_130_ = v___x_119_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___f_121_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v___f_128_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v___f_127_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v___f_126_);
v___x_130_ = v_reuseFailAlloc_134_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 1, v___f_122_);
lean_ctor_set(v___x_112_, 0, v___x_130_);
v___x_132_ = v___x_112_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___f_122_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0(lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; lean_object* v_subst_154_; lean_object* v___x_155_; 
v___x_153_ = lean_st_ref_get(v___y_146_);
v_subst_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc_ref(v_subst_154_);
lean_dec(v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v_subst_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0___boxed(lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0(v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0(lean_object* v_f_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; lean_object* v_subst_177_; lean_object* v_used_178_; lean_object* v_binderRenaming_179_; lean_object* v_funDeclInfoMap_180_; uint8_t v_simplified_181_; lean_object* v_visited_182_; lean_object* v_inline_183_; lean_object* v_inlineLocal_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_195_; 
v___x_176_ = lean_st_ref_take(v___y_169_);
v_subst_177_ = lean_ctor_get(v___x_176_, 0);
v_used_178_ = lean_ctor_get(v___x_176_, 1);
v_binderRenaming_179_ = lean_ctor_get(v___x_176_, 2);
v_funDeclInfoMap_180_ = lean_ctor_get(v___x_176_, 3);
v_simplified_181_ = lean_ctor_get_uint8(v___x_176_, sizeof(void*)*7);
v_visited_182_ = lean_ctor_get(v___x_176_, 4);
v_inline_183_ = lean_ctor_get(v___x_176_, 5);
v_inlineLocal_184_ = lean_ctor_get(v___x_176_, 6);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_195_ == 0)
{
v___x_186_ = v___x_176_;
v_isShared_187_ = v_isSharedCheck_195_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_inlineLocal_184_);
lean_inc(v_inline_183_);
lean_inc(v_visited_182_);
lean_inc(v_funDeclInfoMap_180_);
lean_inc(v_binderRenaming_179_);
lean_inc(v_used_178_);
lean_inc(v_subst_177_);
lean_dec(v___x_176_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_195_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = lean_apply_1(v_f_167_, v_subst_177_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_used_178_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_binderRenaming_179_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v_funDeclInfoMap_180_);
lean_ctor_set(v_reuseFailAlloc_194_, 4, v_visited_182_);
lean_ctor_set(v_reuseFailAlloc_194_, 5, v_inline_183_);
lean_ctor_set(v_reuseFailAlloc_194_, 6, v_inlineLocal_184_);
lean_ctor_set_uint8(v_reuseFailAlloc_194_, sizeof(void*)*7, v_simplified_181_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_st_ref_put(v___y_169_, v___x_190_);
v___x_192_ = lean_box(0);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0___boxed(lean_object* v_f_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0(v_f_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; lean_object* v_subst_211_; lean_object* v_used_212_; lean_object* v_binderRenaming_213_; lean_object* v_funDeclInfoMap_214_; lean_object* v_visited_215_; lean_object* v_inline_216_; lean_object* v_inlineLocal_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_228_; 
v___x_210_ = lean_st_ref_take(v_a_208_);
v_subst_211_ = lean_ctor_get(v___x_210_, 0);
v_used_212_ = lean_ctor_get(v___x_210_, 1);
v_binderRenaming_213_ = lean_ctor_get(v___x_210_, 2);
v_funDeclInfoMap_214_ = lean_ctor_get(v___x_210_, 3);
v_visited_215_ = lean_ctor_get(v___x_210_, 4);
v_inline_216_ = lean_ctor_get(v___x_210_, 5);
v_inlineLocal_217_ = lean_ctor_get(v___x_210_, 6);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_228_ == 0)
{
v___x_219_ = v___x_210_;
v_isShared_220_ = v_isSharedCheck_228_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_inlineLocal_217_);
lean_inc(v_inline_216_);
lean_inc(v_visited_215_);
lean_inc(v_funDeclInfoMap_214_);
lean_inc(v_binderRenaming_213_);
lean_inc(v_used_212_);
lean_inc(v_subst_211_);
lean_dec(v___x_210_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_228_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
uint8_t v___x_221_; lean_object* v___x_223_; 
v___x_221_ = 1;
if (v_isShared_220_ == 0)
{
v___x_223_ = v___x_219_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_subst_211_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_used_212_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_binderRenaming_213_);
lean_ctor_set(v_reuseFailAlloc_227_, 3, v_funDeclInfoMap_214_);
lean_ctor_set(v_reuseFailAlloc_227_, 4, v_visited_215_);
lean_ctor_set(v_reuseFailAlloc_227_, 5, v_inline_216_);
lean_ctor_set(v_reuseFailAlloc_227_, 6, v_inlineLocal_217_);
v___x_223_ = v_reuseFailAlloc_227_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*7, v___x_221_);
v___x_224_ = lean_st_ref_put(v_a_208_, v___x_223_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg___boxed(lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_229_);
lean_dec(v_a_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified(lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_233_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___boxed(lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Compiler_LCNF_Simp_markSimplified(v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object* v_a_250_){
_start:
{
lean_object* v___x_252_; lean_object* v_subst_253_; lean_object* v_used_254_; lean_object* v_binderRenaming_255_; lean_object* v_funDeclInfoMap_256_; uint8_t v_simplified_257_; lean_object* v_visited_258_; lean_object* v_inline_259_; lean_object* v_inlineLocal_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_272_; 
v___x_252_ = lean_st_ref_take(v_a_250_);
v_subst_253_ = lean_ctor_get(v___x_252_, 0);
v_used_254_ = lean_ctor_get(v___x_252_, 1);
v_binderRenaming_255_ = lean_ctor_get(v___x_252_, 2);
v_funDeclInfoMap_256_ = lean_ctor_get(v___x_252_, 3);
v_simplified_257_ = lean_ctor_get_uint8(v___x_252_, sizeof(void*)*7);
v_visited_258_ = lean_ctor_get(v___x_252_, 4);
v_inline_259_ = lean_ctor_get(v___x_252_, 5);
v_inlineLocal_260_ = lean_ctor_get(v___x_252_, 6);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_272_ == 0)
{
v___x_262_ = v___x_252_;
v_isShared_263_ = v_isSharedCheck_272_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_inlineLocal_260_);
lean_inc(v_inline_259_);
lean_inc(v_visited_258_);
lean_inc(v_funDeclInfoMap_256_);
lean_inc(v_binderRenaming_255_);
lean_inc(v_used_254_);
lean_inc(v_subst_253_);
lean_dec(v___x_252_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_272_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_nat_add(v_visited_258_, v___x_264_);
lean_dec(v_visited_258_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 4, v___x_265_);
v___x_267_ = v___x_262_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_subst_253_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_used_254_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_binderRenaming_255_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_funDeclInfoMap_256_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_271_, 5, v_inline_259_);
lean_ctor_set(v_reuseFailAlloc_271_, 6, v_inlineLocal_260_);
lean_ctor_set_uint8(v_reuseFailAlloc_271_, sizeof(void*)*7, v_simplified_257_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_st_ref_put(v_a_250_, v___x_267_);
v___x_269_ = lean_box(0);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg___boxed(lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_273_);
lean_dec(v_a_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited(lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_277_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___boxed(lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Compiler_LCNF_Simp_incVisited(v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___redArg(lean_object* v_a_294_){
_start:
{
lean_object* v___x_296_; lean_object* v_subst_297_; lean_object* v_used_298_; lean_object* v_binderRenaming_299_; lean_object* v_funDeclInfoMap_300_; uint8_t v_simplified_301_; lean_object* v_visited_302_; lean_object* v_inline_303_; lean_object* v_inlineLocal_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_316_; 
v___x_296_ = lean_st_ref_take(v_a_294_);
v_subst_297_ = lean_ctor_get(v___x_296_, 0);
v_used_298_ = lean_ctor_get(v___x_296_, 1);
v_binderRenaming_299_ = lean_ctor_get(v___x_296_, 2);
v_funDeclInfoMap_300_ = lean_ctor_get(v___x_296_, 3);
v_simplified_301_ = lean_ctor_get_uint8(v___x_296_, sizeof(void*)*7);
v_visited_302_ = lean_ctor_get(v___x_296_, 4);
v_inline_303_ = lean_ctor_get(v___x_296_, 5);
v_inlineLocal_304_ = lean_ctor_get(v___x_296_, 6);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_316_ == 0)
{
v___x_306_ = v___x_296_;
v_isShared_307_ = v_isSharedCheck_316_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_inlineLocal_304_);
lean_inc(v_inline_303_);
lean_inc(v_visited_302_);
lean_inc(v_funDeclInfoMap_300_);
lean_inc(v_binderRenaming_299_);
lean_inc(v_used_298_);
lean_inc(v_subst_297_);
lean_dec(v___x_296_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_316_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_inline_303_, v___x_308_);
lean_dec(v_inline_303_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 5, v___x_309_);
v___x_311_ = v___x_306_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_subst_297_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_used_298_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_binderRenaming_299_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_funDeclInfoMap_300_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v_visited_302_);
lean_ctor_set(v_reuseFailAlloc_315_, 5, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_315_, 6, v_inlineLocal_304_);
lean_ctor_set_uint8(v_reuseFailAlloc_315_, sizeof(void*)*7, v_simplified_301_);
v___x_311_ = v_reuseFailAlloc_315_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_st_ref_put(v_a_294_, v___x_311_);
v___x_313_ = lean_box(0);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___redArg___boxed(lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Compiler_LCNF_Simp_incInline___redArg(v_a_317_);
lean_dec(v_a_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline(lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Compiler_LCNF_Simp_incInline___redArg(v_a_321_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___boxed(lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Compiler_LCNF_Simp_incInline(v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; lean_object* v_subst_341_; lean_object* v_used_342_; lean_object* v_binderRenaming_343_; lean_object* v_funDeclInfoMap_344_; uint8_t v_simplified_345_; lean_object* v_visited_346_; lean_object* v_inline_347_; lean_object* v_inlineLocal_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_360_; 
v___x_340_ = lean_st_ref_take(v_a_338_);
v_subst_341_ = lean_ctor_get(v___x_340_, 0);
v_used_342_ = lean_ctor_get(v___x_340_, 1);
v_binderRenaming_343_ = lean_ctor_get(v___x_340_, 2);
v_funDeclInfoMap_344_ = lean_ctor_get(v___x_340_, 3);
v_simplified_345_ = lean_ctor_get_uint8(v___x_340_, sizeof(void*)*7);
v_visited_346_ = lean_ctor_get(v___x_340_, 4);
v_inline_347_ = lean_ctor_get(v___x_340_, 5);
v_inlineLocal_348_ = lean_ctor_get(v___x_340_, 6);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_360_ == 0)
{
v___x_350_ = v___x_340_;
v_isShared_351_ = v_isSharedCheck_360_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_inlineLocal_348_);
lean_inc(v_inline_347_);
lean_inc(v_visited_346_);
lean_inc(v_funDeclInfoMap_344_);
lean_inc(v_binderRenaming_343_);
lean_inc(v_used_342_);
lean_inc(v_subst_341_);
lean_dec(v___x_340_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_360_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_inlineLocal_348_, v___x_352_);
lean_dec(v_inlineLocal_348_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 6, v___x_353_);
v___x_355_ = v___x_350_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_subst_341_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_used_342_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_binderRenaming_343_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v_funDeclInfoMap_344_);
lean_ctor_set(v_reuseFailAlloc_359_, 4, v_visited_346_);
lean_ctor_set(v_reuseFailAlloc_359_, 5, v_inline_347_);
lean_ctor_set(v_reuseFailAlloc_359_, 6, v___x_353_);
lean_ctor_set_uint8(v_reuseFailAlloc_359_, sizeof(void*)*7, v_simplified_345_);
v___x_355_ = v_reuseFailAlloc_359_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_st_ref_put(v_a_338_, v___x_355_);
v___x_357_ = lean_box(0);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg___boxed(lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(v_a_361_);
lean_dec(v_a_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal(lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(v_a_365_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___boxed(lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal(v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(lean_object* v_fvarId_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_385_; lean_object* v_subst_386_; lean_object* v_used_387_; lean_object* v_binderRenaming_388_; lean_object* v_funDeclInfoMap_389_; uint8_t v_simplified_390_; lean_object* v_visited_391_; lean_object* v_inline_392_; lean_object* v_inlineLocal_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_404_; 
v___x_385_ = lean_st_ref_take(v_a_383_);
v_subst_386_ = lean_ctor_get(v___x_385_, 0);
v_used_387_ = lean_ctor_get(v___x_385_, 1);
v_binderRenaming_388_ = lean_ctor_get(v___x_385_, 2);
v_funDeclInfoMap_389_ = lean_ctor_get(v___x_385_, 3);
v_simplified_390_ = lean_ctor_get_uint8(v___x_385_, sizeof(void*)*7);
v_visited_391_ = lean_ctor_get(v___x_385_, 4);
v_inline_392_ = lean_ctor_get(v___x_385_, 5);
v_inlineLocal_393_ = lean_ctor_get(v___x_385_, 6);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_404_ == 0)
{
v___x_395_ = v___x_385_;
v_isShared_396_ = v_isSharedCheck_404_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_inlineLocal_393_);
lean_inc(v_inline_392_);
lean_inc(v_visited_391_);
lean_inc(v_funDeclInfoMap_389_);
lean_inc(v_binderRenaming_388_);
lean_inc(v_used_387_);
lean_inc(v_subst_386_);
lean_dec(v___x_385_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_404_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(v_funDeclInfoMap_389_, v_fvarId_382_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 3, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_subst_386_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_used_387_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_binderRenaming_388_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v_visited_391_);
lean_ctor_set(v_reuseFailAlloc_403_, 5, v_inline_392_);
lean_ctor_set(v_reuseFailAlloc_403_, 6, v_inlineLocal_393_);
lean_ctor_set_uint8(v_reuseFailAlloc_403_, sizeof(void*)*7, v_simplified_390_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = lean_st_ref_put(v_a_383_, v___x_399_);
v___x_401_ = lean_box(0);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___redArg___boxed(lean_object* v_fvarId_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_405_, v_a_406_);
lean_dec(v_a_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline(lean_object* v_fvarId_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_409_, v_a_411_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___boxed(lean_object* v_fvarId_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Compiler_LCNF_Simp_addMustInline(v_fvarId_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(lean_object* v_fvarId_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; lean_object* v_subst_433_; lean_object* v_used_434_; lean_object* v_binderRenaming_435_; lean_object* v_funDeclInfoMap_436_; uint8_t v_simplified_437_; lean_object* v_visited_438_; lean_object* v_inline_439_; lean_object* v_inlineLocal_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_451_; 
v___x_432_ = lean_st_ref_take(v_a_430_);
v_subst_433_ = lean_ctor_get(v___x_432_, 0);
v_used_434_ = lean_ctor_get(v___x_432_, 1);
v_binderRenaming_435_ = lean_ctor_get(v___x_432_, 2);
v_funDeclInfoMap_436_ = lean_ctor_get(v___x_432_, 3);
v_simplified_437_ = lean_ctor_get_uint8(v___x_432_, sizeof(void*)*7);
v_visited_438_ = lean_ctor_get(v___x_432_, 4);
v_inline_439_ = lean_ctor_get(v___x_432_, 5);
v_inlineLocal_440_ = lean_ctor_get(v___x_432_, 6);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_451_ == 0)
{
v___x_442_ = v___x_432_;
v_isShared_443_ = v_isSharedCheck_451_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_inlineLocal_440_);
lean_inc(v_inline_439_);
lean_inc(v_visited_438_);
lean_inc(v_funDeclInfoMap_436_);
lean_inc(v_binderRenaming_435_);
lean_inc(v_used_434_);
lean_inc(v_subst_433_);
lean_dec(v___x_432_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_451_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v_funDeclInfoMap_436_, v_fvarId_429_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 3, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_subst_433_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_used_434_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_binderRenaming_435_);
lean_ctor_set(v_reuseFailAlloc_450_, 3, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_450_, 4, v_visited_438_);
lean_ctor_set(v_reuseFailAlloc_450_, 5, v_inline_439_);
lean_ctor_set(v_reuseFailAlloc_450_, 6, v_inlineLocal_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_450_, sizeof(void*)*7, v_simplified_437_);
v___x_446_ = v_reuseFailAlloc_450_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_st_ref_put(v_a_430_, v___x_446_);
v___x_448_ = lean_box(0);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg___boxed(lean_object* v_fvarId_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(v_fvarId_452_, v_a_453_);
lean_dec(v_a_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc(lean_object* v_fvarId_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(v_fvarId_456_, v_a_458_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___boxed(lean_object* v_fvarId_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Compiler_LCNF_Simp_addFunOcc(v_fvarId_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(lean_object* v_fvarId_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; lean_object* v_subst_480_; lean_object* v_used_481_; lean_object* v_binderRenaming_482_; lean_object* v_funDeclInfoMap_483_; uint8_t v_simplified_484_; lean_object* v_visited_485_; lean_object* v_inline_486_; lean_object* v_inlineLocal_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_498_; 
v___x_479_ = lean_st_ref_take(v_a_477_);
v_subst_480_ = lean_ctor_get(v___x_479_, 0);
v_used_481_ = lean_ctor_get(v___x_479_, 1);
v_binderRenaming_482_ = lean_ctor_get(v___x_479_, 2);
v_funDeclInfoMap_483_ = lean_ctor_get(v___x_479_, 3);
v_simplified_484_ = lean_ctor_get_uint8(v___x_479_, sizeof(void*)*7);
v_visited_485_ = lean_ctor_get(v___x_479_, 4);
v_inline_486_ = lean_ctor_get(v___x_479_, 5);
v_inlineLocal_487_ = lean_ctor_get(v___x_479_, 6);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_498_ == 0)
{
v___x_489_ = v___x_479_;
v_isShared_490_ = v_isSharedCheck_498_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_inlineLocal_487_);
lean_inc(v_inline_486_);
lean_inc(v_visited_485_);
lean_inc(v_funDeclInfoMap_483_);
lean_inc(v_binderRenaming_482_);
lean_inc(v_used_481_);
lean_inc(v_subst_480_);
lean_dec(v___x_479_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_498_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(v_funDeclInfoMap_483_, v_fvarId_476_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 3, v___x_491_);
v___x_493_ = v___x_489_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_subst_480_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_used_481_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_binderRenaming_482_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v_visited_485_);
lean_ctor_set(v_reuseFailAlloc_497_, 5, v_inline_486_);
lean_ctor_set(v_reuseFailAlloc_497_, 6, v_inlineLocal_487_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*7, v_simplified_484_);
v___x_493_ = v_reuseFailAlloc_497_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_st_ref_put(v_a_477_, v___x_493_);
v___x_495_ = lean_box(0);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg___boxed(lean_object* v_fvarId_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(v_fvarId_499_, v_a_500_);
lean_dec(v_a_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc(lean_object* v_fvarId_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(v_fvarId_503_, v_a_505_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___boxed(lean_object* v_fvarId_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc(v_fvarId_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
return v_res_522_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_523_; lean_object* v___x_524_; 
v_cellCount_523_ = lean_unsigned_to_nat(16u);
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_523_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_525_; lean_object* v___x_526_; 
v_cellCount_525_ = lean_unsigned_to_nat(16u);
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_525_);
return v___x_526_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__2(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_527_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1);
v___x_528_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___x_528_);
lean_ctor_set(v___x_530_, 2, v___x_527_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object* v_code_531_, uint8_t v_mustInline_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_539_; lean_object* v_subst_540_; lean_object* v_used_541_; lean_object* v_binderRenaming_542_; lean_object* v_funDeclInfoMap_543_; uint8_t v_simplified_544_; lean_object* v_visited_545_; lean_object* v_inline_546_; lean_object* v_inlineLocal_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_591_; 
v___x_539_ = lean_st_ref_take(v_a_533_);
v_subst_540_ = lean_ctor_get(v___x_539_, 0);
v_used_541_ = lean_ctor_get(v___x_539_, 1);
v_binderRenaming_542_ = lean_ctor_get(v___x_539_, 2);
v_funDeclInfoMap_543_ = lean_ctor_get(v___x_539_, 3);
v_simplified_544_ = lean_ctor_get_uint8(v___x_539_, sizeof(void*)*7);
v_visited_545_ = lean_ctor_get(v___x_539_, 4);
v_inline_546_ = lean_ctor_get(v___x_539_, 5);
v_inlineLocal_547_ = lean_ctor_get(v___x_539_, 6);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_591_ == 0)
{
v___x_549_ = v___x_539_;
v_isShared_550_ = v_isSharedCheck_591_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_inlineLocal_547_);
lean_inc(v_inline_546_);
lean_inc(v_visited_545_);
lean_inc(v_funDeclInfoMap_543_);
lean_inc(v_binderRenaming_542_);
lean_inc(v_used_541_);
lean_inc(v_subst_540_);
lean_dec(v___x_539_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_591_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__2, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__2);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 3, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_subst_540_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_used_541_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_binderRenaming_542_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_590_, 4, v_visited_545_);
lean_ctor_set(v_reuseFailAlloc_590_, 5, v_inline_546_);
lean_ctor_set(v_reuseFailAlloc_590_, 6, v_inlineLocal_547_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*7, v_simplified_544_);
v___x_553_ = v_reuseFailAlloc_590_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_st_ref_put(v_a_533_, v___x_553_);
v___x_555_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(v_funDeclInfoMap_543_, v_code_531_, v_mustInline_532_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_581_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_581_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_581_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_581_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v_subst_561_; lean_object* v_used_562_; lean_object* v_binderRenaming_563_; uint8_t v_simplified_564_; lean_object* v_visited_565_; lean_object* v_inline_566_; lean_object* v_inlineLocal_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_579_; 
v___x_560_ = lean_st_ref_take(v_a_533_);
v_subst_561_ = lean_ctor_get(v___x_560_, 0);
v_used_562_ = lean_ctor_get(v___x_560_, 1);
v_binderRenaming_563_ = lean_ctor_get(v___x_560_, 2);
v_simplified_564_ = lean_ctor_get_uint8(v___x_560_, sizeof(void*)*7);
v_visited_565_ = lean_ctor_get(v___x_560_, 4);
v_inline_566_ = lean_ctor_get(v___x_560_, 5);
v_inlineLocal_567_ = lean_ctor_get(v___x_560_, 6);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v___x_560_, 3);
lean_dec(v_unused_580_);
v___x_569_ = v___x_560_;
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_inlineLocal_567_);
lean_inc(v_inline_566_);
lean_inc(v_visited_565_);
lean_inc(v_binderRenaming_563_);
lean_inc(v_used_562_);
lean_inc(v_subst_561_);
lean_dec(v___x_560_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 3, v_a_556_);
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_subst_561_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_used_562_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_binderRenaming_563_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_a_556_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_visited_565_);
lean_ctor_set(v_reuseFailAlloc_578_, 5, v_inline_566_);
lean_ctor_set(v_reuseFailAlloc_578_, 6, v_inlineLocal_567_);
lean_ctor_set_uint8(v_reuseFailAlloc_578_, sizeof(void*)*7, v_simplified_564_);
v___x_572_ = v_reuseFailAlloc_578_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_573_ = lean_st_ref_put(v_a_533_, v___x_572_);
v___x_574_ = lean_box(0);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_574_);
v___x_576_ = v___x_558_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_555_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_555_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___boxed(lean_object* v_code_592_, lean_object* v_mustInline_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
uint8_t v_mustInline_boxed_600_; lean_object* v_res_601_; 
v_mustInline_boxed_600_ = lean_unbox(v_mustInline_593_);
v_res_601_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_592_, v_mustInline_boxed_600_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object* v_code_602_, uint8_t v_mustInline_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_602_, v_mustInline_603_, v_a_605_, v_a_607_, v_a_608_, v_a_609_, v_a_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___boxed(lean_object* v_code_613_, lean_object* v_mustInline_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
uint8_t v_mustInline_boxed_623_; lean_object* v_res_624_; 
v_mustInline_boxed_623_ = lean_unbox(v_mustInline_614_);
v_res_624_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(v_code_613_, v_mustInline_boxed_623_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
return v_res_624_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_625_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
lean_ctor_set(v___x_630_, 2, v___x_629_);
lean_ctor_set(v___x_630_, 3, v___x_629_);
lean_ctor_set(v___x_630_, 4, v___x_628_);
lean_ctor_set(v___x_630_, 5, v___x_628_);
lean_ctor_set(v___x_630_, 6, v___x_628_);
lean_ctor_set(v___x_630_, 7, v___x_628_);
lean_ctor_set(v___x_630_, 8, v___x_628_);
lean_ctor_set(v___x_630_, 9, v___x_628_);
lean_ctor_set(v___x_630_, 10, v___x_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(lean_object* v_msg_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_options_637_; lean_object* v_ref_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_options_637_ = lean_ctor_get(v___y_634_, 2);
v_ref_638_ = lean_ctor_get(v___y_634_, 5);
v___x_639_ = lean_st_ref_get(v___y_635_);
v___x_640_ = lean_st_ref_get(v___y_633_);
v___x_641_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_632_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_664_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_664_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_664_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_664_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v_env_646_; lean_object* v_lctx_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_662_; 
v_env_646_ = lean_ctor_get(v___x_639_, 0);
lean_inc_ref(v_env_646_);
lean_dec(v___x_639_);
v_lctx_647_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v___x_640_, 1);
lean_dec(v_unused_663_);
v___x_649_ = v___x_640_;
v_isShared_650_ = v_isSharedCheck_662_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_lctx_647_);
lean_dec(v___x_640_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_662_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_651_ = lean_unbox(v_a_642_);
lean_dec(v_a_642_);
v___x_652_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_647_, v___x_651_);
lean_dec_ref(v_lctx_647_);
v___x_653_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2);
lean_inc_ref(v_options_637_);
v___x_654_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_654_, 0, v_env_646_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
lean_ctor_set(v___x_654_, 2, v___x_652_);
lean_ctor_set(v___x_654_, 3, v_options_637_);
if (v_isShared_650_ == 0)
{
lean_ctor_set_tag(v___x_649_, 3);
lean_ctor_set(v___x_649_, 1, v_msg_631_);
lean_ctor_set(v___x_649_, 0, v___x_654_);
v___x_656_ = v___x_649_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_msg_631_);
v___x_656_ = v_reuseFailAlloc_661_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
lean_inc(v_ref_638_);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v_ref_638_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 1);
lean_ctor_set(v___x_644_, 0, v___x_657_);
v___x_659_ = v___x_644_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v___x_640_);
lean_dec(v___x_639_);
lean_dec_ref(v_msg_631_);
v_a_665_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_641_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_641_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___boxed(lean_object* v_msg_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v_msg_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0(lean_object* v_00_u03b1_680_, lean_object* v_msg_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v_msg_681_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___boxed(lean_object* v_00_u03b1_691_, lean_object* v_msg_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0(v_00_u03b1_691_, v_msg_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_701_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_702_; double v___x_703_; 
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_float_of_nat(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(lean_object* v_cls_707_, lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_options_714_; lean_object* v_ref_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_options_714_ = lean_ctor_get(v___y_711_, 2);
v_ref_715_ = lean_ctor_get(v___y_711_, 5);
v___x_716_ = lean_st_ref_get(v___y_712_);
v___x_717_ = lean_st_ref_get(v___y_710_);
v___x_718_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_709_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_777_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_777_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_777_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_777_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v_env_723_; lean_object* v_lctx_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_775_; 
v_env_723_ = lean_ctor_get(v___x_716_, 0);
lean_inc_ref(v_env_723_);
lean_dec(v___x_716_);
v_lctx_724_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v___x_717_, 1);
lean_dec(v_unused_776_);
v___x_726_ = v___x_717_;
v_isShared_727_ = v_isSharedCheck_775_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_lctx_724_);
lean_dec(v___x_717_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_775_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_traceState_730_; lean_object* v_env_731_; lean_object* v_nextMacroScope_732_; lean_object* v_ngen_733_; lean_object* v_auxDeclNGen_734_; lean_object* v_cache_735_; lean_object* v_messages_736_; lean_object* v_infoState_737_; lean_object* v_snapshotTasks_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_774_; 
v___x_728_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2);
v___x_729_ = lean_st_ref_take(v___y_712_);
v_traceState_730_ = lean_ctor_get(v___x_729_, 4);
v_env_731_ = lean_ctor_get(v___x_729_, 0);
v_nextMacroScope_732_ = lean_ctor_get(v___x_729_, 1);
v_ngen_733_ = lean_ctor_get(v___x_729_, 2);
v_auxDeclNGen_734_ = lean_ctor_get(v___x_729_, 3);
v_cache_735_ = lean_ctor_get(v___x_729_, 5);
v_messages_736_ = lean_ctor_get(v___x_729_, 6);
v_infoState_737_ = lean_ctor_get(v___x_729_, 7);
v_snapshotTasks_738_ = lean_ctor_get(v___x_729_, 8);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_774_ == 0)
{
v___x_740_ = v___x_729_;
v_isShared_741_ = v_isSharedCheck_774_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_snapshotTasks_738_);
lean_inc(v_infoState_737_);
lean_inc(v_messages_736_);
lean_inc(v_cache_735_);
lean_inc(v_traceState_730_);
lean_inc(v_auxDeclNGen_734_);
lean_inc(v_ngen_733_);
lean_inc(v_nextMacroScope_732_);
lean_inc(v_env_731_);
lean_dec(v___x_729_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_774_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
uint64_t v_tid_742_; lean_object* v_traces_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_773_; 
v_tid_742_ = lean_ctor_get_uint64(v_traceState_730_, sizeof(void*)*1);
v_traces_743_ = lean_ctor_get(v_traceState_730_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v_traceState_730_);
if (v_isSharedCheck_773_ == 0)
{
v___x_745_ = v_traceState_730_;
v_isShared_746_ = v_isSharedCheck_773_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_traces_743_);
lean_dec(v_traceState_730_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_773_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_747_ = lean_unbox(v_a_719_);
lean_dec(v_a_719_);
v___x_748_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_724_, v___x_747_);
lean_dec_ref(v_lctx_724_);
lean_inc_ref(v_options_714_);
v___x_749_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_749_, 0, v_env_723_);
lean_ctor_set(v___x_749_, 1, v___x_728_);
lean_ctor_set(v___x_749_, 2, v___x_748_);
lean_ctor_set(v___x_749_, 3, v_options_714_);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 3);
lean_ctor_set(v___x_726_, 1, v_msg_708_);
lean_ctor_set(v___x_726_, 0, v___x_749_);
v___x_751_ = v___x_726_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_msg_708_);
v___x_751_ = v_reuseFailAlloc_772_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; double v___x_753_; uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_752_ = lean_box(0);
v___x_753_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0);
v___x_754_ = 0;
v___x_755_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1));
v___x_756_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_756_, 0, v_cls_707_);
lean_ctor_set(v___x_756_, 1, v___x_752_);
lean_ctor_set(v___x_756_, 2, v___x_755_);
lean_ctor_set_float(v___x_756_, sizeof(void*)*3, v___x_753_);
lean_ctor_set_float(v___x_756_, sizeof(void*)*3 + 8, v___x_753_);
lean_ctor_set_uint8(v___x_756_, sizeof(void*)*3 + 16, v___x_754_);
v___x_757_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__2));
v___x_758_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_751_);
lean_ctor_set(v___x_758_, 2, v___x_757_);
lean_inc(v_ref_715_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_ref_715_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_PersistentArray_push___redArg(v_traces_743_, v___x_759_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_760_);
v___x_762_ = v___x_745_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_760_);
lean_ctor_set_uint64(v_reuseFailAlloc_771_, sizeof(void*)*1, v_tid_742_);
v___x_762_ = v_reuseFailAlloc_771_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_764_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 4, v___x_762_);
v___x_764_ = v___x_740_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_env_731_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_nextMacroScope_732_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_ngen_733_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_auxDeclNGen_734_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_770_, 5, v_cache_735_);
lean_ctor_set(v_reuseFailAlloc_770_, 6, v_messages_736_);
lean_ctor_set(v_reuseFailAlloc_770_, 7, v_infoState_737_);
lean_ctor_set(v_reuseFailAlloc_770_, 8, v_snapshotTasks_738_);
v___x_764_ = v_reuseFailAlloc_770_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_765_ = lean_st_ref_put(v___y_712_, v___x_764_);
v___x_766_ = lean_box(0);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_766_);
v___x_768_ = v___x_721_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
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
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec(v___x_717_);
lean_dec(v___x_716_);
lean_dec_ref(v_msg_708_);
lean_dec(v_cls_707_);
v_a_778_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_718_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_718_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___boxed(lean_object* v_cls_786_, lean_object* v_msg_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_786_, v_msg_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(lean_object* v_cls_794_, lean_object* v_msg_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_794_, v_msg_795_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___boxed(lean_object* v_cls_805_, lean_object* v_msg_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(v_cls_805_, v_msg_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(lean_object* v_keys_816_, lean_object* v_vals_817_, lean_object* v_i_818_, lean_object* v_k_819_){
_start:
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = lean_array_get_size(v_keys_816_);
v___x_821_ = lean_nat_dec_lt(v_i_818_, v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
lean_dec(v_i_818_);
v___x_822_ = lean_box(0);
return v___x_822_;
}
else
{
lean_object* v_k_x27_823_; uint8_t v___x_824_; 
v_k_x27_823_ = lean_array_fget_borrowed(v_keys_816_, v_i_818_);
v___x_824_ = lean_name_eq(v_k_819_, v_k_x27_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(1u);
v___x_826_ = lean_nat_add(v_i_818_, v___x_825_);
lean_dec(v_i_818_);
v_i_818_ = v___x_826_;
goto _start;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_array_fget_borrowed(v_vals_817_, v_i_818_);
lean_dec(v_i_818_);
lean_inc(v___x_828_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_keys_830_, lean_object* v_vals_831_, lean_object* v_i_832_, lean_object* v_k_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(v_keys_830_, v_vals_831_, v_i_832_, v_k_833_);
lean_dec(v_k_833_);
lean_dec_ref(v_vals_831_);
lean_dec_ref(v_keys_830_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(lean_object* v_x_835_, size_t v_x_836_, lean_object* v_x_837_){
_start:
{
if (lean_obj_tag(v_x_835_) == 0)
{
lean_object* v_es_838_; lean_object* v___x_839_; size_t v___x_840_; size_t v___x_841_; lean_object* v_j_842_; lean_object* v___x_843_; 
v_es_838_ = lean_ctor_get(v_x_835_, 0);
v___x_839_ = lean_box(2);
v___x_840_ = ((size_t)31ULL);
v___x_841_ = lean_usize_land(v_x_836_, v___x_840_);
v_j_842_ = lean_usize_to_nat(v___x_841_);
v___x_843_ = lean_array_get_borrowed(v___x_839_, v_es_838_, v_j_842_);
lean_dec(v_j_842_);
switch(lean_obj_tag(v___x_843_))
{
case 0:
{
lean_object* v_key_844_; lean_object* v_val_845_; uint8_t v___x_846_; 
v_key_844_ = lean_ctor_get(v___x_843_, 0);
v_val_845_ = lean_ctor_get(v___x_843_, 1);
v___x_846_ = lean_name_eq(v_x_837_, v_key_844_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
v___x_847_ = lean_box(0);
return v___x_847_;
}
else
{
lean_object* v___x_848_; 
lean_inc(v_val_845_);
v___x_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_848_, 0, v_val_845_);
return v___x_848_;
}
}
case 1:
{
lean_object* v_node_849_; size_t v___x_850_; size_t v___x_851_; 
v_node_849_ = lean_ctor_get(v___x_843_, 0);
v___x_850_ = ((size_t)5ULL);
v___x_851_ = lean_usize_shift_right(v_x_836_, v___x_850_);
v_x_835_ = v_node_849_;
v_x_836_ = v___x_851_;
goto _start;
}
default: 
{
lean_object* v___x_853_; 
v___x_853_ = lean_box(0);
return v___x_853_;
}
}
}
else
{
lean_object* v_ks_854_; lean_object* v_vs_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v_ks_854_ = lean_ctor_get(v_x_835_, 0);
v_vs_855_ = lean_ctor_get(v_x_835_, 1);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(v_ks_854_, v_vs_855_, v___x_856_, v_x_837_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___boxed(lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
size_t v_x_7672__boxed_861_; lean_object* v_res_862_; 
v_x_7672__boxed_861_ = lean_unbox_usize(v_x_859_);
lean_dec(v_x_859_);
v_res_862_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_858_, v_x_7672__boxed_861_, v_x_860_);
lean_dec(v_x_860_);
lean_dec_ref(v_x_858_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
uint64_t v___y_866_; 
if (lean_obj_tag(v_x_864_) == 0)
{
uint64_t v___x_869_; 
v___x_869_ = 1723ULL;
v___y_866_ = v___x_869_;
goto v___jp_865_;
}
else
{
uint64_t v_hash_870_; 
v_hash_870_ = lean_ctor_get_uint64(v_x_864_, sizeof(void*)*2);
v___y_866_ = v_hash_870_;
goto v___jp_865_;
}
v___jp_865_:
{
size_t v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_uint64_to_usize(v___y_866_);
v___x_868_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_863_, v___x_867_, v_x_864_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___boxed(lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_x_871_, v_x_872_);
lean_dec(v_x_872_);
lean_dec_ref(v_x_871_);
return v_res_873_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__0));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__2));
v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__4));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12(void){
_start:
{
lean_object* v_cls_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_cls_893_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9));
v___x_894_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__11));
v___x_895_ = l_Lean_Name_append(v___x_894_, v_cls_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t v_recursive_896_, lean_object* v_declName_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___y_907_; uint8_t v_inlineIfReduce_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v_options_1030_; uint8_t v_hasTrace_1031_; 
v_options_1030_ = lean_ctor_get(v_a_903_, 2);
v_hasTrace_1031_ = lean_ctor_get_uint8(v_options_1030_, sizeof(void*)*1);
if (v_hasTrace_1031_ == 0)
{
v___y_1019_ = v_a_898_;
v___y_1020_ = v_a_899_;
v___y_1021_ = v_a_900_;
v___y_1022_ = v_a_901_;
v___y_1023_ = v_a_902_;
v___y_1024_ = v_a_903_;
v___y_1025_ = v_a_904_;
goto v___jp_1018_;
}
else
{
lean_object* v_inheritedTraceOptions_1032_; lean_object* v_cls_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_inheritedTraceOptions_1032_ = lean_ctor_get(v_a_903_, 13);
v_cls_1033_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9));
v___x_1034_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12);
v___x_1035_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1032_, v_options_1030_, v___x_1034_);
if (v___x_1035_ == 0)
{
v___y_1019_ = v_a_898_;
v___y_1020_ = v_a_899_;
v___y_1021_ = v_a_900_;
v___y_1022_ = v_a_901_;
v___y_1023_ = v_a_902_;
v___y_1024_ = v_a_903_;
v___y_1025_ = v_a_904_;
goto v___jp_1018_;
}
else
{
uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = 0;
lean_inc(v_declName_897_);
v___x_1037_ = l_Lean_MessageData_ofConstName(v_declName_897_, v___x_1036_);
v___x_1038_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_1033_, v___x_1037_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_dec_ref_known(v___x_1038_, 1);
v___y_1019_ = v_a_898_;
v___y_1020_ = v_a_899_;
v___y_1021_ = v_a_900_;
v___y_1022_ = v_a_901_;
v___y_1023_ = v_a_902_;
v___y_1024_ = v_a_903_;
v___y_1025_ = v_a_904_;
goto v___jp_1018_;
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_declName_897_);
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
v___jp_906_:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_912_);
if (lean_obj_tag(v___x_916_) == 0)
{
if (v_recursive_896_ == 0)
{
lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_declName_897_);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v___x_916_, 0);
lean_dec(v_unused_924_);
v___x_918_ = v___x_916_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_dec(v___x_916_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___y_907_);
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___y_907_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
if (v_inlineIfReduce_908_ == 0)
{
lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_declName_897_);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v___x_916_, 0);
lean_dec(v_unused_932_);
v___x_926_ = v___x_916_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_dec(v___x_916_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___y_907_);
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___y_907_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_974_; 
v_a_933_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_974_ == 0)
{
v___x_935_ = v___x_916_;
v_isShared_936_ = v_isSharedCheck_974_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_916_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_974_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_maxRecInlineIfReduce_937_; uint8_t v___x_938_; 
v_maxRecInlineIfReduce_937_ = lean_ctor_get(v_a_933_, 2);
lean_inc(v_maxRecInlineIfReduce_937_);
lean_dec(v_a_933_);
v___x_938_ = lean_nat_dec_lt(v_maxRecInlineIfReduce_937_, v___y_907_);
lean_dec(v_maxRecInlineIfReduce_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_940_; 
lean_dec(v_declName_897_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___y_907_);
v___x_940_ = v___x_935_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___y_907_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
else
{
lean_object* v___x_942_; 
lean_del_object(v___x_935_);
lean_dec(v___y_907_);
v___x_942_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_912_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v_maxRecInlineIfReduce_944_; lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v_maxRecInlineIfReduce_944_ = lean_ctor_get(v_a_943_, 2);
lean_inc(v_maxRecInlineIfReduce_944_);
lean_dec(v_a_943_);
v___x_945_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1);
v___x_946_ = 0;
v___x_947_ = l_Lean_MessageData_ofConstName(v_declName_897_, v___x_946_);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_945_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l_Nat_reprFast(v_maxRecInlineIfReduce_944_);
v___x_952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
v___x_953_ = l_Lean_MessageData_ofFormat(v___x_952_);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_950_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5);
v___x_956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_956_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_declName_897_);
v_a_966_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_942_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_942_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
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
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v___y_907_);
lean_dec(v_declName_897_);
v_a_975_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_916_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_916_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
v___jp_983_:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_984_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; uint8_t v___x_994_; lean_object* v___x_995_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = lean_unbox(v_a_993_);
lean_dec(v_a_993_);
lean_inc(v_declName_897_);
v___x_995_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_897_, v___x_994_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_add(v___y_991_, v___x_997_);
lean_dec(v___y_991_);
if (lean_obj_tag(v_a_996_) == 1)
{
lean_object* v_val_999_; uint8_t v___x_1000_; 
v_val_999_ = lean_ctor_get(v_a_996_, 0);
lean_inc(v_val_999_);
lean_dec_ref_known(v_a_996_, 1);
v___x_1000_ = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(v_val_999_);
lean_dec(v_val_999_);
v___y_907_ = v___x_998_;
v_inlineIfReduce_908_ = v___x_1000_;
v___y_909_ = v___y_990_;
v___y_910_ = v___y_985_;
v___y_911_ = v___y_989_;
v___y_912_ = v___y_984_;
v___y_913_ = v___y_988_;
v___y_914_ = v___y_986_;
v___y_915_ = v___y_987_;
goto v___jp_906_;
}
else
{
uint8_t v___x_1001_; 
lean_dec(v_a_996_);
v___x_1001_ = 0;
v___y_907_ = v___x_998_;
v_inlineIfReduce_908_ = v___x_1001_;
v___y_909_ = v___y_990_;
v___y_910_ = v___y_985_;
v___y_911_ = v___y_989_;
v___y_912_ = v___y_984_;
v___y_913_ = v___y_988_;
v___y_914_ = v___y_986_;
v___y_915_ = v___y_987_;
goto v___jp_906_;
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec(v___y_991_);
lean_dec(v_declName_897_);
v_a_1002_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_995_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_995_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v___y_991_);
lean_dec(v_declName_897_);
v_a_1010_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_992_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_992_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
v___jp_1018_:
{
lean_object* v_inlineStackOccs_1026_; lean_object* v___x_1027_; 
v_inlineStackOccs_1026_ = lean_ctor_get(v___y_1019_, 3);
v___x_1027_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_inlineStackOccs_1026_, v_declName_897_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_unsigned_to_nat(0u);
v___y_984_ = v___y_1022_;
v___y_985_ = v___y_1020_;
v___y_986_ = v___y_1024_;
v___y_987_ = v___y_1025_;
v___y_988_ = v___y_1023_;
v___y_989_ = v___y_1021_;
v___y_990_ = v___y_1019_;
v___y_991_ = v___x_1028_;
goto v___jp_983_;
}
else
{
lean_object* v_val_1029_; 
v_val_1029_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v___x_1027_, 1);
v___y_984_ = v___y_1022_;
v___y_985_ = v___y_1020_;
v___y_986_ = v___y_1024_;
v___y_987_ = v___y_1025_;
v___y_988_ = v___y_1023_;
v___y_989_ = v___y_1021_;
v___y_990_ = v___y_1019_;
v___y_991_ = v_val_1029_;
goto v___jp_983_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___boxed(lean_object* v_recursive_1047_, lean_object* v_declName_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
uint8_t v_recursive_boxed_1057_; lean_object* v_res_1058_; 
v_recursive_boxed_1057_ = lean_unbox(v_recursive_1047_);
v_res_1058_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_boxed_1057_, v_declName_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1(lean_object* v_00_u03b2_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_x_1060_, v_x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___boxed(lean_object* v_00_u03b2_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1(v_00_u03b2_1063_, v_x_1064_, v_x_1065_);
lean_dec(v_x_1065_);
lean_dec_ref(v_x_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(lean_object* v_00_u03b2_1067_, lean_object* v_x_1068_, size_t v_x_1069_, lean_object* v_x_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_1068_, v_x_1069_, v_x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
size_t v_x_8082__boxed_1076_; lean_object* v_res_1077_; 
v_x_8082__boxed_1076_ = lean_unbox_usize(v_x_1074_);
lean_dec(v_x_1074_);
v_res_1077_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(v_00_u03b2_1072_, v_x_1073_, v_x_8082__boxed_1076_, v_x_1075_);
lean_dec(v_x_1075_);
lean_dec_ref(v_x_1073_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1078_, lean_object* v_keys_1079_, lean_object* v_vals_1080_, lean_object* v_heq_1081_, lean_object* v_i_1082_, lean_object* v_k_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(v_keys_1079_, v_vals_1080_, v_i_1082_, v_k_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1085_, lean_object* v_keys_1086_, lean_object* v_vals_1087_, lean_object* v_heq_1088_, lean_object* v_i_1089_, lean_object* v_k_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3(v_00_u03b2_1085_, v_keys_1086_, v_vals_1087_, v_heq_1088_, v_i_1089_, v_k_1090_);
lean_dec(v_k_1090_);
lean_dec_ref(v_vals_1087_);
lean_dec_ref(v_keys_1086_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg(lean_object* v_value_1094_, uint8_t v_recursive_1095_, lean_object* v_x_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
if (lean_obj_tag(v_value_1094_) == 3)
{
lean_object* v_declName_1105_; lean_object* v___x_1106_; 
v_declName_1105_ = lean_ctor_get(v_value_1094_, 0);
lean_inc_n(v_declName_1105_, 2);
lean_dec_ref_known(v_value_1094_, 3);
v___x_1106_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1095_, v_declName_1105_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v_declName_1108_; lean_object* v_config_1109_; lean_object* v_inlineStack_1110_; lean_object* v_inlineStackOccs_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1106_, 1);
v_declName_1108_ = lean_ctor_get(v_a_1097_, 0);
v_config_1109_ = lean_ctor_get(v_a_1097_, 1);
v_inlineStack_1110_ = lean_ctor_get(v_a_1097_, 2);
v_inlineStackOccs_1111_ = lean_ctor_get(v_a_1097_, 3);
v___x_1112_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0));
v___x_1113_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1));
lean_inc(v_inlineStack_1110_);
lean_inc(v_declName_1105_);
v___x_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1114_, 0, v_declName_1105_);
lean_ctor_set(v___x_1114_, 1, v_inlineStack_1110_);
lean_inc_ref(v_inlineStackOccs_1111_);
v___x_1115_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1112_, v___x_1113_, v_inlineStackOccs_1111_, v_declName_1105_, v_a_1107_);
lean_inc_ref(v_config_1109_);
lean_inc(v_declName_1108_);
v___x_1116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1116_, 0, v_declName_1108_);
lean_ctor_set(v___x_1116_, 1, v_config_1109_);
lean_ctor_set(v___x_1116_, 2, v___x_1114_);
lean_ctor_set(v___x_1116_, 3, v___x_1115_);
lean_inc(v_a_1103_);
lean_inc_ref(v_a_1102_);
lean_inc(v_a_1101_);
lean_inc_ref(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc(v_a_1098_);
v___x_1117_ = lean_apply_8(v_x_1096_, v___x_1116_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, lean_box(0));
return v___x_1117_;
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_declName_1105_);
lean_dec_ref(v_x_1096_);
v_a_1118_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1106_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1106_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v___x_1126_; 
lean_dec(v_value_1094_);
lean_inc(v_a_1103_);
lean_inc_ref(v_a_1102_);
lean_inc(v_a_1101_);
lean_inc_ref(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc(v_a_1098_);
lean_inc_ref(v_a_1097_);
v___x_1126_ = lean_apply_8(v_x_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, lean_box(0));
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg___boxed(lean_object* v_value_1127_, lean_object* v_recursive_1128_, lean_object* v_x_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
uint8_t v_recursive_boxed_1138_; lean_object* v_res_1139_; 
v_recursive_boxed_1138_ = lean_unbox(v_recursive_1128_);
v_res_1139_ = l_Lean_Compiler_LCNF_Simp_withInlining___redArg(v_value_1127_, v_recursive_boxed_1138_, v_x_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining(lean_object* v_00_u03b1_1140_, lean_object* v_value_1141_, uint8_t v_recursive_1142_, lean_object* v_x_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
if (lean_obj_tag(v_value_1141_) == 3)
{
lean_object* v_declName_1152_; lean_object* v___x_1153_; 
v_declName_1152_ = lean_ctor_get(v_value_1141_, 0);
lean_inc_n(v_declName_1152_, 2);
lean_dec_ref_known(v_value_1141_, 3);
v___x_1153_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1142_, v_declName_1152_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v_declName_1155_; lean_object* v_config_1156_; lean_object* v_inlineStack_1157_; lean_object* v_inlineStackOccs_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1153_, 1);
v_declName_1155_ = lean_ctor_get(v_a_1144_, 0);
v_config_1156_ = lean_ctor_get(v_a_1144_, 1);
v_inlineStack_1157_ = lean_ctor_get(v_a_1144_, 2);
v_inlineStackOccs_1158_ = lean_ctor_get(v_a_1144_, 3);
v___x_1159_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0));
v___x_1160_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1));
lean_inc(v_inlineStack_1157_);
lean_inc(v_declName_1152_);
v___x_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_declName_1152_);
lean_ctor_set(v___x_1161_, 1, v_inlineStack_1157_);
lean_inc_ref(v_inlineStackOccs_1158_);
v___x_1162_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1159_, v___x_1160_, v_inlineStackOccs_1158_, v_declName_1152_, v_a_1154_);
lean_inc_ref(v_config_1156_);
lean_inc(v_declName_1155_);
v___x_1163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1163_, 0, v_declName_1155_);
lean_ctor_set(v___x_1163_, 1, v_config_1156_);
lean_ctor_set(v___x_1163_, 2, v___x_1161_);
lean_ctor_set(v___x_1163_, 3, v___x_1162_);
lean_inc(v_a_1150_);
lean_inc_ref(v_a_1149_);
lean_inc(v_a_1148_);
lean_inc_ref(v_a_1147_);
lean_inc_ref(v_a_1146_);
lean_inc(v_a_1145_);
v___x_1164_ = lean_apply_8(v_x_1143_, v___x_1163_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, lean_box(0));
return v___x_1164_;
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v_declName_1152_);
lean_dec_ref(v_x_1143_);
v_a_1165_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1153_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1153_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
lean_object* v___x_1173_; 
lean_dec(v_value_1141_);
lean_inc(v_a_1150_);
lean_inc_ref(v_a_1149_);
lean_inc(v_a_1148_);
lean_inc_ref(v_a_1147_);
lean_inc_ref(v_a_1146_);
lean_inc(v_a_1145_);
lean_inc_ref(v_a_1144_);
v___x_1173_ = lean_apply_8(v_x_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, lean_box(0));
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___boxed(lean_object* v_00_u03b1_1174_, lean_object* v_value_1175_, lean_object* v_recursive_1176_, lean_object* v_x_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
uint8_t v_recursive_boxed_1186_; lean_object* v_res_1187_; 
v_recursive_boxed_1186_ = lean_unbox(v_recursive_1176_);
v_res_1187_ = l_Lean_Compiler_LCNF_Simp_withInlining(v_00_u03b1_1174_, v_value_1175_, v_recursive_boxed_1186_, v_x_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
return v_res_1187_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__0));
v___x_1190_ = l_Lean_stringToMessageData(v___x_1189_);
return v___x_1190_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__3));
v___x_1195_ = l_Lean_MessageData_ofFormat(v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(lean_object* v_as_x27_1196_, lean_object* v_b_1197_){
_start:
{
if (lean_obj_tag(v_as_x27_1196_) == 0)
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v_b_1197_);
return v___x_1199_;
}
else
{
lean_object* v_snd_1200_; lean_object* v_head_1201_; lean_object* v_tail_1202_; lean_object* v_fst_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1244_; 
v_snd_1200_ = lean_ctor_get(v_b_1197_, 1);
lean_inc(v_snd_1200_);
v_head_1201_ = lean_ctor_get(v_as_x27_1196_, 0);
v_tail_1202_ = lean_ctor_get(v_as_x27_1196_, 1);
v_fst_1203_ = lean_ctor_get(v_b_1197_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_b_1197_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v_b_1197_, 1);
lean_dec(v_unused_1245_);
v___x_1205_ = v_b_1197_;
v_isShared_1206_ = v_isSharedCheck_1244_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_fst_1203_);
lean_dec(v_b_1197_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1244_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v_fst_1207_; lean_object* v_snd_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1243_; 
v_fst_1207_ = lean_ctor_get(v_snd_1200_, 0);
v_snd_1208_ = lean_ctor_get(v_snd_1200_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_snd_1200_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1210_ = v_snd_1200_;
v_isShared_1211_ = v_isSharedCheck_1243_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_snd_1208_);
lean_inc(v_fst_1207_);
lean_dec(v_snd_1200_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1243_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_name_eq(v_fst_1207_, v_head_1201_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
lean_dec(v_snd_1208_);
lean_dec(v_fst_1207_);
v___x_1213_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1);
lean_inc_n(v_head_1201_, 2);
v___x_1214_ = l_Lean_MessageData_ofConstName(v_head_1201_, v___x_1212_);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1213_);
v___x_1216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_fst_1203_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = lean_box(v___x_1212_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v___x_1217_);
lean_ctor_set(v___x_1210_, 0, v_head_1201_);
v___x_1219_ = v___x_1210_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_head_1201_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1221_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v___x_1219_);
lean_ctor_set(v___x_1205_, 0, v___x_1216_);
v___x_1221_ = v___x_1205_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v_as_x27_1196_ = v_tail_1202_;
v_b_1197_ = v___x_1221_;
goto _start;
}
}
}
else
{
uint8_t v___x_1225_; 
v___x_1225_ = lean_unbox(v_snd_1208_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
lean_dec(v_snd_1208_);
v___x_1226_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4);
v___x_1227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1227_, 0, v_fst_1203_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = lean_box(v___x_1212_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v___x_1228_);
v___x_1230_ = v___x_1210_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_fst_1207_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1232_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v___x_1230_);
lean_ctor_set(v___x_1205_, 0, v___x_1227_);
v___x_1232_ = v___x_1205_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
v_as_x27_1196_ = v_tail_1202_;
v_b_1197_ = v___x_1232_;
goto _start;
}
}
}
else
{
lean_object* v___x_1237_; 
if (v_isShared_1211_ == 0)
{
v___x_1237_ = v___x_1210_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_fst_1207_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_snd_1208_);
v___x_1237_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v___x_1237_);
v___x_1239_ = v___x_1205_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_fst_1203_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
v_as_x27_1196_ = v_tail_1202_;
v_b_1197_ = v___x_1239_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___boxed(lean_object* v_as_x27_1246_, lean_object* v_b_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_1246_, v_b_1247_);
lean_dec(v_as_x27_1246_);
return v_res_1249_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = l_Lean_maxRecDepthErrorMessage;
v___x_1251_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0);
v___x_1253_ = l_Lean_MessageData_ofFormat(v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__2));
v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_inlineStack_1265_; 
v_inlineStack_1265_ = lean_ctor_get(v_a_1257_, 2);
if (lean_obj_tag(v_inlineStack_1265_) == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1);
v___x_1267_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_1266_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
return v___x_1267_;
}
else
{
lean_object* v_head_1268_; lean_object* v_tail_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v_a_1278_; lean_object* v_fst_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1288_; 
v_head_1268_ = lean_ctor_get(v_inlineStack_1265_, 0);
v_tail_1269_ = lean_ctor_get(v_inlineStack_1265_, 1);
v___x_1270_ = 0;
lean_inc_n(v_head_1268_, 2);
v___x_1271_ = l_Lean_MessageData_ofConstName(v_head_1268_, v___x_1270_);
v___x_1272_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_box(v___x_1270_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_head_1268_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1273_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_tail_1269_, v___x_1276_);
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref(v___x_1277_);
v_fst_1279_ = lean_ctor_get(v_a_1278_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_a_1278_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v_a_1278_, 1);
lean_dec(v_unused_1289_);
v___x_1281_ = v_a_1278_;
v_isShared_1282_ = v_isSharedCheck_1288_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_fst_1279_);
lean_dec(v_a_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1288_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1283_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3);
if (v_isShared_1282_ == 0)
{
lean_ctor_set_tag(v___x_1281_, 7);
lean_ctor_set(v___x_1281_, 1, v_fst_1279_);
lean_ctor_set(v___x_1281_, 0, v___x_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_fst_1279_);
v___x_1285_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_1285_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
return v___x_1286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___boxed(lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object* v_00_u03b1_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___boxed(lean_object* v_00_u03b1_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(v_00_u03b1_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(lean_object* v_as_1319_, lean_object* v_as_x27_1320_, lean_object* v_b_1321_, lean_object* v_a_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_1320_, v_b_1321_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___boxed(lean_object* v_as_1332_, lean_object* v_as_x27_1333_, lean_object* v_b_1334_, lean_object* v_a_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(v_as_1332_, v_as_x27_1333_, v_b_1334_, v_a_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v_as_x27_1333_);
lean_dec(v_as_1332_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(lean_object* v_x_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_fileName_1354_; lean_object* v_fileMap_1355_; lean_object* v_options_1356_; lean_object* v_currRecDepth_1357_; lean_object* v_maxRecDepth_1358_; lean_object* v_ref_1359_; lean_object* v_currNamespace_1360_; lean_object* v_openDecls_1361_; lean_object* v_initHeartbeats_1362_; lean_object* v_maxHeartbeats_1363_; lean_object* v_quotContext_1364_; lean_object* v_currMacroScope_1365_; uint8_t v_diag_1366_; lean_object* v_cancelTk_x3f_1367_; uint8_t v_suppressElabErrors_1368_; lean_object* v_inheritedTraceOptions_1369_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v_fileName_1354_ = lean_ctor_get(v_a_1351_, 0);
v_fileMap_1355_ = lean_ctor_get(v_a_1351_, 1);
v_options_1356_ = lean_ctor_get(v_a_1351_, 2);
v_currRecDepth_1357_ = lean_ctor_get(v_a_1351_, 3);
v_maxRecDepth_1358_ = lean_ctor_get(v_a_1351_, 4);
v_ref_1359_ = lean_ctor_get(v_a_1351_, 5);
v_currNamespace_1360_ = lean_ctor_get(v_a_1351_, 6);
v_openDecls_1361_ = lean_ctor_get(v_a_1351_, 7);
v_initHeartbeats_1362_ = lean_ctor_get(v_a_1351_, 8);
v_maxHeartbeats_1363_ = lean_ctor_get(v_a_1351_, 9);
v_quotContext_1364_ = lean_ctor_get(v_a_1351_, 10);
v_currMacroScope_1365_ = lean_ctor_get(v_a_1351_, 11);
v_diag_1366_ = lean_ctor_get_uint8(v_a_1351_, sizeof(void*)*14);
v_cancelTk_x3f_1367_ = lean_ctor_get(v_a_1351_, 12);
v_suppressElabErrors_1368_ = lean_ctor_get_uint8(v_a_1351_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1369_ = lean_ctor_get(v_a_1351_, 13);
v___x_1375_ = lean_unsigned_to_nat(0u);
v___x_1376_ = lean_nat_dec_eq(v_maxRecDepth_1358_, v___x_1375_);
if (v___x_1376_ == 0)
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_nat_dec_eq(v_currRecDepth_1357_, v_maxRecDepth_1358_);
if (v___x_1377_ == 0)
{
goto v___jp_1370_;
}
else
{
lean_object* v___x_1378_; 
lean_dec_ref(v_x_1345_);
v___x_1378_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
return v___x_1378_;
}
}
else
{
goto v___jp_1370_;
}
v___jp_1370_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v_currRecDepth_1357_, v___x_1371_);
lean_inc_ref(v_inheritedTraceOptions_1369_);
lean_inc(v_cancelTk_x3f_1367_);
lean_inc(v_currMacroScope_1365_);
lean_inc(v_quotContext_1364_);
lean_inc(v_maxHeartbeats_1363_);
lean_inc(v_initHeartbeats_1362_);
lean_inc(v_openDecls_1361_);
lean_inc(v_currNamespace_1360_);
lean_inc(v_ref_1359_);
lean_inc(v_maxRecDepth_1358_);
lean_inc_ref(v_options_1356_);
lean_inc_ref(v_fileMap_1355_);
lean_inc_ref(v_fileName_1354_);
v___x_1373_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1373_, 0, v_fileName_1354_);
lean_ctor_set(v___x_1373_, 1, v_fileMap_1355_);
lean_ctor_set(v___x_1373_, 2, v_options_1356_);
lean_ctor_set(v___x_1373_, 3, v___x_1372_);
lean_ctor_set(v___x_1373_, 4, v_maxRecDepth_1358_);
lean_ctor_set(v___x_1373_, 5, v_ref_1359_);
lean_ctor_set(v___x_1373_, 6, v_currNamespace_1360_);
lean_ctor_set(v___x_1373_, 7, v_openDecls_1361_);
lean_ctor_set(v___x_1373_, 8, v_initHeartbeats_1362_);
lean_ctor_set(v___x_1373_, 9, v_maxHeartbeats_1363_);
lean_ctor_set(v___x_1373_, 10, v_quotContext_1364_);
lean_ctor_set(v___x_1373_, 11, v_currMacroScope_1365_);
lean_ctor_set(v___x_1373_, 12, v_cancelTk_x3f_1367_);
lean_ctor_set(v___x_1373_, 13, v_inheritedTraceOptions_1369_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*14, v_diag_1366_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*14 + 1, v_suppressElabErrors_1368_);
lean_inc(v_a_1352_);
lean_inc(v_a_1350_);
lean_inc_ref(v_a_1349_);
lean_inc_ref(v_a_1348_);
lean_inc(v_a_1347_);
lean_inc_ref(v_a_1346_);
v___x_1374_ = lean_apply_8(v_x_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v___x_1373_, v_a_1352_, lean_box(0));
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg___boxed(lean_object* v_x_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(v_x_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth(lean_object* v_00_u03b1_1389_, lean_object* v_x_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_fileName_1399_; lean_object* v_fileMap_1400_; lean_object* v_options_1401_; lean_object* v_currRecDepth_1402_; lean_object* v_maxRecDepth_1403_; lean_object* v_ref_1404_; lean_object* v_currNamespace_1405_; lean_object* v_openDecls_1406_; lean_object* v_initHeartbeats_1407_; lean_object* v_maxHeartbeats_1408_; lean_object* v_quotContext_1409_; lean_object* v_currMacroScope_1410_; uint8_t v_diag_1411_; lean_object* v_cancelTk_x3f_1412_; uint8_t v_suppressElabErrors_1413_; lean_object* v_inheritedTraceOptions_1414_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v_fileName_1399_ = lean_ctor_get(v_a_1396_, 0);
v_fileMap_1400_ = lean_ctor_get(v_a_1396_, 1);
v_options_1401_ = lean_ctor_get(v_a_1396_, 2);
v_currRecDepth_1402_ = lean_ctor_get(v_a_1396_, 3);
v_maxRecDepth_1403_ = lean_ctor_get(v_a_1396_, 4);
v_ref_1404_ = lean_ctor_get(v_a_1396_, 5);
v_currNamespace_1405_ = lean_ctor_get(v_a_1396_, 6);
v_openDecls_1406_ = lean_ctor_get(v_a_1396_, 7);
v_initHeartbeats_1407_ = lean_ctor_get(v_a_1396_, 8);
v_maxHeartbeats_1408_ = lean_ctor_get(v_a_1396_, 9);
v_quotContext_1409_ = lean_ctor_get(v_a_1396_, 10);
v_currMacroScope_1410_ = lean_ctor_get(v_a_1396_, 11);
v_diag_1411_ = lean_ctor_get_uint8(v_a_1396_, sizeof(void*)*14);
v_cancelTk_x3f_1412_ = lean_ctor_get(v_a_1396_, 12);
v_suppressElabErrors_1413_ = lean_ctor_get_uint8(v_a_1396_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1414_ = lean_ctor_get(v_a_1396_, 13);
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = lean_nat_dec_eq(v_maxRecDepth_1403_, v___x_1420_);
if (v___x_1421_ == 0)
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_nat_dec_eq(v_currRecDepth_1402_, v_maxRecDepth_1403_);
if (v___x_1422_ == 0)
{
goto v___jp_1415_;
}
else
{
lean_object* v___x_1423_; 
lean_dec_ref(v_x_1390_);
v___x_1423_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
return v___x_1423_;
}
}
else
{
goto v___jp_1415_;
}
v___jp_1415_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1416_ = lean_unsigned_to_nat(1u);
v___x_1417_ = lean_nat_add(v_currRecDepth_1402_, v___x_1416_);
lean_inc_ref(v_inheritedTraceOptions_1414_);
lean_inc(v_cancelTk_x3f_1412_);
lean_inc(v_currMacroScope_1410_);
lean_inc(v_quotContext_1409_);
lean_inc(v_maxHeartbeats_1408_);
lean_inc(v_initHeartbeats_1407_);
lean_inc(v_openDecls_1406_);
lean_inc(v_currNamespace_1405_);
lean_inc(v_ref_1404_);
lean_inc(v_maxRecDepth_1403_);
lean_inc_ref(v_options_1401_);
lean_inc_ref(v_fileMap_1400_);
lean_inc_ref(v_fileName_1399_);
v___x_1418_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1418_, 0, v_fileName_1399_);
lean_ctor_set(v___x_1418_, 1, v_fileMap_1400_);
lean_ctor_set(v___x_1418_, 2, v_options_1401_);
lean_ctor_set(v___x_1418_, 3, v___x_1417_);
lean_ctor_set(v___x_1418_, 4, v_maxRecDepth_1403_);
lean_ctor_set(v___x_1418_, 5, v_ref_1404_);
lean_ctor_set(v___x_1418_, 6, v_currNamespace_1405_);
lean_ctor_set(v___x_1418_, 7, v_openDecls_1406_);
lean_ctor_set(v___x_1418_, 8, v_initHeartbeats_1407_);
lean_ctor_set(v___x_1418_, 9, v_maxHeartbeats_1408_);
lean_ctor_set(v___x_1418_, 10, v_quotContext_1409_);
lean_ctor_set(v___x_1418_, 11, v_currMacroScope_1410_);
lean_ctor_set(v___x_1418_, 12, v_cancelTk_x3f_1412_);
lean_ctor_set(v___x_1418_, 13, v_inheritedTraceOptions_1414_);
lean_ctor_set_uint8(v___x_1418_, sizeof(void*)*14, v_diag_1411_);
lean_ctor_set_uint8(v___x_1418_, sizeof(void*)*14 + 1, v_suppressElabErrors_1413_);
lean_inc(v_a_1397_);
lean_inc(v_a_1395_);
lean_inc_ref(v_a_1394_);
lean_inc_ref(v_a_1393_);
lean_inc(v_a_1392_);
lean_inc_ref(v_a_1391_);
v___x_1419_ = lean_apply_8(v_x_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v___x_1418_, v_a_1397_, lean_box(0));
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___boxed(lean_object* v_00_u03b1_1424_, lean_object* v_x_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth(v_00_u03b1_1424_, v_x_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec_ref(v_a_1428_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(lean_object* v_a_1435_, lean_object* v_fvarId_1436_, lean_object* v___x_1437_, lean_object* v_a_x3f_1438_){
_start:
{
lean_object* v___x_1440_; lean_object* v_subst_1441_; lean_object* v_used_1442_; lean_object* v_binderRenaming_1443_; lean_object* v_funDeclInfoMap_1444_; uint8_t v_simplified_1445_; lean_object* v_visited_1446_; lean_object* v_inline_1447_; lean_object* v_inlineLocal_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1459_; 
v___x_1440_ = lean_st_ref_take(v_a_1435_);
v_subst_1441_ = lean_ctor_get(v___x_1440_, 0);
v_used_1442_ = lean_ctor_get(v___x_1440_, 1);
v_binderRenaming_1443_ = lean_ctor_get(v___x_1440_, 2);
v_funDeclInfoMap_1444_ = lean_ctor_get(v___x_1440_, 3);
v_simplified_1445_ = lean_ctor_get_uint8(v___x_1440_, sizeof(void*)*7);
v_visited_1446_ = lean_ctor_get(v___x_1440_, 4);
v_inline_1447_ = lean_ctor_get(v___x_1440_, 5);
v_inlineLocal_1448_ = lean_ctor_get(v___x_1440_, 6);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1450_ = v___x_1440_;
v_isShared_1451_ = v_isSharedCheck_1459_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_inlineLocal_1448_);
lean_inc(v_inline_1447_);
lean_inc(v_visited_1446_);
lean_inc(v_funDeclInfoMap_1444_);
lean_inc(v_binderRenaming_1443_);
lean_inc(v_used_1442_);
lean_inc(v_subst_1441_);
lean_dec(v___x_1440_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1459_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1452_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(v_funDeclInfoMap_1444_, v_fvarId_1436_, v___x_1437_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 3, v___x_1452_);
v___x_1454_ = v___x_1450_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_subst_1441_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_used_1442_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_binderRenaming_1443_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v_visited_1446_);
lean_ctor_set(v_reuseFailAlloc_1458_, 5, v_inline_1447_);
lean_ctor_set(v_reuseFailAlloc_1458_, 6, v_inlineLocal_1448_);
lean_ctor_set_uint8(v_reuseFailAlloc_1458_, sizeof(void*)*7, v_simplified_1445_);
v___x_1454_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = lean_st_ref_put(v_a_1435_, v___x_1454_);
v___x_1456_ = lean_box(0);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0___boxed(lean_object* v_a_1460_, lean_object* v_fvarId_1461_, lean_object* v___x_1462_, lean_object* v_a_x3f_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1460_, v_fvarId_1461_, v___x_1462_, v_a_x3f_1463_);
lean_dec(v_a_x3f_1463_);
lean_dec(v_a_1460_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_m_1466_, lean_object* v_query_1467_, lean_object* v_x_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_){
_start:
{
lean_object* v_zero_1471_; uint8_t v_isZero_1472_; 
v_zero_1471_ = lean_unsigned_to_nat(0u);
v_isZero_1472_ = lean_nat_dec_eq(v_x_1469_, v_zero_1471_);
if (v_isZero_1472_ == 1)
{
lean_dec(v_x_1470_);
lean_dec(v_x_1469_);
if (lean_obj_tag(v_x_1468_) == 0)
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_box(2);
return v___x_1473_;
}
else
{
lean_object* v_val_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_val_1474_ = lean_ctor_get(v_x_1468_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_x_1468_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v_x_1468_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_val_1474_);
lean_dec(v_x_1468_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_val_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_object* v_keyArray_1482_; lean_object* v_valueArray_1483_; lean_object* v___x_1484_; uint8_t v_isSome_1485_; 
v_keyArray_1482_ = lean_ctor_get(v_m_1466_, 1);
v_valueArray_1483_ = lean_ctor_get(v_m_1466_, 2);
v___x_1484_ = lean_array_fget_borrowed(v_keyArray_1482_, v_x_1470_);
v_isSome_1485_ = lean_noption_is_some(v___x_1484_);
if (v_isSome_1485_ == 0)
{
lean_dec(v_x_1469_);
if (lean_obj_tag(v_x_1468_) == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_x_1470_);
return v___x_1486_;
}
else
{
lean_object* v_val_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_x_1470_);
v_val_1487_ = lean_ctor_get(v_x_1468_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_x_1468_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v_x_1468_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_val_1487_);
lean_dec(v_x_1468_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_val_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
else
{
lean_object* v_one_1495_; lean_object* v_n_1496_; lean_object* v___y_1498_; 
v_one_1495_ = lean_unsigned_to_nat(1u);
v_n_1496_ = lean_nat_sub(v_x_1469_, v_one_1495_);
lean_dec(v_x_1469_);
if (v_isSome_1485_ == 0)
{
goto v___jp_1504_;
}
else
{
lean_object* v___x_1506_; uint8_t v_isSome_1507_; 
v___x_1506_ = lean_array_fget_borrowed(v_valueArray_1483_, v_x_1470_);
v_isSome_1507_ = lean_noption_is_some(v___x_1506_);
if (v_isSome_1507_ == 0)
{
goto v___jp_1504_;
}
else
{
lean_object* v_val_1508_; uint8_t v___x_1509_; 
lean_inc(v___x_1484_);
v_val_1508_ = lean_noption_get(v___x_1484_);
v___x_1509_ = l_Lean_instBEqFVarId_beq(v_val_1508_, v_query_1467_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
lean_dec(v_val_1508_);
v___x_1510_ = lean_array_get_size(v_keyArray_1482_);
v___x_1511_ = lean_nat_add(v_x_1470_, v_one_1495_);
lean_dec(v_x_1470_);
v___x_1512_ = lean_nat_dec_lt(v___x_1511_, v___x_1510_);
if (v___x_1512_ == 0)
{
lean_dec(v___x_1511_);
v_x_1469_ = v_n_1496_;
v_x_1470_ = v_zero_1471_;
goto _start;
}
else
{
v_x_1469_ = v_n_1496_;
v_x_1470_ = v___x_1511_;
goto _start;
}
}
else
{
lean_object* v_val_1515_; lean_object* v___x_1516_; 
lean_dec(v_n_1496_);
lean_dec(v_x_1468_);
lean_inc(v___x_1506_);
v_val_1515_ = lean_noption_get(v___x_1506_);
v___x_1516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1516_, 0, v_x_1470_);
lean_ctor_set(v___x_1516_, 1, v_val_1508_);
lean_ctor_set(v___x_1516_, 2, v_val_1515_);
return v___x_1516_;
}
}
}
v___jp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1499_ = lean_array_get_size(v_keyArray_1482_);
v___x_1500_ = lean_nat_add(v_x_1470_, v_one_1495_);
lean_dec(v_x_1470_);
v___x_1501_ = lean_nat_dec_lt(v___x_1500_, v___x_1499_);
if (v___x_1501_ == 0)
{
lean_dec(v___x_1500_);
v_x_1468_ = v___y_1498_;
v_x_1469_ = v_n_1496_;
v_x_1470_ = v_zero_1471_;
goto _start;
}
else
{
v_x_1468_ = v___y_1498_;
v_x_1469_ = v_n_1496_;
v_x_1470_ = v___x_1500_;
goto _start;
}
}
v___jp_1504_:
{
if (lean_obj_tag(v_x_1468_) == 0)
{
lean_object* v___x_1505_; 
lean_inc(v_x_1470_);
v___x_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_x_1470_);
v___y_1498_ = v___x_1505_;
goto v___jp_1497_;
}
else
{
v___y_1498_ = v_x_1468_;
goto v___jp_1497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_m_1517_, lean_object* v_query_1518_, lean_object* v_x_1519_, lean_object* v_x_1520_, lean_object* v_x_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1_spec__2___redArg(v_m_1517_, v_query_1518_, v_x_1519_, v_x_1520_, v_x_1521_);
lean_dec(v_query_1518_);
lean_dec_ref(v_m_1517_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg(lean_object* v_m_1523_, lean_object* v_query_1524_){
_start:
{
lean_object* v_keyArray_1525_; lean_object* v___x_1526_; uint64_t v___x_1527_; uint64_t v___x_1528_; uint64_t v___x_1529_; uint64_t v_fold_1530_; uint64_t v___x_1531_; uint64_t v___x_1532_; uint64_t v___x_1533_; size_t v___x_1534_; size_t v___x_1535_; size_t v___x_1536_; size_t v___x_1537_; size_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_keyArray_1525_ = lean_ctor_get(v_m_1523_, 1);
v___x_1526_ = lean_array_get_size(v_keyArray_1525_);
v___x_1527_ = l_Lean_instHashableFVarId_hash(v_query_1524_);
v___x_1528_ = 32ULL;
v___x_1529_ = lean_uint64_shift_right(v___x_1527_, v___x_1528_);
v_fold_1530_ = lean_uint64_xor(v___x_1527_, v___x_1529_);
v___x_1531_ = 16ULL;
v___x_1532_ = lean_uint64_shift_right(v_fold_1530_, v___x_1531_);
v___x_1533_ = lean_uint64_xor(v_fold_1530_, v___x_1532_);
v___x_1534_ = lean_uint64_to_usize(v___x_1533_);
v___x_1535_ = lean_usize_of_nat(v___x_1526_);
v___x_1536_ = ((size_t)1ULL);
v___x_1537_ = lean_usize_sub(v___x_1535_, v___x_1536_);
v___x_1538_ = lean_usize_land(v___x_1534_, v___x_1537_);
v___x_1539_ = lean_usize_to_nat(v___x_1538_);
v___x_1540_ = lean_box(0);
v___x_1541_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1_spec__2___redArg(v_m_1523_, v_query_1524_, v___x_1540_, v___x_1526_, v___x_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_1542_, lean_object* v_query_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg(v_m_1542_, v_query_1543_);
lean_dec(v_query_1543_);
lean_dec_ref(v_m_1542_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(lean_object* v_m_1545_, lean_object* v_query_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg(v_m_1545_, v_query_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_index_1548_; lean_object* v_key_1549_; lean_object* v_value_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_index_1548_ = lean_ctor_get(v___x_1547_, 0);
v_key_1549_ = lean_ctor_get(v___x_1547_, 1);
v_value_1550_ = lean_ctor_get(v___x_1547_, 2);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1547_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_value_1550_);
lean_inc(v_key_1549_);
lean_inc(v_index_1548_);
lean_dec(v___x_1547_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_index_1548_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_key_1549_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_value_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
else
{
lean_object* v___x_1558_; 
lean_dec(v___x_1547_);
v___x_1558_ = lean_box(1);
return v___x_1558_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg___boxed(lean_object* v_m_1559_, lean_object* v_query_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_m_1559_, v_query_1560_);
lean_dec(v_query_1560_);
lean_dec_ref(v_m_1559_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(lean_object* v_m_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_m_1562_, v_a_1563_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_value_1565_; lean_object* v___x_1566_; 
v_value_1565_ = lean_ctor_get(v___x_1564_, 2);
lean_inc(v_value_1565_);
lean_dec_ref_known(v___x_1564_, 3);
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_value_1565_);
return v___x_1566_;
}
else
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_box(0);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg___boxed(lean_object* v_m_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec_ref(v_m_1568_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(lean_object* v_fvarId_1571_, lean_object* v_x_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v_funDeclInfoMap_1582_; lean_object* v___x_1583_; lean_object* v_a_1585_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1581_ = lean_st_ref_get(v_a_1574_);
v_funDeclInfoMap_1582_ = lean_ctor_get(v___x_1581_, 3);
lean_inc_ref(v_funDeclInfoMap_1582_);
lean_dec(v___x_1581_);
v___x_1583_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_1582_, v_fvarId_1571_);
lean_dec_ref(v_funDeclInfoMap_1582_);
lean_inc(v_fvarId_1571_);
v___x_1596_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_1571_, v_a_1574_);
lean_dec_ref(v___x_1596_);
lean_inc(v_a_1579_);
lean_inc_ref(v_a_1578_);
lean_inc(v_a_1577_);
lean_inc_ref(v_a_1576_);
lean_inc_ref(v_a_1575_);
lean_inc(v_a_1574_);
lean_inc_ref(v_a_1573_);
v___x_1597_ = lean_apply_8(v_x_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, lean_box(0));
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1614_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1614_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1614_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
lean_inc(v_a_1598_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 1);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v___x_1604_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1574_, v_fvarId_1571_, v___x_1583_, v___x_1603_);
lean_dec_ref(v___x_1603_);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v___x_1604_, 0);
lean_dec(v_unused_1612_);
v___x_1606_ = v___x_1604_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_dec(v___x_1604_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v_a_1598_);
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1598_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
else
{
lean_object* v_a_1615_; 
v_a_1615_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1597_, 1);
v_a_1585_ = v_a_1615_;
goto v___jp_1584_;
}
v___jp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
v___x_1586_ = lean_box(0);
v___x_1587_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1574_, v_fvarId_1571_, v___x_1583_, v___x_1586_);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; 
v_unused_1595_ = lean_ctor_get(v___x_1587_, 0);
lean_dec(v_unused_1595_);
v___x_1589_ = v___x_1587_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_dec(v___x_1587_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 1);
lean_ctor_set(v___x_1589_, 0, v_a_1585_);
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1585_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___boxed(lean_object* v_fvarId_1616_, lean_object* v_x_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1616_, v_x_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object* v_00_u03b1_1627_, lean_object* v_fvarId_1628_, lean_object* v_x_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1628_, v_x_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___boxed(lean_object* v_00_u03b1_1639_, lean_object* v_fvarId_1640_, lean_object* v_x_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline(v_00_u03b1_1639_, v_fvarId_1640_, v_x_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(lean_object* v_00_u03b2_1651_, lean_object* v_m_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_1652_, v_a_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___boxed(lean_object* v_00_u03b2_1655_, lean_object* v_m_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(v_00_u03b2_1655_, v_m_1656_, v_a_1657_);
lean_dec(v_a_1657_);
lean_dec_ref(v_m_1656_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(lean_object* v_00_u03b2_1659_, lean_object* v_m_1660_, lean_object* v_query_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_m_1660_, v_query_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1663_, lean_object* v_m_1664_, lean_object* v_query_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(v_00_u03b2_1663_, v_m_1664_, v_query_1665_);
lean_dec(v_query_1665_);
lean_dec_ref(v_m_1664_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1667_, lean_object* v_m_1668_, lean_object* v_query_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg(v_m_1668_, v_query_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1671_, lean_object* v_m_1672_, lean_object* v_query_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1(v_00_u03b2_1671_, v_m_1672_, v_query_1673_);
lean_dec(v_query_1673_);
lean_dec_ref(v_m_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1675_, lean_object* v_m_1676_, lean_object* v_query_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1_spec__2___redArg(v_m_1676_, v_query_1677_, v_x_1678_, v_x_1679_, v_x_1680_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1683_, lean_object* v_m_1684_, lean_object* v_query_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1683_, v_m_1684_, v_query_1685_, v_x_1686_, v_x_1687_, v_x_1688_, v_x_1689_);
lean_dec(v_query_1685_);
lean_dec_ref(v_m_1684_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object* v_fvarId_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v___x_1702_; lean_object* v_funDeclInfoMap_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_st_ref_get(v_a_1692_);
v_funDeclInfoMap_1703_ = lean_ctor_get(v___x_1702_, 3);
lean_inc_ref(v_funDeclInfoMap_1703_);
lean_dec(v___x_1702_);
v___x_1704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_1703_, v_fvarId_1691_);
lean_dec_ref(v_funDeclInfoMap_1703_);
if (lean_obj_tag(v___x_1704_) == 1)
{
lean_object* v_val_1705_; uint8_t v___x_1706_; 
v_val_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_val_1705_);
lean_dec_ref_known(v___x_1704_, 1);
v___x_1706_ = lean_unbox(v_val_1705_);
lean_dec(v_val_1705_);
switch(v___x_1706_)
{
case 0:
{
goto v___jp_1698_;
}
case 2:
{
goto v___jp_1698_;
}
default: 
{
goto v___jp_1694_;
}
}
}
else
{
lean_dec(v___x_1704_);
goto v___jp_1694_;
}
v___jp_1694_:
{
uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = 0;
v___x_1696_ = lean_box(v___x_1695_);
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
return v___x_1697_;
}
v___jp_1698_:
{
uint8_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = 1;
v___x_1700_ = lean_box(v___x_1699_);
v___x_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
return v___x_1701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg___boxed(lean_object* v_fvarId_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1707_, v_a_1708_);
lean_dec(v_a_1708_);
lean_dec(v_fvarId_1707_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object* v_fvarId_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1711_, v_a_1713_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object* v_fvarId_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(v_fvarId_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_fvarId_1721_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg(lean_object* v_code_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_1732_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1746_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1746_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1746_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v_smallThreshold_1739_; uint8_t v___x_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v_smallThreshold_1739_ = lean_ctor_get(v_a_1735_, 0);
lean_inc(v_smallThreshold_1739_);
lean_dec(v_a_1735_);
v___x_1740_ = 0;
v___x_1741_ = l_Lean_Compiler_LCNF_Code_sizeLe(v___x_1740_, v_code_1731_, v_smallThreshold_1739_);
lean_dec(v_smallThreshold_1739_);
v___x_1742_ = lean_box(v___x_1741_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1742_);
v___x_1744_ = v___x_1737_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_a_1747_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1734_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1734_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg___boxed(lean_object* v_code_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1755_, v_a_1756_);
lean_dec_ref(v_a_1756_);
lean_dec_ref(v_code_1755_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object* v_code_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1759_, v_a_1763_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object* v_code_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Compiler_LCNF_Simp_isSmall(v_code_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
lean_dec_ref(v_code_1769_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object* v_decl_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v_fvarId_1783_; lean_object* v_value_1784_; lean_object* v___x_1785_; lean_object* v_a_1786_; uint8_t v___x_1787_; 
v_fvarId_1783_ = lean_ctor_get(v_decl_1779_, 0);
v_value_1784_ = lean_ctor_get(v_decl_1779_, 4);
v___x_1785_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1783_, v_a_1780_);
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
v___x_1787_ = lean_unbox(v_a_1786_);
lean_dec(v_a_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; 
lean_dec_ref(v___x_1785_);
v___x_1788_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_value_1784_, v_a_1781_);
return v___x_1788_;
}
else
{
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg___boxed(lean_object* v_decl_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1789_, v_a_1790_, v_a_1791_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec_ref(v_decl_1789_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object* v_decl_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1794_, v_a_1796_, v_a_1798_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object* v_decl_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(v_decl_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec_ref(v_decl_1804_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_spec__1___redArg(lean_object* v_b_1814_, lean_object* v_acc_1815_, lean_object* v_i_1816_){
_start:
{
lean_object* v___y_1818_; lean_object* v_keyArray_1826_; lean_object* v_valueArray_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v_keyArray_1826_ = lean_ctor_get(v_b_1814_, 1);
v_valueArray_1827_ = lean_ctor_get(v_b_1814_, 2);
v___x_1828_ = lean_array_get_size(v_keyArray_1826_);
v___x_1829_ = lean_nat_dec_lt(v_i_1816_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_dec(v_i_1816_);
return v_acc_1815_;
}
else
{
lean_object* v___x_1830_; uint8_t v_isSome_1831_; 
v___x_1830_ = lean_array_fget_borrowed(v_keyArray_1826_, v_i_1816_);
v_isSome_1831_ = lean_noption_is_some(v___x_1830_);
if (v_isSome_1831_ == 0)
{
goto v___jp_1822_;
}
else
{
lean_object* v___x_1832_; uint8_t v_isSome_1833_; 
v___x_1832_ = lean_array_fget_borrowed(v_valueArray_1827_, v_i_1816_);
v_isSome_1833_ = lean_noption_is_some(v___x_1832_);
if (v_isSome_1833_ == 0)
{
goto v___jp_1822_;
}
else
{
lean_object* v_val_1834_; lean_object* v_val_1835_; lean_object* v_i_1837_; lean_object* v___x_1842_; 
lean_inc(v___x_1830_);
v_val_1834_ = lean_noption_get(v___x_1830_);
lean_inc(v___x_1832_);
v_val_1835_ = lean_noption_get(v___x_1832_);
v___x_1842_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg(v_acc_1815_, v_val_1834_);
switch(lean_obj_tag(v___x_1842_))
{
case 0:
{
lean_object* v_index_1843_; lean_object* v_size_1844_; lean_object* v___x_1845_; 
v_index_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_index_1843_);
lean_dec_ref_known(v___x_1842_, 3);
v_size_1844_ = lean_ctor_get(v_acc_1815_, 0);
lean_inc(v_size_1844_);
v___x_1845_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1815_, v_size_1844_, v_index_1843_, v_val_1834_, v_val_1835_);
lean_dec(v_index_1843_);
v___y_1818_ = v___x_1845_;
goto v___jp_1817_;
}
case 1:
{
lean_object* v_index_1846_; 
v_index_1846_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_index_1846_);
lean_dec_ref_known(v___x_1842_, 1);
v_i_1837_ = v_index_1846_;
goto v___jp_1836_;
}
default: 
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1815_, v___x_1847_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_index_1849_; 
v_index_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_index_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v_i_1837_ = v_index_1849_;
goto v___jp_1836_;
}
else
{
lean_dec(v_val_1835_);
lean_dec(v_val_1834_);
v___y_1818_ = v_acc_1815_;
goto v___jp_1817_;
}
}
}
v___jp_1836_:
{
lean_object* v_size_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v_size_1838_ = lean_ctor_get(v_acc_1815_, 0);
v___x_1839_ = lean_unsigned_to_nat(1u);
v___x_1840_ = lean_nat_add(v_size_1838_, v___x_1839_);
v___x_1841_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1815_, v___x_1840_, v_i_1837_, v_val_1834_, v_val_1835_);
lean_dec(v_i_1837_);
v___y_1818_ = v___x_1841_;
goto v___jp_1817_;
}
}
}
}
v___jp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_unsigned_to_nat(1u);
v___x_1820_ = lean_nat_add(v_i_1816_, v___x_1819_);
lean_dec(v_i_1816_);
v_acc_1815_ = v___y_1818_;
v_i_1816_ = v___x_1820_;
goto _start;
}
v___jp_1822_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = lean_unsigned_to_nat(1u);
v___x_1824_ = lean_nat_add(v_i_1816_, v___x_1823_);
lean_dec(v_i_1816_);
v_i_1816_ = v___x_1824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_b_1850_, lean_object* v_acc_1851_, lean_object* v_i_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_spec__1___redArg(v_b_1850_, v_acc_1851_, v_i_1852_);
lean_dec_ref(v_b_1850_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(lean_object* v_init_1854_, lean_object* v_b_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_spec__1___redArg(v_b_1855_, v_init_1854_, v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg___boxed(lean_object* v_init_1858_, lean_object* v_b_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_init_1858_, v_b_1859_);
lean_dec_ref(v_b_1859_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(lean_object* v_m_1861_){
_start:
{
lean_object* v_keyArray_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v_cellCount_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v_target_1869_; lean_object* v___x_1870_; 
v_keyArray_1862_ = lean_ctor_get(v_m_1861_, 1);
v___x_1863_ = lean_array_get_size(v_keyArray_1862_);
v___x_1864_ = lean_unsigned_to_nat(2u);
v_cellCount_1865_ = lean_nat_mul(v___x_1863_, v___x_1864_);
v___x_1866_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1865_);
v___x_1867_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1865_);
v___x_1868_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1865_);
v_target_1869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1869_, 0, v___x_1866_);
lean_ctor_set(v_target_1869_, 1, v___x_1867_);
lean_ctor_set(v_target_1869_, 2, v___x_1868_);
v___x_1870_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_target_1869_, v_m_1861_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg___boxed(lean_object* v_m_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_m_1871_);
lean_dec_ref(v_m_1871_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(lean_object* v_as_1873_, size_t v_sz_1874_, size_t v_i_1875_, lean_object* v_b_1876_){
_start:
{
uint8_t v___x_1878_; 
v___x_1878_ = lean_usize_dec_lt(v_i_1875_, v_sz_1874_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_b_1876_);
return v___x_1879_;
}
else
{
lean_object* v_snd_1880_; lean_object* v_fst_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1976_; 
v_snd_1880_ = lean_ctor_get(v_b_1876_, 1);
v_fst_1881_ = lean_ctor_get(v_b_1876_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_b_1876_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1883_ = v_b_1876_;
v_isShared_1884_ = v_isSharedCheck_1976_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_snd_1880_);
lean_inc(v_fst_1881_);
lean_dec(v_b_1876_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1976_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v_array_1885_; lean_object* v_start_1886_; lean_object* v_stop_1887_; uint8_t v___x_1888_; 
v_array_1885_ = lean_ctor_get(v_snd_1880_, 0);
v_start_1886_ = lean_ctor_get(v_snd_1880_, 1);
v_stop_1887_ = lean_ctor_get(v_snd_1880_, 2);
v___x_1888_ = lean_nat_dec_lt(v_start_1886_, v_stop_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1890_; 
if (v_isShared_1884_ == 0)
{
v___x_1890_ = v___x_1883_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_fst_1881_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_snd_1880_);
v___x_1890_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
else
{
lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1972_; 
lean_inc(v_stop_1887_);
lean_inc(v_start_1886_);
lean_inc_ref(v_array_1885_);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_snd_1880_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; lean_object* v_unused_1974_; lean_object* v_unused_1975_; 
v_unused_1973_ = lean_ctor_get(v_snd_1880_, 2);
lean_dec(v_unused_1973_);
v_unused_1974_ = lean_ctor_get(v_snd_1880_, 1);
lean_dec(v_unused_1974_);
v_unused_1975_ = lean_ctor_get(v_snd_1880_, 0);
lean_dec(v_unused_1975_);
v___x_1894_ = v_snd_1880_;
v_isShared_1895_ = v_isSharedCheck_1972_;
goto v_resetjp_1893_;
}
else
{
lean_dec(v_snd_1880_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1972_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v_a_1896_; lean_object* v_fvarId_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1902_; 
v_a_1896_ = lean_array_uget_borrowed(v_as_1873_, v_i_1875_);
v_fvarId_1897_ = lean_ctor_get(v_a_1896_, 0);
v___x_1898_ = lean_array_fget(v_array_1885_, v_start_1886_);
v___x_1899_ = lean_unsigned_to_nat(1u);
v___x_1900_ = lean_nat_add(v_start_1886_, v___x_1899_);
lean_dec(v_start_1886_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v___x_1900_);
v___x_1902_ = v___x_1894_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_array_1885_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_stop_1887_);
v___x_1902_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
lean_object* v___y_1904_; lean_object* v___y_1912_; lean_object* v_i_1913_; lean_object* v___y_1928_; lean_object* v_i_1929_; lean_object* v___y_1934_; lean_object* v___x_1943_; 
v___x_1943_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg(v_fst_1881_, v_fvarId_1897_);
switch(lean_obj_tag(v___x_1943_))
{
case 0:
{
lean_object* v_index_1944_; lean_object* v_size_1945_; lean_object* v___x_1946_; 
v_index_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_index_1944_);
lean_dec_ref_known(v___x_1943_, 3);
v_size_1945_ = lean_ctor_get(v_fst_1881_, 0);
lean_inc(v_size_1945_);
lean_inc(v_fvarId_1897_);
v___x_1946_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1881_, v_size_1945_, v_index_1944_, v_fvarId_1897_, v___x_1898_);
lean_dec(v_index_1944_);
v___y_1904_ = v___x_1946_;
goto v___jp_1903_;
}
case 1:
{
lean_object* v_index_1947_; lean_object* v_size_1948_; lean_object* v_keyArray_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v_index_1947_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_index_1947_);
lean_dec_ref_known(v___x_1943_, 1);
v_size_1948_ = lean_ctor_get(v_fst_1881_, 0);
v_keyArray_1949_ = lean_ctor_get(v_fst_1881_, 1);
v___x_1950_ = lean_nat_add(v_size_1948_, v___x_1899_);
v___x_1951_ = lean_array_get_size(v_keyArray_1949_);
v___x_1952_ = lean_nat_dec_lt(v___x_1950_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_dec(v___x_1950_);
lean_dec(v_index_1947_);
goto v___jp_1917_;
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1953_ = lean_unsigned_to_nat(4u);
v___x_1954_ = lean_nat_mul(v___x_1950_, v___x_1953_);
v___x_1955_ = lean_unsigned_to_nat(3u);
v___x_1956_ = lean_nat_mul(v___x_1951_, v___x_1955_);
v___x_1957_ = lean_nat_dec_le(v___x_1954_, v___x_1956_);
lean_dec(v___x_1956_);
lean_dec(v___x_1954_);
if (v___x_1957_ == 0)
{
lean_dec(v___x_1950_);
lean_dec(v_index_1947_);
goto v___jp_1917_;
}
else
{
lean_object* v___x_1958_; 
lean_inc(v_fvarId_1897_);
v___x_1958_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1881_, v___x_1950_, v_index_1947_, v_fvarId_1897_, v___x_1898_);
lean_dec(v_index_1947_);
v___y_1904_ = v___x_1958_;
goto v___jp_1903_;
}
}
}
default: 
{
lean_object* v_size_1959_; lean_object* v_keyArray_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v_size_1959_ = lean_ctor_get(v_fst_1881_, 0);
v_keyArray_1960_ = lean_ctor_get(v_fst_1881_, 1);
v___x_1961_ = lean_nat_add(v_size_1959_, v___x_1899_);
v___x_1962_ = lean_array_get_size(v_keyArray_1960_);
v___x_1963_ = lean_nat_dec_lt(v___x_1961_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; 
lean_dec(v___x_1961_);
v___x_1964_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_fst_1881_);
lean_dec(v_fst_1881_);
v___y_1934_ = v___x_1964_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1965_ = lean_unsigned_to_nat(4u);
v___x_1966_ = lean_nat_mul(v___x_1961_, v___x_1965_);
lean_dec(v___x_1961_);
v___x_1967_ = lean_unsigned_to_nat(3u);
v___x_1968_ = lean_nat_mul(v___x_1962_, v___x_1967_);
v___x_1969_ = lean_nat_dec_le(v___x_1966_, v___x_1968_);
lean_dec(v___x_1968_);
lean_dec(v___x_1966_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
v___x_1970_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_fst_1881_);
lean_dec(v_fst_1881_);
v___y_1934_ = v___x_1970_;
goto v___jp_1933_;
}
else
{
v___y_1934_ = v_fst_1881_;
goto v___jp_1933_;
}
}
}
}
v___jp_1903_:
{
lean_object* v___x_1906_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 1, v___x_1902_);
lean_ctor_set(v___x_1883_, 0, v___y_1904_);
v___x_1906_ = v___x_1883_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___y_1904_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v___x_1902_);
v___x_1906_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
size_t v___x_1907_; size_t v___x_1908_; 
v___x_1907_ = ((size_t)1ULL);
v___x_1908_ = lean_usize_add(v_i_1875_, v___x_1907_);
v_i_1875_ = v___x_1908_;
v_b_1876_ = v___x_1906_;
goto _start;
}
}
v___jp_1911_:
{
lean_object* v_size_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_size_1914_ = lean_ctor_get(v___y_1912_, 0);
v___x_1915_ = lean_nat_add(v_size_1914_, v___x_1899_);
lean_inc(v_fvarId_1897_);
v___x_1916_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1912_, v___x_1915_, v_i_1913_, v_fvarId_1897_, v___x_1898_);
lean_dec(v_i_1913_);
v___y_1904_ = v___x_1916_;
goto v___jp_1903_;
}
v___jp_1917_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_fst_1881_);
lean_dec(v_fst_1881_);
v___x_1919_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg(v___x_1918_, v_fvarId_1897_);
switch(lean_obj_tag(v___x_1919_))
{
case 0:
{
lean_object* v_index_1920_; lean_object* v_size_1921_; lean_object* v___x_1922_; 
v_index_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_index_1920_);
lean_dec_ref_known(v___x_1919_, 3);
v_size_1921_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_size_1921_);
lean_inc(v_fvarId_1897_);
v___x_1922_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1918_, v_size_1921_, v_index_1920_, v_fvarId_1897_, v___x_1898_);
lean_dec(v_index_1920_);
v___y_1904_ = v___x_1922_;
goto v___jp_1903_;
}
case 1:
{
lean_object* v_index_1923_; 
v_index_1923_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_index_1923_);
lean_dec_ref_known(v___x_1919_, 1);
v___y_1912_ = v___x_1918_;
v_i_1913_ = v_index_1923_;
goto v___jp_1911_;
}
default: 
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_unsigned_to_nat(0u);
v___x_1925_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1918_, v___x_1924_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_index_1926_; 
v_index_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_index_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___y_1912_ = v___x_1918_;
v_i_1913_ = v_index_1926_;
goto v___jp_1911_;
}
else
{
lean_dec(v___x_1898_);
v___y_1904_ = v___x_1918_;
goto v___jp_1903_;
}
}
}
}
v___jp_1927_:
{
lean_object* v_size_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_size_1930_ = lean_ctor_get(v___y_1928_, 0);
v___x_1931_ = lean_nat_add(v_size_1930_, v___x_1899_);
lean_inc(v_fvarId_1897_);
v___x_1932_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1928_, v___x_1931_, v_i_1929_, v_fvarId_1897_, v___x_1898_);
lean_dec(v_i_1929_);
v___y_1904_ = v___x_1932_;
goto v___jp_1903_;
}
v___jp_1933_:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg(v___y_1934_, v_fvarId_1897_);
switch(lean_obj_tag(v___x_1935_))
{
case 0:
{
lean_object* v_index_1936_; lean_object* v_size_1937_; lean_object* v___x_1938_; 
v_index_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_index_1936_);
lean_dec_ref_known(v___x_1935_, 3);
v_size_1937_ = lean_ctor_get(v___y_1934_, 0);
lean_inc(v_size_1937_);
lean_inc(v_fvarId_1897_);
v___x_1938_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1934_, v_size_1937_, v_index_1936_, v_fvarId_1897_, v___x_1898_);
lean_dec(v_index_1936_);
v___y_1904_ = v___x_1938_;
goto v___jp_1903_;
}
case 1:
{
lean_object* v_index_1939_; 
v_index_1939_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_index_1939_);
lean_dec_ref_known(v___x_1935_, 1);
v___y_1928_ = v___y_1934_;
v_i_1929_ = v_index_1939_;
goto v___jp_1927_;
}
default: 
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1934_, v___x_1940_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_index_1942_; 
v_index_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_index_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v___y_1928_ = v___y_1934_;
v_i_1929_ = v_index_1942_;
goto v___jp_1927_;
}
else
{
lean_dec(v___x_1898_);
v___y_1904_ = v___y_1934_;
goto v___jp_1903_;
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg___boxed(lean_object* v_as_1977_, lean_object* v_sz_1978_, lean_object* v_i_1979_, lean_object* v_b_1980_, lean_object* v___y_1981_){
_start:
{
size_t v_sz_boxed_1982_; size_t v_i_boxed_1983_; lean_object* v_res_1984_; 
v_sz_boxed_1982_ = lean_unbox_usize(v_sz_1978_);
lean_dec(v_sz_1978_);
v_i_boxed_1983_ = lean_unbox_usize(v_i_1979_);
lean_dec(v_i_1979_);
v_res_1984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_1977_, v_sz_boxed_1982_, v_i_boxed_1983_, v_b_1980_);
lean_dec_ref(v_as_1977_);
return v_res_1984_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_betaReduce___closed__0(void){
_start:
{
lean_object* v_cellCount_1985_; lean_object* v___x_1986_; 
v_cellCount_1985_ = lean_unsigned_to_nat(16u);
v___x_1986_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1985_);
return v___x_1986_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_betaReduce___closed__1(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v_subst_1990_; 
v___x_1987_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_betaReduce___closed__0, &l_Lean_Compiler_LCNF_Simp_betaReduce___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_betaReduce___closed__0);
v___x_1988_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0);
v___x_1989_ = lean_unsigned_to_nat(0u);
v_subst_1990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_subst_1990_, 0, v___x_1989_);
lean_ctor_set(v_subst_1990_, 1, v___x_1988_);
lean_ctor_set(v_subst_1990_, 2, v___x_1987_);
return v_subst_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object* v_params_1991_, lean_object* v_code_1992_, lean_object* v_args_1993_, uint8_t v_mustInline_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v___x_2003_; lean_object* v_subst_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; size_t v_sz_2008_; size_t v___x_2009_; lean_object* v___x_2010_; 
v___x_2003_ = lean_unsigned_to_nat(0u);
v_subst_2004_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_betaReduce___closed__1, &l_Lean_Compiler_LCNF_Simp_betaReduce___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_betaReduce___closed__1);
v___x_2005_ = lean_array_get_size(v_args_1993_);
v___x_2006_ = l_Array_toSubarray___redArg(v_args_1993_, v___x_2003_, v___x_2005_);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v_subst_2004_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v_sz_2008_ = lean_array_size(v_params_1991_);
v___x_2009_ = ((size_t)0ULL);
v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_params_1991_, v_sz_2008_, v___x_2009_, v___x_2007_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v_fst_2012_; uint8_t v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v_fst_2012_ = lean_ctor_get(v_a_2011_, 0);
lean_inc(v_fst_2012_);
lean_dec(v_a_2011_);
v___x_2013_ = 0;
v___x_2014_ = 0;
v___x_2015_ = l_Lean_Compiler_LCNF_Code_internalize(v___x_2013_, v_code_1992_, v_fst_2012_, v___x_2014_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2017_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_n(v_a_2016_, 2);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2017_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_a_2016_, v_mustInline_1994_, v_a_1996_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v___x_2017_, 0);
lean_dec(v_unused_2025_);
v___x_2019_ = v___x_2017_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_dec(v___x_2017_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v_a_2016_);
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2016_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_a_2016_);
v_a_2026_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2017_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2017_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
return v___x_2015_;
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v_code_1992_);
v_a_2034_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2010_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2010_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object* v_params_2042_, lean_object* v_code_2043_, lean_object* v_args_2044_, lean_object* v_mustInline_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
uint8_t v_mustInline_boxed_2054_; lean_object* v_res_2055_; 
v_mustInline_boxed_2054_ = lean_unbox(v_mustInline_2045_);
v_res_2055_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_2042_, v_code_2043_, v_args_2044_, v_mustInline_boxed_2054_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec_ref(v_params_2042_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0(lean_object* v_00_u03b2_2056_, lean_object* v_m_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_m_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___boxed(lean_object* v_00_u03b2_2059_, lean_object* v_m_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0(v_00_u03b2_2059_, v_m_2060_);
lean_dec_ref(v_m_2060_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(lean_object* v_as_2062_, size_t v_sz_2063_, size_t v_i_2064_, lean_object* v_b_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_2062_, v_sz_2063_, v_i_2064_, v_b_2065_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___boxed(lean_object* v_as_2075_, lean_object* v_sz_2076_, lean_object* v_i_2077_, lean_object* v_b_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
size_t v_sz_boxed_2087_; size_t v_i_boxed_2088_; lean_object* v_res_2089_; 
v_sz_boxed_2087_ = lean_unbox_usize(v_sz_2076_);
lean_dec(v_sz_2076_);
v_i_boxed_2088_ = lean_unbox_usize(v_i_2077_);
lean_dec(v_i_2077_);
v_res_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(v_as_2075_, v_sz_boxed_2087_, v_i_boxed_2088_, v_b_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec_ref(v_as_2075_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(lean_object* v_00_u03b2_2090_, lean_object* v_init_2091_, lean_object* v_b_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_init_2091_, v_b_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2094_, lean_object* v_init_2095_, lean_object* v_b_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(v_00_u03b2_2094_, v_init_2095_, v_b_2096_);
lean_dec_ref(v_b_2096_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2098_, lean_object* v_b_2099_, lean_object* v_acc_2100_, lean_object* v_i_2101_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_spec__1___redArg(v_b_2099_, v_acc_2100_, v_i_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2103_, lean_object* v_b_2104_, lean_object* v_acc_2105_, lean_object* v_i_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_spec__1(v_00_u03b2_2103_, v_b_2104_, v_acc_2105_, v_i_2106_);
lean_dec_ref(v_b_2104_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object* v_decl_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
uint8_t v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = 0;
v___x_2113_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2112_, v_decl_2108_, v_a_2110_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v___x_2114_; 
lean_dec_ref_known(v___x_2113_, 1);
v___x_2114_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2109_);
return v___x_2114_;
}
else
{
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg___boxed(lean_object* v_decl_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2115_, v_a_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_decl_2115_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object* v_decl_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2120_, v_a_2122_, v_a_2125_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object* v_decl_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(v_decl_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec_ref(v_decl_2130_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object* v_decl_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
uint8_t v___x_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = 0;
v___x_2145_ = 1;
v___x_2146_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_2144_, v_decl_2140_, v___x_2145_, v_a_2142_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v___x_2147_; 
lean_dec_ref_known(v___x_2146_, 1);
v___x_2147_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2141_);
return v___x_2147_;
}
else
{
return v___x_2146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg___boxed(lean_object* v_decl_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2148_, v_a_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_decl_2148_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object* v_decl_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2153_, v_a_2155_, v_a_2158_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object* v_decl_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(v_decl_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec_ref(v_decl_2163_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object* v_fvarId_2173_, lean_object* v_fvarId_x27_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v___x_2181_; lean_object* v_subst_2182_; lean_object* v_used_2183_; lean_object* v_binderRenaming_2184_; lean_object* v_funDeclInfoMap_2185_; uint8_t v_simplified_2186_; lean_object* v_visited_2187_; lean_object* v_inline_2188_; lean_object* v_inlineLocal_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2324_; 
v___x_2181_ = lean_st_ref_take(v_a_2175_);
v_subst_2182_ = lean_ctor_get(v___x_2181_, 0);
v_used_2183_ = lean_ctor_get(v___x_2181_, 1);
v_binderRenaming_2184_ = lean_ctor_get(v___x_2181_, 2);
v_funDeclInfoMap_2185_ = lean_ctor_get(v___x_2181_, 3);
v_simplified_2186_ = lean_ctor_get_uint8(v___x_2181_, sizeof(void*)*7);
v_visited_2187_ = lean_ctor_get(v___x_2181_, 4);
v_inline_2188_ = lean_ctor_get(v___x_2181_, 5);
v_inlineLocal_2189_ = lean_ctor_get(v___x_2181_, 6);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2191_ = v___x_2181_;
v_isShared_2192_ = v_isSharedCheck_2324_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_inlineLocal_2189_);
lean_inc(v_inline_2188_);
lean_inc(v_visited_2187_);
lean_inc(v_funDeclInfoMap_2185_);
lean_inc(v_binderRenaming_2184_);
lean_inc(v_used_2183_);
lean_inc(v_subst_2182_);
lean_dec(v___x_2181_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2324_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___y_2194_; lean_object* v___x_2259_; lean_object* v___y_2261_; lean_object* v_i_2262_; lean_object* v___y_2268_; lean_object* v___y_2278_; lean_object* v_i_2279_; lean_object* v___x_2294_; 
lean_inc(v_fvarId_x27_2174_);
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v_fvarId_x27_2174_);
v___x_2294_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg(v_subst_2182_, v_fvarId_2173_);
switch(lean_obj_tag(v___x_2294_))
{
case 0:
{
lean_object* v_index_2295_; lean_object* v_size_2296_; lean_object* v___x_2297_; 
v_index_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_index_2295_);
lean_dec_ref_known(v___x_2294_, 3);
v_size_2296_ = lean_ctor_get(v_subst_2182_, 0);
lean_inc(v_size_2296_);
lean_inc(v_fvarId_2173_);
v___x_2297_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_2182_, v_size_2296_, v_index_2295_, v_fvarId_2173_, v___x_2259_);
lean_dec(v_index_2295_);
v___y_2194_ = v___x_2297_;
goto v___jp_2193_;
}
case 1:
{
lean_object* v_index_2298_; lean_object* v_size_2299_; lean_object* v_keyArray_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v_index_2298_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_index_2298_);
lean_dec_ref_known(v___x_2294_, 1);
v_size_2299_ = lean_ctor_get(v_subst_2182_, 0);
v_keyArray_2300_ = lean_ctor_get(v_subst_2182_, 1);
v___x_2301_ = lean_unsigned_to_nat(1u);
v___x_2302_ = lean_nat_add(v_size_2299_, v___x_2301_);
v___x_2303_ = lean_array_get_size(v_keyArray_2300_);
v___x_2304_ = lean_nat_dec_lt(v___x_2302_, v___x_2303_);
if (v___x_2304_ == 0)
{
lean_dec(v___x_2302_);
lean_dec(v_index_2298_);
goto v___jp_2284_;
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2305_ = lean_unsigned_to_nat(4u);
v___x_2306_ = lean_nat_mul(v___x_2302_, v___x_2305_);
v___x_2307_ = lean_unsigned_to_nat(3u);
v___x_2308_ = lean_nat_mul(v___x_2303_, v___x_2307_);
v___x_2309_ = lean_nat_dec_le(v___x_2306_, v___x_2308_);
lean_dec(v___x_2308_);
lean_dec(v___x_2306_);
if (v___x_2309_ == 0)
{
lean_dec(v___x_2302_);
lean_dec(v_index_2298_);
goto v___jp_2284_;
}
else
{
lean_object* v___x_2310_; 
lean_inc(v_fvarId_2173_);
v___x_2310_ = l_Std_DHashMap_Raw_setEntry___redArg(v_subst_2182_, v___x_2302_, v_index_2298_, v_fvarId_2173_, v___x_2259_);
lean_dec(v_index_2298_);
v___y_2194_ = v___x_2310_;
goto v___jp_2193_;
}
}
}
default: 
{
lean_object* v_size_2311_; lean_object* v_keyArray_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v_size_2311_ = lean_ctor_get(v_subst_2182_, 0);
v_keyArray_2312_ = lean_ctor_get(v_subst_2182_, 1);
v___x_2313_ = lean_unsigned_to_nat(1u);
v___x_2314_ = lean_nat_add(v_size_2311_, v___x_2313_);
v___x_2315_ = lean_array_get_size(v_keyArray_2312_);
v___x_2316_ = lean_nat_dec_lt(v___x_2314_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; 
lean_dec(v___x_2314_);
v___x_2317_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_subst_2182_);
lean_dec_ref(v_subst_2182_);
v___y_2268_ = v___x_2317_;
goto v___jp_2267_;
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2318_ = lean_unsigned_to_nat(4u);
v___x_2319_ = lean_nat_mul(v___x_2314_, v___x_2318_);
lean_dec(v___x_2314_);
v___x_2320_ = lean_unsigned_to_nat(3u);
v___x_2321_ = lean_nat_mul(v___x_2315_, v___x_2320_);
v___x_2322_ = lean_nat_dec_le(v___x_2319_, v___x_2321_);
lean_dec(v___x_2321_);
lean_dec(v___x_2319_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_subst_2182_);
lean_dec_ref(v_subst_2182_);
v___y_2268_ = v___x_2323_;
goto v___jp_2267_;
}
else
{
v___y_2268_ = v_subst_2182_;
goto v___jp_2267_;
}
}
}
}
v___jp_2193_:
{
lean_object* v___x_2196_; 
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___y_2194_);
v___x_2196_ = v___x_2191_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___y_2194_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_used_2183_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_binderRenaming_2184_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_funDeclInfoMap_2185_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v_visited_2187_);
lean_ctor_set(v_reuseFailAlloc_2258_, 5, v_inline_2188_);
lean_ctor_set(v_reuseFailAlloc_2258_, 6, v_inlineLocal_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*7, v_simplified_2186_);
v___x_2196_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_st_ref_put(v_a_2175_, v___x_2196_);
v___x_2198_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_2173_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2249_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2249_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2249_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
uint8_t v___x_2203_; 
v___x_2203_ = l_Lean_Name_isInternal(v_a_2199_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; 
lean_del_object(v___x_2201_);
lean_inc(v_fvarId_x27_2174_);
v___x_2204_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_x27_2174_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2236_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2236_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2236_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
uint8_t v___x_2209_; 
v___x_2209_ = l_Lean_Name_isInternal(v_a_2205_);
lean_dec(v_a_2205_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
lean_dec(v_a_2199_);
lean_dec(v_fvarId_x27_2174_);
v___x_2210_ = lean_box(0);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2210_);
v___x_2212_ = v___x_2207_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
else
{
lean_object* v___x_2214_; lean_object* v_subst_2215_; lean_object* v_used_2216_; lean_object* v_binderRenaming_2217_; lean_object* v_funDeclInfoMap_2218_; uint8_t v_simplified_2219_; lean_object* v_visited_2220_; lean_object* v_inline_2221_; lean_object* v_inlineLocal_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2235_; 
v___x_2214_ = lean_st_ref_take(v_a_2175_);
v_subst_2215_ = lean_ctor_get(v___x_2214_, 0);
v_used_2216_ = lean_ctor_get(v___x_2214_, 1);
v_binderRenaming_2217_ = lean_ctor_get(v___x_2214_, 2);
v_funDeclInfoMap_2218_ = lean_ctor_get(v___x_2214_, 3);
v_simplified_2219_ = lean_ctor_get_uint8(v___x_2214_, sizeof(void*)*7);
v_visited_2220_ = lean_ctor_get(v___x_2214_, 4);
v_inline_2221_ = lean_ctor_get(v___x_2214_, 5);
v_inlineLocal_2222_ = lean_ctor_get(v___x_2214_, 6);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2224_ = v___x_2214_;
v_isShared_2225_ = v_isSharedCheck_2235_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_inlineLocal_2222_);
lean_inc(v_inline_2221_);
lean_inc(v_visited_2220_);
lean_inc(v_funDeclInfoMap_2218_);
lean_inc(v_binderRenaming_2217_);
lean_inc(v_used_2216_);
lean_inc(v_subst_2215_);
lean_dec(v___x_2214_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2235_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2226_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_x27_2174_, v_a_2199_, v_binderRenaming_2217_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 2, v___x_2226_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_subst_2215_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_used_2216_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v___x_2226_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v_funDeclInfoMap_2218_);
lean_ctor_set(v_reuseFailAlloc_2234_, 4, v_visited_2220_);
lean_ctor_set(v_reuseFailAlloc_2234_, 5, v_inline_2221_);
lean_ctor_set(v_reuseFailAlloc_2234_, 6, v_inlineLocal_2222_);
lean_ctor_set_uint8(v_reuseFailAlloc_2234_, sizeof(void*)*7, v_simplified_2219_);
v___x_2228_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2229_ = lean_st_ref_put(v_a_2175_, v___x_2228_);
v___x_2230_ = lean_box(0);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2230_);
v___x_2232_ = v___x_2207_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec(v_a_2199_);
lean_dec(v_fvarId_x27_2174_);
v_a_2237_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2204_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2204_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
lean_dec(v_a_2199_);
lean_dec(v_fvarId_x27_2174_);
v___x_2245_ = lean_box(0);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2245_);
v___x_2247_ = v___x_2201_;
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
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v_fvarId_x27_2174_);
v_a_2250_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2198_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2198_);
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
}
v___jp_2260_:
{
lean_object* v_size_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_size_2263_ = lean_ctor_get(v___y_2261_, 0);
v___x_2264_ = lean_unsigned_to_nat(1u);
v___x_2265_ = lean_nat_add(v_size_2263_, v___x_2264_);
lean_inc(v_fvarId_2173_);
v___x_2266_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2261_, v___x_2265_, v_i_2262_, v_fvarId_2173_, v___x_2259_);
lean_dec(v_i_2262_);
v___y_2194_ = v___x_2266_;
goto v___jp_2193_;
}
v___jp_2267_:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg(v___y_2268_, v_fvarId_2173_);
switch(lean_obj_tag(v___x_2269_))
{
case 0:
{
lean_object* v_index_2270_; lean_object* v_size_2271_; lean_object* v___x_2272_; 
v_index_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_index_2270_);
lean_dec_ref_known(v___x_2269_, 3);
v_size_2271_ = lean_ctor_get(v___y_2268_, 0);
lean_inc(v_size_2271_);
lean_inc(v_fvarId_2173_);
v___x_2272_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2268_, v_size_2271_, v_index_2270_, v_fvarId_2173_, v___x_2259_);
lean_dec(v_index_2270_);
v___y_2194_ = v___x_2272_;
goto v___jp_2193_;
}
case 1:
{
lean_object* v_index_2273_; 
v_index_2273_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_index_2273_);
lean_dec_ref_known(v___x_2269_, 1);
v___y_2261_ = v___y_2268_;
v_i_2262_ = v_index_2273_;
goto v___jp_2260_;
}
default: 
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = lean_unsigned_to_nat(0u);
v___x_2275_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2268_, v___x_2274_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_index_2276_; 
v_index_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_index_2276_);
lean_dec_ref_known(v___x_2275_, 1);
v___y_2261_ = v___y_2268_;
v_i_2262_ = v_index_2276_;
goto v___jp_2260_;
}
else
{
lean_dec_ref_known(v___x_2259_, 1);
v___y_2194_ = v___y_2268_;
goto v___jp_2193_;
}
}
}
}
v___jp_2277_:
{
lean_object* v_size_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_size_2280_ = lean_ctor_get(v___y_2278_, 0);
v___x_2281_ = lean_unsigned_to_nat(1u);
v___x_2282_ = lean_nat_add(v_size_2280_, v___x_2281_);
lean_inc(v_fvarId_2173_);
v___x_2283_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2278_, v___x_2282_, v_i_2279_, v_fvarId_2173_, v___x_2259_);
lean_dec(v_i_2279_);
v___y_2194_ = v___x_2283_;
goto v___jp_2193_;
}
v___jp_2284_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_subst_2182_);
lean_dec_ref(v_subst_2182_);
v___x_2286_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0_spec__1___redArg(v___x_2285_, v_fvarId_2173_);
switch(lean_obj_tag(v___x_2286_))
{
case 0:
{
lean_object* v_index_2287_; lean_object* v_size_2288_; lean_object* v___x_2289_; 
v_index_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_index_2287_);
lean_dec_ref_known(v___x_2286_, 3);
v_size_2288_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_size_2288_);
lean_inc(v_fvarId_2173_);
v___x_2289_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2285_, v_size_2288_, v_index_2287_, v_fvarId_2173_, v___x_2259_);
lean_dec(v_index_2287_);
v___y_2194_ = v___x_2289_;
goto v___jp_2193_;
}
case 1:
{
lean_object* v_index_2290_; 
v_index_2290_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_index_2290_);
lean_dec_ref_known(v___x_2286_, 1);
v___y_2278_ = v___x_2285_;
v_i_2279_ = v_index_2290_;
goto v___jp_2277_;
}
default: 
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2285_, v___x_2291_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_index_2293_; 
v_index_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_index_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v___y_2278_ = v___x_2285_;
v_i_2279_ = v_index_2293_;
goto v___jp_2277_;
}
else
{
lean_dec_ref_known(v___x_2259_, 1);
v___y_2194_ = v___x_2285_;
goto v___jp_2193_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg___boxed(lean_object* v_fvarId_2325_, lean_object* v_fvarId_x27_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2325_, v_fvarId_x27_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_a_2327_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object* v_fvarId_2334_, lean_object* v_fvarId_x27_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2334_, v_fvarId_x27_2335_, v_a_2337_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___boxed(lean_object* v_fvarId_2345_, lean_object* v_fvarId_x27_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst(v_fvarId_2345_, v_fvarId_x27_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
return v_res_2355_;
}
}
lean_object* runtime_initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Renaming(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Config(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Renaming(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Simp_instMonadSimpM = _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadSimpM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Renaming(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_JpCases(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Config(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Renaming(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
}
#ifdef __cplusplus
}
#endif
