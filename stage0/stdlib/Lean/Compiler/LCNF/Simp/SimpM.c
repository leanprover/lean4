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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
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
v___x_191_ = lean_st_ref_set(v___y_169_, v___x_190_);
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
v___x_224_ = lean_st_ref_set(v_a_208_, v___x_223_);
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
v___x_268_ = lean_st_ref_set(v_a_250_, v___x_267_);
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
v___x_312_ = lean_st_ref_set(v_a_294_, v___x_311_);
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
v___x_356_ = lean_st_ref_set(v_a_338_, v___x_355_);
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
v___x_400_ = lean_st_ref_set(v_a_383_, v___x_399_);
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
v___x_447_ = lean_st_ref_set(v_a_430_, v___x_446_);
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
v___x_494_ = lean_st_ref_set(v_a_477_, v___x_493_);
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
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_box(0);
v___x_524_ = lean_unsigned_to_nat(16u);
v___x_525_ = lean_mk_array(v___x_524_, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_526_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object* v_code_529_, uint8_t v_mustInline_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_537_; lean_object* v_subst_538_; lean_object* v_used_539_; lean_object* v_binderRenaming_540_; lean_object* v_funDeclInfoMap_541_; uint8_t v_simplified_542_; lean_object* v_visited_543_; lean_object* v_inline_544_; lean_object* v_inlineLocal_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_589_; 
v___x_537_ = lean_st_ref_take(v_a_531_);
v_subst_538_ = lean_ctor_get(v___x_537_, 0);
v_used_539_ = lean_ctor_get(v___x_537_, 1);
v_binderRenaming_540_ = lean_ctor_get(v___x_537_, 2);
v_funDeclInfoMap_541_ = lean_ctor_get(v___x_537_, 3);
v_simplified_542_ = lean_ctor_get_uint8(v___x_537_, sizeof(void*)*7);
v_visited_543_ = lean_ctor_get(v___x_537_, 4);
v_inline_544_ = lean_ctor_get(v___x_537_, 5);
v_inlineLocal_545_ = lean_ctor_get(v___x_537_, 6);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_589_ == 0)
{
v___x_547_ = v___x_537_;
v_isShared_548_ = v_isSharedCheck_589_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_inlineLocal_545_);
lean_inc(v_inline_544_);
lean_inc(v_visited_543_);
lean_inc(v_funDeclInfoMap_541_);
lean_inc(v_binderRenaming_540_);
lean_inc(v_used_539_);
lean_inc(v_subst_538_);
lean_dec(v___x_537_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_589_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 3, v___x_549_);
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_subst_538_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_used_539_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_binderRenaming_540_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v_visited_543_);
lean_ctor_set(v_reuseFailAlloc_588_, 5, v_inline_544_);
lean_ctor_set(v_reuseFailAlloc_588_, 6, v_inlineLocal_545_);
lean_ctor_set_uint8(v_reuseFailAlloc_588_, sizeof(void*)*7, v_simplified_542_);
v___x_551_ = v_reuseFailAlloc_588_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_st_ref_set(v_a_531_, v___x_551_);
v___x_553_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(v_funDeclInfoMap_541_, v_code_529_, v_mustInline_530_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_579_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_579_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_579_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_579_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v_subst_559_; lean_object* v_used_560_; lean_object* v_binderRenaming_561_; uint8_t v_simplified_562_; lean_object* v_visited_563_; lean_object* v_inline_564_; lean_object* v_inlineLocal_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_577_; 
v___x_558_ = lean_st_ref_take(v_a_531_);
v_subst_559_ = lean_ctor_get(v___x_558_, 0);
v_used_560_ = lean_ctor_get(v___x_558_, 1);
v_binderRenaming_561_ = lean_ctor_get(v___x_558_, 2);
v_simplified_562_ = lean_ctor_get_uint8(v___x_558_, sizeof(void*)*7);
v_visited_563_ = lean_ctor_get(v___x_558_, 4);
v_inline_564_ = lean_ctor_get(v___x_558_, 5);
v_inlineLocal_565_ = lean_ctor_get(v___x_558_, 6);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v___x_558_, 3);
lean_dec(v_unused_578_);
v___x_567_ = v___x_558_;
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_inlineLocal_565_);
lean_inc(v_inline_564_);
lean_inc(v_visited_563_);
lean_inc(v_binderRenaming_561_);
lean_inc(v_used_560_);
lean_inc(v_subst_559_);
lean_dec(v___x_558_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 3, v_a_554_);
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_subst_559_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_used_560_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_binderRenaming_561_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_a_554_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v_visited_563_);
lean_ctor_set(v_reuseFailAlloc_576_, 5, v_inline_564_);
lean_ctor_set(v_reuseFailAlloc_576_, 6, v_inlineLocal_565_);
lean_ctor_set_uint8(v_reuseFailAlloc_576_, sizeof(void*)*7, v_simplified_562_);
v___x_570_ = v_reuseFailAlloc_576_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_571_ = lean_st_ref_set(v_a_531_, v___x_570_);
v___x_572_ = lean_box(0);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_572_);
v___x_574_ = v___x_556_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_a_580_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_553_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_553_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___boxed(lean_object* v_code_590_, lean_object* v_mustInline_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
uint8_t v_mustInline_boxed_598_; lean_object* v_res_599_; 
v_mustInline_boxed_598_ = lean_unbox(v_mustInline_591_);
v_res_599_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_590_, v_mustInline_boxed_598_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object* v_code_600_, uint8_t v_mustInline_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_600_, v_mustInline_601_, v_a_603_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___boxed(lean_object* v_code_611_, lean_object* v_mustInline_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
uint8_t v_mustInline_boxed_621_; lean_object* v_res_622_; 
v_mustInline_boxed_621_ = lean_unbox(v_mustInline_612_);
v_res_622_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(v_code_611_, v_mustInline_boxed_621_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
return v_res_622_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_623_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
lean_ctor_set(v___x_628_, 3, v___x_627_);
lean_ctor_set(v___x_628_, 4, v___x_626_);
lean_ctor_set(v___x_628_, 5, v___x_626_);
lean_ctor_set(v___x_628_, 6, v___x_626_);
lean_ctor_set(v___x_628_, 7, v___x_626_);
lean_ctor_set(v___x_628_, 8, v___x_626_);
lean_ctor_set(v___x_628_, 9, v___x_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_options_635_; lean_object* v_ref_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_options_635_ = lean_ctor_get(v___y_632_, 2);
v_ref_636_ = lean_ctor_get(v___y_632_, 5);
v___x_637_ = lean_st_ref_get(v___y_633_);
v___x_638_ = lean_st_ref_get(v___y_631_);
v___x_639_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_630_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_662_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_662_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_662_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_662_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_env_644_; lean_object* v_lctx_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_660_; 
v_env_644_ = lean_ctor_get(v___x_637_, 0);
lean_inc_ref(v_env_644_);
lean_dec(v___x_637_);
v_lctx_645_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v___x_638_, 1);
lean_dec(v_unused_661_);
v___x_647_ = v___x_638_;
v_isShared_648_ = v_isSharedCheck_660_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_lctx_645_);
lean_dec(v___x_638_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_660_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_649_ = lean_unbox(v_a_640_);
lean_dec(v_a_640_);
v___x_650_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_645_, v___x_649_);
lean_dec_ref(v_lctx_645_);
v___x_651_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2);
lean_inc_ref(v_options_635_);
v___x_652_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_652_, 0, v_env_644_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
lean_ctor_set(v___x_652_, 2, v___x_650_);
lean_ctor_set(v___x_652_, 3, v_options_635_);
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 3);
lean_ctor_set(v___x_647_, 1, v_msg_629_);
lean_ctor_set(v___x_647_, 0, v___x_652_);
v___x_654_ = v___x_647_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_msg_629_);
v___x_654_ = v_reuseFailAlloc_659_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; lean_object* v___x_657_; 
lean_inc(v_ref_636_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v_ref_636_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 1);
lean_ctor_set(v___x_642_, 0, v___x_655_);
v___x_657_ = v___x_642_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec(v___x_638_);
lean_dec(v___x_637_);
lean_dec_ref(v_msg_629_);
v_a_663_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_639_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_639_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___boxed(lean_object* v_msg_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v_msg_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0(lean_object* v_00_u03b1_678_, lean_object* v_msg_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v_msg_679_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___boxed(lean_object* v_00_u03b1_689_, lean_object* v_msg_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0(v_00_u03b1_689_, v_msg_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
return v_res_699_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_700_; double v___x_701_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_float_of_nat(v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(lean_object* v_cls_705_, lean_object* v_msg_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_options_712_; lean_object* v_ref_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_options_712_ = lean_ctor_get(v___y_709_, 2);
v_ref_713_ = lean_ctor_get(v___y_709_, 5);
v___x_714_ = lean_st_ref_get(v___y_710_);
v___x_715_ = lean_st_ref_get(v___y_708_);
v___x_716_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_707_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_775_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_775_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_775_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_775_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_env_721_; lean_object* v_lctx_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_773_; 
v_env_721_ = lean_ctor_get(v___x_714_, 0);
lean_inc_ref(v_env_721_);
lean_dec(v___x_714_);
v_lctx_722_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v___x_715_, 1);
lean_dec(v_unused_774_);
v___x_724_ = v___x_715_;
v_isShared_725_ = v_isSharedCheck_773_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_lctx_722_);
lean_dec(v___x_715_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_773_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_traceState_728_; lean_object* v_env_729_; lean_object* v_nextMacroScope_730_; lean_object* v_ngen_731_; lean_object* v_auxDeclNGen_732_; lean_object* v_cache_733_; lean_object* v_messages_734_; lean_object* v_infoState_735_; lean_object* v_snapshotTasks_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_772_; 
v___x_726_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2);
v___x_727_ = lean_st_ref_take(v___y_710_);
v_traceState_728_ = lean_ctor_get(v___x_727_, 4);
v_env_729_ = lean_ctor_get(v___x_727_, 0);
v_nextMacroScope_730_ = lean_ctor_get(v___x_727_, 1);
v_ngen_731_ = lean_ctor_get(v___x_727_, 2);
v_auxDeclNGen_732_ = lean_ctor_get(v___x_727_, 3);
v_cache_733_ = lean_ctor_get(v___x_727_, 5);
v_messages_734_ = lean_ctor_get(v___x_727_, 6);
v_infoState_735_ = lean_ctor_get(v___x_727_, 7);
v_snapshotTasks_736_ = lean_ctor_get(v___x_727_, 8);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_772_ == 0)
{
v___x_738_ = v___x_727_;
v_isShared_739_ = v_isSharedCheck_772_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snapshotTasks_736_);
lean_inc(v_infoState_735_);
lean_inc(v_messages_734_);
lean_inc(v_cache_733_);
lean_inc(v_traceState_728_);
lean_inc(v_auxDeclNGen_732_);
lean_inc(v_ngen_731_);
lean_inc(v_nextMacroScope_730_);
lean_inc(v_env_729_);
lean_dec(v___x_727_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_772_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
uint64_t v_tid_740_; lean_object* v_traces_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_771_; 
v_tid_740_ = lean_ctor_get_uint64(v_traceState_728_, sizeof(void*)*1);
v_traces_741_ = lean_ctor_get(v_traceState_728_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_traceState_728_);
if (v_isSharedCheck_771_ == 0)
{
v___x_743_ = v_traceState_728_;
v_isShared_744_ = v_isSharedCheck_771_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_traces_741_);
lean_dec(v_traceState_728_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_771_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_745_ = lean_unbox(v_a_717_);
lean_dec(v_a_717_);
v___x_746_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_722_, v___x_745_);
lean_dec_ref(v_lctx_722_);
lean_inc_ref(v_options_712_);
v___x_747_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_747_, 0, v_env_721_);
lean_ctor_set(v___x_747_, 1, v___x_726_);
lean_ctor_set(v___x_747_, 2, v___x_746_);
lean_ctor_set(v___x_747_, 3, v_options_712_);
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 3);
lean_ctor_set(v___x_724_, 1, v_msg_706_);
lean_ctor_set(v___x_724_, 0, v___x_747_);
v___x_749_ = v___x_724_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_msg_706_);
v___x_749_ = v_reuseFailAlloc_770_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; double v___x_751_; uint8_t v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_750_ = lean_box(0);
v___x_751_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0);
v___x_752_ = 0;
v___x_753_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1));
v___x_754_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_754_, 0, v_cls_705_);
lean_ctor_set(v___x_754_, 1, v___x_750_);
lean_ctor_set(v___x_754_, 2, v___x_753_);
lean_ctor_set_float(v___x_754_, sizeof(void*)*3, v___x_751_);
lean_ctor_set_float(v___x_754_, sizeof(void*)*3 + 8, v___x_751_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*3 + 16, v___x_752_);
v___x_755_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__2));
v___x_756_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_749_);
lean_ctor_set(v___x_756_, 2, v___x_755_);
lean_inc(v_ref_713_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_ref_713_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_PersistentArray_push___redArg(v_traces_741_, v___x_757_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_758_);
v___x_760_ = v___x_743_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_758_);
lean_ctor_set_uint64(v_reuseFailAlloc_769_, sizeof(void*)*1, v_tid_740_);
v___x_760_ = v_reuseFailAlloc_769_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v___x_760_);
v___x_762_ = v___x_738_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_env_729_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_nextMacroScope_730_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v_ngen_731_);
lean_ctor_set(v_reuseFailAlloc_768_, 3, v_auxDeclNGen_732_);
lean_ctor_set(v_reuseFailAlloc_768_, 4, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_768_, 5, v_cache_733_);
lean_ctor_set(v_reuseFailAlloc_768_, 6, v_messages_734_);
lean_ctor_set(v_reuseFailAlloc_768_, 7, v_infoState_735_);
lean_ctor_set(v_reuseFailAlloc_768_, 8, v_snapshotTasks_736_);
v___x_762_ = v_reuseFailAlloc_768_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_763_ = lean_st_ref_set(v___y_710_, v___x_762_);
v___x_764_ = lean_box(0);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_764_);
v___x_766_ = v___x_719_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
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
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v___x_715_);
lean_dec(v___x_714_);
lean_dec_ref(v_msg_706_);
lean_dec(v_cls_705_);
v_a_776_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_716_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_716_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___boxed(lean_object* v_cls_784_, lean_object* v_msg_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_784_, v_msg_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(lean_object* v_cls_792_, lean_object* v_msg_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_792_, v_msg_793_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___boxed(lean_object* v_cls_803_, lean_object* v_msg_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(v_cls_803_, v_msg_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(lean_object* v_keys_814_, lean_object* v_vals_815_, lean_object* v_i_816_, lean_object* v_k_817_){
_start:
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_array_get_size(v_keys_814_);
v___x_819_ = lean_nat_dec_lt(v_i_816_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
lean_dec(v_i_816_);
v___x_820_ = lean_box(0);
return v___x_820_;
}
else
{
lean_object* v_k_x27_821_; uint8_t v___x_822_; 
v_k_x27_821_ = lean_array_fget_borrowed(v_keys_814_, v_i_816_);
v___x_822_ = lean_name_eq(v_k_817_, v_k_x27_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_add(v_i_816_, v___x_823_);
lean_dec(v_i_816_);
v_i_816_ = v___x_824_;
goto _start;
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_array_fget_borrowed(v_vals_815_, v_i_816_);
lean_dec(v_i_816_);
lean_inc(v___x_826_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_keys_828_, lean_object* v_vals_829_, lean_object* v_i_830_, lean_object* v_k_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(v_keys_828_, v_vals_829_, v_i_830_, v_k_831_);
lean_dec(v_k_831_);
lean_dec_ref(v_vals_829_);
lean_dec_ref(v_keys_828_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(lean_object* v_x_833_, size_t v_x_834_, lean_object* v_x_835_){
_start:
{
if (lean_obj_tag(v_x_833_) == 0)
{
lean_object* v_es_836_; lean_object* v___x_837_; size_t v___x_838_; size_t v___x_839_; lean_object* v_j_840_; lean_object* v___x_841_; 
v_es_836_ = lean_ctor_get(v_x_833_, 0);
v___x_837_ = lean_box(2);
v___x_838_ = ((size_t)31ULL);
v___x_839_ = lean_usize_land(v_x_834_, v___x_838_);
v_j_840_ = lean_usize_to_nat(v___x_839_);
v___x_841_ = lean_array_get_borrowed(v___x_837_, v_es_836_, v_j_840_);
lean_dec(v_j_840_);
switch(lean_obj_tag(v___x_841_))
{
case 0:
{
lean_object* v_key_842_; lean_object* v_val_843_; uint8_t v___x_844_; 
v_key_842_ = lean_ctor_get(v___x_841_, 0);
v_val_843_ = lean_ctor_get(v___x_841_, 1);
v___x_844_ = lean_name_eq(v_x_835_, v_key_842_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
v___x_845_ = lean_box(0);
return v___x_845_;
}
else
{
lean_object* v___x_846_; 
lean_inc(v_val_843_);
v___x_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_846_, 0, v_val_843_);
return v___x_846_;
}
}
case 1:
{
lean_object* v_node_847_; size_t v___x_848_; size_t v___x_849_; 
v_node_847_ = lean_ctor_get(v___x_841_, 0);
v___x_848_ = ((size_t)5ULL);
v___x_849_ = lean_usize_shift_right(v_x_834_, v___x_848_);
v_x_833_ = v_node_847_;
v_x_834_ = v___x_849_;
goto _start;
}
default: 
{
lean_object* v___x_851_; 
v___x_851_ = lean_box(0);
return v___x_851_;
}
}
}
else
{
lean_object* v_ks_852_; lean_object* v_vs_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_ks_852_ = lean_ctor_get(v_x_833_, 0);
v_vs_853_ = lean_ctor_get(v_x_833_, 1);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(v_ks_852_, v_vs_853_, v___x_854_, v_x_835_);
return v___x_855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___boxed(lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
size_t v_x_7604__boxed_859_; lean_object* v_res_860_; 
v_x_7604__boxed_859_ = lean_unbox_usize(v_x_857_);
lean_dec(v_x_857_);
v_res_860_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_856_, v_x_7604__boxed_859_, v_x_858_);
lean_dec(v_x_858_);
lean_dec_ref(v_x_856_);
return v_res_860_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_861_; uint64_t v___x_862_; 
v___x_861_ = lean_unsigned_to_nat(1723u);
v___x_862_ = lean_uint64_of_nat(v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
uint64_t v___y_866_; 
if (lean_obj_tag(v_x_864_) == 0)
{
uint64_t v___x_869_; 
v___x_869_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0);
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
v___x_992_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_988_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; uint8_t v___x_994_; lean_object* v___x_995_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = lean_unbox(v_a_993_);
lean_dec(v_a_993_);
lean_inc(v_declName_897_);
v___x_995_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_897_, v___x_994_, v___y_990_, v___y_985_);
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
v___y_909_ = v___y_984_;
v___y_910_ = v___y_989_;
v___y_911_ = v___y_987_;
v___y_912_ = v___y_988_;
v___y_913_ = v___y_986_;
v___y_914_ = v___y_990_;
v___y_915_ = v___y_985_;
goto v___jp_906_;
}
else
{
uint8_t v___x_1001_; 
lean_dec(v_a_996_);
v___x_1001_ = 0;
v___y_907_ = v___x_998_;
v_inlineIfReduce_908_ = v___x_1001_;
v___y_909_ = v___y_984_;
v___y_910_ = v___y_989_;
v___y_911_ = v___y_987_;
v___y_912_ = v___y_988_;
v___y_913_ = v___y_986_;
v___y_914_ = v___y_990_;
v___y_915_ = v___y_985_;
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
v___y_984_ = v___y_1019_;
v___y_985_ = v___y_1025_;
v___y_986_ = v___y_1023_;
v___y_987_ = v___y_1021_;
v___y_988_ = v___y_1022_;
v___y_989_ = v___y_1020_;
v___y_990_ = v___y_1024_;
v___y_991_ = v___x_1028_;
goto v___jp_983_;
}
else
{
lean_object* v_val_1029_; 
v_val_1029_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v___x_1027_, 1);
v___y_984_ = v___y_1019_;
v___y_985_ = v___y_1025_;
v___y_986_ = v___y_1023_;
v___y_987_ = v___y_1021_;
v___y_988_ = v___y_1022_;
v___y_989_ = v___y_1020_;
v___y_990_ = v___y_1024_;
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
size_t v_x_8020__boxed_1076_; lean_object* v_res_1077_; 
v_x_8020__boxed_1076_ = lean_unbox_usize(v_x_1074_);
lean_dec(v_x_1074_);
v_res_1077_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(v_00_u03b2_1072_, v_x_1073_, v_x_8020__boxed_1076_, v_x_1075_);
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
lean_object* v_fileName_1354_; lean_object* v_fileMap_1355_; lean_object* v_options_1356_; lean_object* v_currRecDepth_1357_; lean_object* v_maxRecDepth_1358_; lean_object* v_ref_1359_; lean_object* v_currNamespace_1360_; lean_object* v_openDecls_1361_; lean_object* v_initHeartbeats_1362_; lean_object* v_maxHeartbeats_1363_; lean_object* v_quotContext_1364_; lean_object* v_currMacroScope_1365_; uint8_t v_diag_1366_; lean_object* v_cancelTk_x3f_1367_; uint8_t v_suppressElabErrors_1368_; lean_object* v_inheritedTraceOptions_1369_; uint8_t v___y_1371_; lean_object* v___x_1377_; uint8_t v___x_1378_; uint8_t v___x_1379_; 
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
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = lean_nat_dec_eq(v_maxRecDepth_1358_, v___x_1377_);
v___x_1379_ = lean_bool_not(v___x_1378_);
if (v___x_1379_ == 0)
{
v___y_1371_ = v___x_1379_;
goto v___jp_1370_;
}
else
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_nat_dec_eq(v_currRecDepth_1357_, v_maxRecDepth_1358_);
v___y_1371_ = v___x_1380_;
goto v___jp_1370_;
}
v___jp_1370_:
{
if (v___y_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_nat_add(v_currRecDepth_1357_, v___x_1372_);
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
v___x_1374_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1374_, 0, v_fileName_1354_);
lean_ctor_set(v___x_1374_, 1, v_fileMap_1355_);
lean_ctor_set(v___x_1374_, 2, v_options_1356_);
lean_ctor_set(v___x_1374_, 3, v___x_1373_);
lean_ctor_set(v___x_1374_, 4, v_maxRecDepth_1358_);
lean_ctor_set(v___x_1374_, 5, v_ref_1359_);
lean_ctor_set(v___x_1374_, 6, v_currNamespace_1360_);
lean_ctor_set(v___x_1374_, 7, v_openDecls_1361_);
lean_ctor_set(v___x_1374_, 8, v_initHeartbeats_1362_);
lean_ctor_set(v___x_1374_, 9, v_maxHeartbeats_1363_);
lean_ctor_set(v___x_1374_, 10, v_quotContext_1364_);
lean_ctor_set(v___x_1374_, 11, v_currMacroScope_1365_);
lean_ctor_set(v___x_1374_, 12, v_cancelTk_x3f_1367_);
lean_ctor_set(v___x_1374_, 13, v_inheritedTraceOptions_1369_);
lean_ctor_set_uint8(v___x_1374_, sizeof(void*)*14, v_diag_1366_);
lean_ctor_set_uint8(v___x_1374_, sizeof(void*)*14 + 1, v_suppressElabErrors_1368_);
lean_inc(v_a_1352_);
lean_inc(v_a_1350_);
lean_inc_ref(v_a_1349_);
lean_inc_ref(v_a_1348_);
lean_inc(v_a_1347_);
lean_inc_ref(v_a_1346_);
v___x_1375_ = lean_apply_8(v_x_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v___x_1374_, v_a_1352_, lean_box(0));
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; 
lean_dec_ref(v_x_1345_);
v___x_1376_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
return v___x_1376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg___boxed(lean_object* v_x_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(v_x_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth(lean_object* v_00_u03b1_1391_, lean_object* v_x_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_fileName_1401_; lean_object* v_fileMap_1402_; lean_object* v_options_1403_; lean_object* v_currRecDepth_1404_; lean_object* v_maxRecDepth_1405_; lean_object* v_ref_1406_; lean_object* v_currNamespace_1407_; lean_object* v_openDecls_1408_; lean_object* v_initHeartbeats_1409_; lean_object* v_maxHeartbeats_1410_; lean_object* v_quotContext_1411_; lean_object* v_currMacroScope_1412_; uint8_t v_diag_1413_; lean_object* v_cancelTk_x3f_1414_; uint8_t v_suppressElabErrors_1415_; lean_object* v_inheritedTraceOptions_1416_; uint8_t v___y_1418_; lean_object* v___x_1424_; uint8_t v___x_1425_; uint8_t v___x_1426_; 
v_fileName_1401_ = lean_ctor_get(v_a_1398_, 0);
v_fileMap_1402_ = lean_ctor_get(v_a_1398_, 1);
v_options_1403_ = lean_ctor_get(v_a_1398_, 2);
v_currRecDepth_1404_ = lean_ctor_get(v_a_1398_, 3);
v_maxRecDepth_1405_ = lean_ctor_get(v_a_1398_, 4);
v_ref_1406_ = lean_ctor_get(v_a_1398_, 5);
v_currNamespace_1407_ = lean_ctor_get(v_a_1398_, 6);
v_openDecls_1408_ = lean_ctor_get(v_a_1398_, 7);
v_initHeartbeats_1409_ = lean_ctor_get(v_a_1398_, 8);
v_maxHeartbeats_1410_ = lean_ctor_get(v_a_1398_, 9);
v_quotContext_1411_ = lean_ctor_get(v_a_1398_, 10);
v_currMacroScope_1412_ = lean_ctor_get(v_a_1398_, 11);
v_diag_1413_ = lean_ctor_get_uint8(v_a_1398_, sizeof(void*)*14);
v_cancelTk_x3f_1414_ = lean_ctor_get(v_a_1398_, 12);
v_suppressElabErrors_1415_ = lean_ctor_get_uint8(v_a_1398_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1416_ = lean_ctor_get(v_a_1398_, 13);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = lean_nat_dec_eq(v_maxRecDepth_1405_, v___x_1424_);
v___x_1426_ = lean_bool_not(v___x_1425_);
if (v___x_1426_ == 0)
{
v___y_1418_ = v___x_1426_;
goto v___jp_1417_;
}
else
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_nat_dec_eq(v_currRecDepth_1404_, v_maxRecDepth_1405_);
v___y_1418_ = v___x_1427_;
goto v___jp_1417_;
}
v___jp_1417_:
{
if (v___y_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1419_ = lean_unsigned_to_nat(1u);
v___x_1420_ = lean_nat_add(v_currRecDepth_1404_, v___x_1419_);
lean_inc_ref(v_inheritedTraceOptions_1416_);
lean_inc(v_cancelTk_x3f_1414_);
lean_inc(v_currMacroScope_1412_);
lean_inc(v_quotContext_1411_);
lean_inc(v_maxHeartbeats_1410_);
lean_inc(v_initHeartbeats_1409_);
lean_inc(v_openDecls_1408_);
lean_inc(v_currNamespace_1407_);
lean_inc(v_ref_1406_);
lean_inc(v_maxRecDepth_1405_);
lean_inc_ref(v_options_1403_);
lean_inc_ref(v_fileMap_1402_);
lean_inc_ref(v_fileName_1401_);
v___x_1421_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1421_, 0, v_fileName_1401_);
lean_ctor_set(v___x_1421_, 1, v_fileMap_1402_);
lean_ctor_set(v___x_1421_, 2, v_options_1403_);
lean_ctor_set(v___x_1421_, 3, v___x_1420_);
lean_ctor_set(v___x_1421_, 4, v_maxRecDepth_1405_);
lean_ctor_set(v___x_1421_, 5, v_ref_1406_);
lean_ctor_set(v___x_1421_, 6, v_currNamespace_1407_);
lean_ctor_set(v___x_1421_, 7, v_openDecls_1408_);
lean_ctor_set(v___x_1421_, 8, v_initHeartbeats_1409_);
lean_ctor_set(v___x_1421_, 9, v_maxHeartbeats_1410_);
lean_ctor_set(v___x_1421_, 10, v_quotContext_1411_);
lean_ctor_set(v___x_1421_, 11, v_currMacroScope_1412_);
lean_ctor_set(v___x_1421_, 12, v_cancelTk_x3f_1414_);
lean_ctor_set(v___x_1421_, 13, v_inheritedTraceOptions_1416_);
lean_ctor_set_uint8(v___x_1421_, sizeof(void*)*14, v_diag_1413_);
lean_ctor_set_uint8(v___x_1421_, sizeof(void*)*14 + 1, v_suppressElabErrors_1415_);
lean_inc(v_a_1399_);
lean_inc(v_a_1397_);
lean_inc_ref(v_a_1396_);
lean_inc_ref(v_a_1395_);
lean_inc(v_a_1394_);
lean_inc_ref(v_a_1393_);
v___x_1422_ = lean_apply_8(v_x_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v___x_1421_, v_a_1399_, lean_box(0));
return v___x_1422_;
}
else
{
lean_object* v___x_1423_; 
lean_dec_ref(v_x_1392_);
v___x_1423_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___boxed(lean_object* v_00_u03b1_1428_, lean_object* v_x_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth(v_00_u03b1_1428_, v_x_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec_ref(v_a_1432_);
lean_dec(v_a_1431_);
lean_dec_ref(v_a_1430_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(lean_object* v_a_1439_, lean_object* v_fvarId_1440_, lean_object* v___x_1441_, lean_object* v_a_x3f_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v_subst_1445_; lean_object* v_used_1446_; lean_object* v_binderRenaming_1447_; lean_object* v_funDeclInfoMap_1448_; uint8_t v_simplified_1449_; lean_object* v_visited_1450_; lean_object* v_inline_1451_; lean_object* v_inlineLocal_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1463_; 
v___x_1444_ = lean_st_ref_take(v_a_1439_);
v_subst_1445_ = lean_ctor_get(v___x_1444_, 0);
v_used_1446_ = lean_ctor_get(v___x_1444_, 1);
v_binderRenaming_1447_ = lean_ctor_get(v___x_1444_, 2);
v_funDeclInfoMap_1448_ = lean_ctor_get(v___x_1444_, 3);
v_simplified_1449_ = lean_ctor_get_uint8(v___x_1444_, sizeof(void*)*7);
v_visited_1450_ = lean_ctor_get(v___x_1444_, 4);
v_inline_1451_ = lean_ctor_get(v___x_1444_, 5);
v_inlineLocal_1452_ = lean_ctor_get(v___x_1444_, 6);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1454_ = v___x_1444_;
v_isShared_1455_ = v_isSharedCheck_1463_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_inlineLocal_1452_);
lean_inc(v_inline_1451_);
lean_inc(v_visited_1450_);
lean_inc(v_funDeclInfoMap_1448_);
lean_inc(v_binderRenaming_1447_);
lean_inc(v_used_1446_);
lean_inc(v_subst_1445_);
lean_dec(v___x_1444_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1463_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(v_funDeclInfoMap_1448_, v_fvarId_1440_, v___x_1441_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 3, v___x_1456_);
v___x_1458_ = v___x_1454_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_subst_1445_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_used_1446_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_binderRenaming_1447_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_visited_1450_);
lean_ctor_set(v_reuseFailAlloc_1462_, 5, v_inline_1451_);
lean_ctor_set(v_reuseFailAlloc_1462_, 6, v_inlineLocal_1452_);
lean_ctor_set_uint8(v_reuseFailAlloc_1462_, sizeof(void*)*7, v_simplified_1449_);
v___x_1458_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = lean_st_ref_set(v_a_1439_, v___x_1458_);
v___x_1460_ = lean_box(0);
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
return v___x_1461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0___boxed(lean_object* v_a_1464_, lean_object* v_fvarId_1465_, lean_object* v___x_1466_, lean_object* v_a_x3f_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1464_, v_fvarId_1465_, v___x_1466_, v_a_x3f_1467_);
lean_dec(v_a_x3f_1467_);
lean_dec(v_a_1464_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(lean_object* v_a_1470_, lean_object* v_x_1471_){
_start:
{
if (lean_obj_tag(v_x_1471_) == 0)
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_box(0);
return v___x_1472_;
}
else
{
lean_object* v_key_1473_; lean_object* v_value_1474_; lean_object* v_tail_1475_; uint8_t v___x_1476_; 
v_key_1473_ = lean_ctor_get(v_x_1471_, 0);
v_value_1474_ = lean_ctor_get(v_x_1471_, 1);
v_tail_1475_ = lean_ctor_get(v_x_1471_, 2);
v___x_1476_ = l_Lean_instBEqFVarId_beq(v_key_1473_, v_a_1470_);
if (v___x_1476_ == 0)
{
v_x_1471_ = v_tail_1475_;
goto _start;
}
else
{
lean_object* v___x_1478_; 
lean_inc(v_value_1474_);
v___x_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1478_, 0, v_value_1474_);
return v___x_1478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg___boxed(lean_object* v_a_1479_, lean_object* v_x_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1479_, v_x_1480_);
lean_dec(v_x_1480_);
lean_dec(v_a_1479_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(lean_object* v_m_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v_buckets_1484_; lean_object* v___x_1485_; uint64_t v___x_1486_; uint64_t v___x_1487_; uint64_t v___x_1488_; uint64_t v_fold_1489_; uint64_t v___x_1490_; uint64_t v___x_1491_; uint64_t v___x_1492_; size_t v___x_1493_; size_t v___x_1494_; size_t v___x_1495_; size_t v___x_1496_; size_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_buckets_1484_ = lean_ctor_get(v_m_1482_, 1);
v___x_1485_ = lean_array_get_size(v_buckets_1484_);
v___x_1486_ = l_Lean_instHashableFVarId_hash(v_a_1483_);
v___x_1487_ = 32ULL;
v___x_1488_ = lean_uint64_shift_right(v___x_1486_, v___x_1487_);
v_fold_1489_ = lean_uint64_xor(v___x_1486_, v___x_1488_);
v___x_1490_ = 16ULL;
v___x_1491_ = lean_uint64_shift_right(v_fold_1489_, v___x_1490_);
v___x_1492_ = lean_uint64_xor(v_fold_1489_, v___x_1491_);
v___x_1493_ = lean_uint64_to_usize(v___x_1492_);
v___x_1494_ = lean_usize_of_nat(v___x_1485_);
v___x_1495_ = ((size_t)1ULL);
v___x_1496_ = lean_usize_sub(v___x_1494_, v___x_1495_);
v___x_1497_ = lean_usize_land(v___x_1493_, v___x_1496_);
v___x_1498_ = lean_array_uget_borrowed(v_buckets_1484_, v___x_1497_);
v___x_1499_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1483_, v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg___boxed(lean_object* v_m_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_m_1500_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(lean_object* v_fvarId_1503_, lean_object* v_x_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v_funDeclInfoMap_1514_; lean_object* v___x_1515_; lean_object* v_a_1517_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1513_ = lean_st_ref_get(v_a_1506_);
v_funDeclInfoMap_1514_ = lean_ctor_get(v___x_1513_, 3);
lean_inc_ref(v_funDeclInfoMap_1514_);
lean_dec(v___x_1513_);
v___x_1515_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_1514_, v_fvarId_1503_);
lean_dec_ref(v_funDeclInfoMap_1514_);
lean_inc(v_fvarId_1503_);
v___x_1528_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_1503_, v_a_1506_);
lean_dec_ref(v___x_1528_);
lean_inc(v_a_1511_);
lean_inc_ref(v_a_1510_);
lean_inc(v_a_1509_);
lean_inc_ref(v_a_1508_);
lean_inc_ref(v_a_1507_);
lean_inc(v_a_1506_);
lean_inc_ref(v_a_1505_);
v___x_1529_ = lean_apply_8(v_x_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, lean_box(0));
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1546_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1546_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1546_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
lean_inc(v_a_1530_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 1);
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
v___x_1536_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1506_, v_fvarId_1503_, v___x_1515_, v___x_1535_);
lean_dec_ref(v___x_1535_);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v___x_1536_, 0);
lean_dec(v_unused_1544_);
v___x_1538_ = v___x_1536_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_dec(v___x_1536_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v_a_1530_);
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1530_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
else
{
lean_object* v_a_1547_; 
v_a_1547_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1529_, 1);
v_a_1517_ = v_a_1547_;
goto v___jp_1516_;
}
v___jp_1516_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
v___x_1518_ = lean_box(0);
v___x_1519_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1506_, v_fvarId_1503_, v___x_1515_, v___x_1518_);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v___x_1519_, 0);
lean_dec(v_unused_1527_);
v___x_1521_ = v___x_1519_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_dec(v___x_1519_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set_tag(v___x_1521_, 1);
lean_ctor_set(v___x_1521_, 0, v_a_1517_);
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1517_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___boxed(lean_object* v_fvarId_1548_, lean_object* v_x_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1548_, v_x_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object* v_00_u03b1_1559_, lean_object* v_fvarId_1560_, lean_object* v_x_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1560_, v_x_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___boxed(lean_object* v_00_u03b1_1571_, lean_object* v_fvarId_1572_, lean_object* v_x_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline(v_00_u03b1_1571_, v_fvarId_1572_, v_x_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(lean_object* v_00_u03b2_1583_, lean_object* v_m_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_1584_, v_a_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___boxed(lean_object* v_00_u03b2_1587_, lean_object* v_m_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(v_00_u03b2_1587_, v_m_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_m_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(lean_object* v_00_u03b2_1591_, lean_object* v_a_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1592_, v_x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1595_, lean_object* v_a_1596_, lean_object* v_x_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(v_00_u03b2_1595_, v_a_1596_, v_x_1597_);
lean_dec(v_x_1597_);
lean_dec(v_a_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object* v_fvarId_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v___x_1610_; lean_object* v_funDeclInfoMap_1611_; lean_object* v___x_1612_; 
v___x_1610_ = lean_st_ref_get(v_a_1600_);
v_funDeclInfoMap_1611_ = lean_ctor_get(v___x_1610_, 3);
lean_inc_ref(v_funDeclInfoMap_1611_);
lean_dec(v___x_1610_);
v___x_1612_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_1611_, v_fvarId_1599_);
lean_dec_ref(v_funDeclInfoMap_1611_);
if (lean_obj_tag(v___x_1612_) == 1)
{
lean_object* v_val_1613_; uint8_t v___x_1614_; 
v_val_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_val_1613_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1614_ = lean_unbox(v_val_1613_);
lean_dec(v_val_1613_);
switch(v___x_1614_)
{
case 0:
{
goto v___jp_1606_;
}
case 2:
{
goto v___jp_1606_;
}
default: 
{
goto v___jp_1602_;
}
}
}
else
{
lean_dec(v___x_1612_);
goto v___jp_1602_;
}
v___jp_1602_:
{
uint8_t v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1603_ = 0;
v___x_1604_ = lean_box(v___x_1603_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
v___jp_1606_:
{
uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = 1;
v___x_1608_ = lean_box(v___x_1607_);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg___boxed(lean_object* v_fvarId_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1615_, v_a_1616_);
lean_dec(v_a_1616_);
lean_dec(v_fvarId_1615_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object* v_fvarId_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1619_, v_a_1621_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object* v_fvarId_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(v_fvarId_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_fvarId_1629_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg(lean_object* v_code_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_1640_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1654_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1654_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1654_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v_smallThreshold_1647_; uint8_t v___x_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v_smallThreshold_1647_ = lean_ctor_get(v_a_1643_, 0);
lean_inc(v_smallThreshold_1647_);
lean_dec(v_a_1643_);
v___x_1648_ = 0;
v___x_1649_ = l_Lean_Compiler_LCNF_Code_sizeLe(v___x_1648_, v_code_1639_, v_smallThreshold_1647_);
lean_dec(v_smallThreshold_1647_);
v___x_1650_ = lean_box(v___x_1649_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1650_);
v___x_1652_ = v___x_1645_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
v_a_1655_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1642_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1642_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg___boxed(lean_object* v_code_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1663_, v_a_1664_);
lean_dec_ref(v_a_1664_);
lean_dec_ref(v_code_1663_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object* v_code_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1667_, v_a_1671_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object* v_code_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_Compiler_LCNF_Simp_isSmall(v_code_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec_ref(v_code_1677_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object* v_decl_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_fvarId_1691_; lean_object* v_value_1692_; lean_object* v___x_1693_; lean_object* v_a_1694_; uint8_t v___x_1695_; 
v_fvarId_1691_ = lean_ctor_get(v_decl_1687_, 0);
v_value_1692_ = lean_ctor_get(v_decl_1687_, 4);
v___x_1693_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1691_, v_a_1688_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
v___x_1695_ = lean_unbox(v_a_1694_);
lean_dec(v_a_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; 
lean_dec_ref(v___x_1693_);
v___x_1696_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_value_1692_, v_a_1689_);
return v___x_1696_;
}
else
{
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg___boxed(lean_object* v_decl_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1697_, v_a_1698_, v_a_1699_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec_ref(v_decl_1697_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object* v_decl_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1702_, v_a_1704_, v_a_1706_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object* v_decl_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(v_decl_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec_ref(v_decl_1712_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(lean_object* v_a_1722_, lean_object* v_b_1723_, lean_object* v_x_1724_){
_start:
{
if (lean_obj_tag(v_x_1724_) == 0)
{
lean_dec(v_b_1723_);
lean_dec(v_a_1722_);
return v_x_1724_;
}
else
{
lean_object* v_key_1725_; lean_object* v_value_1726_; lean_object* v_tail_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1739_; 
v_key_1725_ = lean_ctor_get(v_x_1724_, 0);
v_value_1726_ = lean_ctor_get(v_x_1724_, 1);
v_tail_1727_ = lean_ctor_get(v_x_1724_, 2);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_x_1724_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1729_ = v_x_1724_;
v_isShared_1730_ = v_isSharedCheck_1739_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_tail_1727_);
lean_inc(v_value_1726_);
lean_inc(v_key_1725_);
lean_dec(v_x_1724_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1739_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
uint8_t v___x_1731_; 
v___x_1731_ = l_Lean_instBEqFVarId_beq(v_key_1725_, v_a_1722_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1732_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_1722_, v_b_1723_, v_tail_1727_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 2, v___x_1732_);
v___x_1734_ = v___x_1729_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_key_1725_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_value_1726_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
else
{
lean_object* v___x_1737_; 
lean_dec(v_value_1726_);
lean_dec(v_key_1725_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 1, v_b_1723_);
lean_ctor_set(v___x_1729_, 0, v_a_1722_);
v___x_1737_ = v___x_1729_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1722_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_b_1723_);
lean_ctor_set(v_reuseFailAlloc_1738_, 2, v_tail_1727_);
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
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(lean_object* v_a_1740_, lean_object* v_x_1741_){
_start:
{
if (lean_obj_tag(v_x_1741_) == 0)
{
uint8_t v___x_1742_; 
v___x_1742_ = 0;
return v___x_1742_;
}
else
{
lean_object* v_key_1743_; lean_object* v_tail_1744_; uint8_t v___x_1745_; 
v_key_1743_ = lean_ctor_get(v_x_1741_, 0);
v_tail_1744_ = lean_ctor_get(v_x_1741_, 2);
v___x_1745_ = l_Lean_instBEqFVarId_beq(v_key_1743_, v_a_1740_);
if (v___x_1745_ == 0)
{
v_x_1741_ = v_tail_1744_;
goto _start;
}
else
{
return v___x_1745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg___boxed(lean_object* v_a_1747_, lean_object* v_x_1748_){
_start:
{
uint8_t v_res_1749_; lean_object* v_r_1750_; 
v_res_1749_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1747_, v_x_1748_);
lean_dec(v_x_1748_);
lean_dec(v_a_1747_);
v_r_1750_ = lean_box(v_res_1749_);
return v_r_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
if (lean_obj_tag(v_x_1752_) == 0)
{
return v_x_1751_;
}
else
{
lean_object* v_key_1753_; lean_object* v_value_1754_; lean_object* v_tail_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1778_; 
v_key_1753_ = lean_ctor_get(v_x_1752_, 0);
v_value_1754_ = lean_ctor_get(v_x_1752_, 1);
v_tail_1755_ = lean_ctor_get(v_x_1752_, 2);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_x_1752_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1757_ = v_x_1752_;
v_isShared_1758_ = v_isSharedCheck_1778_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_tail_1755_);
lean_inc(v_value_1754_);
lean_inc(v_key_1753_);
lean_dec(v_x_1752_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1778_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; uint64_t v___x_1760_; uint64_t v___x_1761_; uint64_t v___x_1762_; uint64_t v_fold_1763_; uint64_t v___x_1764_; uint64_t v___x_1765_; uint64_t v___x_1766_; size_t v___x_1767_; size_t v___x_1768_; size_t v___x_1769_; size_t v___x_1770_; size_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1759_ = lean_array_get_size(v_x_1751_);
v___x_1760_ = l_Lean_instHashableFVarId_hash(v_key_1753_);
v___x_1761_ = 32ULL;
v___x_1762_ = lean_uint64_shift_right(v___x_1760_, v___x_1761_);
v_fold_1763_ = lean_uint64_xor(v___x_1760_, v___x_1762_);
v___x_1764_ = 16ULL;
v___x_1765_ = lean_uint64_shift_right(v_fold_1763_, v___x_1764_);
v___x_1766_ = lean_uint64_xor(v_fold_1763_, v___x_1765_);
v___x_1767_ = lean_uint64_to_usize(v___x_1766_);
v___x_1768_ = lean_usize_of_nat(v___x_1759_);
v___x_1769_ = ((size_t)1ULL);
v___x_1770_ = lean_usize_sub(v___x_1768_, v___x_1769_);
v___x_1771_ = lean_usize_land(v___x_1767_, v___x_1770_);
v___x_1772_ = lean_array_uget_borrowed(v_x_1751_, v___x_1771_);
lean_inc(v___x_1772_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 2, v___x_1772_);
v___x_1774_ = v___x_1757_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_key_1753_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_value_1754_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_array_uset(v_x_1751_, v___x_1771_, v___x_1774_);
v_x_1751_ = v___x_1775_;
v_x_1752_ = v_tail_1755_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1779_, lean_object* v_source_1780_, lean_object* v_target_1781_){
_start:
{
lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1782_ = lean_array_get_size(v_source_1780_);
v___x_1783_ = lean_nat_dec_lt(v_i_1779_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_dec_ref(v_source_1780_);
lean_dec(v_i_1779_);
return v_target_1781_;
}
else
{
lean_object* v_es_1784_; lean_object* v___x_1785_; lean_object* v_source_1786_; lean_object* v_target_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_es_1784_ = lean_array_fget(v_source_1780_, v_i_1779_);
v___x_1785_ = lean_box(0);
v_source_1786_ = lean_array_fset(v_source_1780_, v_i_1779_, v___x_1785_);
v_target_1787_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(v_target_1781_, v_es_1784_);
v___x_1788_ = lean_unsigned_to_nat(1u);
v___x_1789_ = lean_nat_add(v_i_1779_, v___x_1788_);
lean_dec(v_i_1779_);
v_i_1779_ = v___x_1789_;
v_source_1780_ = v_source_1786_;
v_target_1781_ = v_target_1787_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(lean_object* v_data_1791_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v_nbuckets_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1792_ = lean_array_get_size(v_data_1791_);
v___x_1793_ = lean_unsigned_to_nat(2u);
v_nbuckets_1794_ = lean_nat_mul(v___x_1792_, v___x_1793_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_box(0);
v___x_1797_ = lean_mk_array(v_nbuckets_1794_, v___x_1796_);
v___x_1798_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(v___x_1795_, v_data_1791_, v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(lean_object* v_m_1799_, lean_object* v_a_1800_, lean_object* v_b_1801_){
_start:
{
lean_object* v_size_1802_; lean_object* v_buckets_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1846_; 
v_size_1802_ = lean_ctor_get(v_m_1799_, 0);
v_buckets_1803_ = lean_ctor_get(v_m_1799_, 1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_m_1799_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1805_ = v_m_1799_;
v_isShared_1806_ = v_isSharedCheck_1846_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_buckets_1803_);
lean_inc(v_size_1802_);
lean_dec(v_m_1799_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1846_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; uint64_t v___x_1808_; uint64_t v___x_1809_; uint64_t v___x_1810_; uint64_t v_fold_1811_; uint64_t v___x_1812_; uint64_t v___x_1813_; uint64_t v___x_1814_; size_t v___x_1815_; size_t v___x_1816_; size_t v___x_1817_; size_t v___x_1818_; size_t v___x_1819_; lean_object* v_bkt_1820_; uint8_t v___x_1821_; 
v___x_1807_ = lean_array_get_size(v_buckets_1803_);
v___x_1808_ = l_Lean_instHashableFVarId_hash(v_a_1800_);
v___x_1809_ = 32ULL;
v___x_1810_ = lean_uint64_shift_right(v___x_1808_, v___x_1809_);
v_fold_1811_ = lean_uint64_xor(v___x_1808_, v___x_1810_);
v___x_1812_ = 16ULL;
v___x_1813_ = lean_uint64_shift_right(v_fold_1811_, v___x_1812_);
v___x_1814_ = lean_uint64_xor(v_fold_1811_, v___x_1813_);
v___x_1815_ = lean_uint64_to_usize(v___x_1814_);
v___x_1816_ = lean_usize_of_nat(v___x_1807_);
v___x_1817_ = ((size_t)1ULL);
v___x_1818_ = lean_usize_sub(v___x_1816_, v___x_1817_);
v___x_1819_ = lean_usize_land(v___x_1815_, v___x_1818_);
v_bkt_1820_ = lean_array_uget_borrowed(v_buckets_1803_, v___x_1819_);
v___x_1821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1800_, v_bkt_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v_size_x27_1823_; lean_object* v___x_1824_; lean_object* v_buckets_x27_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1822_ = lean_unsigned_to_nat(1u);
v_size_x27_1823_ = lean_nat_add(v_size_1802_, v___x_1822_);
lean_dec(v_size_1802_);
lean_inc(v_bkt_1820_);
v___x_1824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1824_, 0, v_a_1800_);
lean_ctor_set(v___x_1824_, 1, v_b_1801_);
lean_ctor_set(v___x_1824_, 2, v_bkt_1820_);
v_buckets_x27_1825_ = lean_array_uset(v_buckets_1803_, v___x_1819_, v___x_1824_);
v___x_1826_ = lean_unsigned_to_nat(4u);
v___x_1827_ = lean_nat_mul(v_size_x27_1823_, v___x_1826_);
v___x_1828_ = lean_unsigned_to_nat(3u);
v___x_1829_ = lean_nat_div(v___x_1827_, v___x_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_array_get_size(v_buckets_x27_1825_);
v___x_1831_ = lean_nat_dec_le(v___x_1829_, v___x_1830_);
lean_dec(v___x_1829_);
if (v___x_1831_ == 0)
{
lean_object* v_val_1832_; lean_object* v___x_1834_; 
v_val_1832_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(v_buckets_x27_1825_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v_val_1832_);
lean_ctor_set(v___x_1805_, 0, v_size_x27_1823_);
v___x_1834_ = v___x_1805_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_size_x27_1823_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_val_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
else
{
lean_object* v___x_1837_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v_buckets_x27_1825_);
lean_ctor_set(v___x_1805_, 0, v_size_x27_1823_);
v___x_1837_ = v___x_1805_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_size_x27_1823_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_buckets_x27_1825_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
lean_object* v___x_1839_; lean_object* v_buckets_x27_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
lean_inc(v_bkt_1820_);
v___x_1839_ = lean_box(0);
v_buckets_x27_1840_ = lean_array_uset(v_buckets_1803_, v___x_1819_, v___x_1839_);
v___x_1841_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_1800_, v_b_1801_, v_bkt_1820_);
v___x_1842_ = lean_array_uset(v_buckets_x27_1840_, v___x_1819_, v___x_1841_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1842_);
v___x_1844_ = v___x_1805_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_size_1802_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(lean_object* v_as_1847_, size_t v_sz_1848_, size_t v_i_1849_, lean_object* v_b_1850_){
_start:
{
uint8_t v___x_1852_; 
v___x_1852_ = lean_usize_dec_lt(v_i_1849_, v_sz_1848_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_b_1850_);
return v___x_1853_;
}
else
{
lean_object* v_snd_1854_; lean_object* v_fst_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1889_; 
v_snd_1854_ = lean_ctor_get(v_b_1850_, 1);
v_fst_1855_ = lean_ctor_get(v_b_1850_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_b_1850_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1857_ = v_b_1850_;
v_isShared_1858_ = v_isSharedCheck_1889_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_snd_1854_);
lean_inc(v_fst_1855_);
lean_dec(v_b_1850_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1889_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v_array_1859_; lean_object* v_start_1860_; lean_object* v_stop_1861_; uint8_t v___x_1862_; 
v_array_1859_ = lean_ctor_get(v_snd_1854_, 0);
v_start_1860_ = lean_ctor_get(v_snd_1854_, 1);
v_stop_1861_ = lean_ctor_get(v_snd_1854_, 2);
v___x_1862_ = lean_nat_dec_lt(v_start_1860_, v_stop_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1864_; 
if (v_isShared_1858_ == 0)
{
v___x_1864_ = v___x_1857_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_fst_1855_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_snd_1854_);
v___x_1864_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
return v___x_1865_;
}
}
else
{
lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1885_; 
lean_inc(v_stop_1861_);
lean_inc(v_start_1860_);
lean_inc_ref(v_array_1859_);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_snd_1854_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; lean_object* v_unused_1887_; lean_object* v_unused_1888_; 
v_unused_1886_ = lean_ctor_get(v_snd_1854_, 2);
lean_dec(v_unused_1886_);
v_unused_1887_ = lean_ctor_get(v_snd_1854_, 1);
lean_dec(v_unused_1887_);
v_unused_1888_ = lean_ctor_get(v_snd_1854_, 0);
lean_dec(v_unused_1888_);
v___x_1868_ = v_snd_1854_;
v_isShared_1869_ = v_isSharedCheck_1885_;
goto v_resetjp_1867_;
}
else
{
lean_dec(v_snd_1854_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1885_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v_a_1870_; lean_object* v_fvarId_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
v_a_1870_ = lean_array_uget_borrowed(v_as_1847_, v_i_1849_);
v_fvarId_1871_ = lean_ctor_get(v_a_1870_, 0);
v___x_1872_ = lean_array_fget(v_array_1859_, v_start_1860_);
v___x_1873_ = lean_unsigned_to_nat(1u);
v___x_1874_ = lean_nat_add(v_start_1860_, v___x_1873_);
lean_dec(v_start_1860_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___x_1874_);
v___x_1876_ = v___x_1868_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_array_1859_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_stop_1861_);
v___x_1876_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
lean_inc(v_fvarId_1871_);
v___x_1877_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_fst_1855_, v_fvarId_1871_, v___x_1872_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 1, v___x_1876_);
lean_ctor_set(v___x_1857_, 0, v___x_1877_);
v___x_1879_ = v___x_1857_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1876_);
v___x_1879_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
size_t v___x_1880_; size_t v___x_1881_; 
v___x_1880_ = ((size_t)1ULL);
v___x_1881_ = lean_usize_add(v_i_1849_, v___x_1880_);
v_i_1849_ = v___x_1881_;
v_b_1850_ = v___x_1879_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg___boxed(lean_object* v_as_1890_, lean_object* v_sz_1891_, lean_object* v_i_1892_, lean_object* v_b_1893_, lean_object* v___y_1894_){
_start:
{
size_t v_sz_boxed_1895_; size_t v_i_boxed_1896_; lean_object* v_res_1897_; 
v_sz_boxed_1895_ = lean_unbox_usize(v_sz_1891_);
lean_dec(v_sz_1891_);
v_i_boxed_1896_ = lean_unbox_usize(v_i_1892_);
lean_dec(v_i_1892_);
v_res_1897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_1890_, v_sz_boxed_1895_, v_i_boxed_1896_, v_b_1893_);
lean_dec_ref(v_as_1890_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object* v_params_1898_, lean_object* v_code_1899_, lean_object* v_args_1900_, uint8_t v_mustInline_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___x_1910_; lean_object* v_subst_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; size_t v_sz_1915_; size_t v___x_1916_; lean_object* v___x_1917_; 
v___x_1910_ = lean_unsigned_to_nat(0u);
v_subst_1911_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1);
v___x_1912_ = lean_array_get_size(v_args_1900_);
v___x_1913_ = l_Array_toSubarray___redArg(v_args_1900_, v___x_1910_, v___x_1912_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v_subst_1911_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v_sz_1915_ = lean_array_size(v_params_1898_);
v___x_1916_ = ((size_t)0ULL);
v___x_1917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_params_1898_, v_sz_1915_, v___x_1916_, v___x_1914_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v_fst_1919_; uint8_t v___x_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v_fst_1919_ = lean_ctor_get(v_a_1918_, 0);
lean_inc(v_fst_1919_);
lean_dec(v_a_1918_);
v___x_1920_ = 0;
v___x_1921_ = 0;
v___x_1922_ = l_Lean_Compiler_LCNF_Code_internalize(v___x_1920_, v_code_1899_, v_fst_1919_, v___x_1921_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1924_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc_n(v_a_1923_, 2);
lean_dec_ref_known(v___x_1922_, 1);
v___x_1924_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_a_1923_, v_mustInline_1901_, v_a_1903_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v___x_1924_, 0);
lean_dec(v_unused_1932_);
v___x_1926_ = v___x_1924_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_dec(v___x_1924_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v_a_1923_);
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1923_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_a_1923_);
v_a_1933_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1924_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1924_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
return v___x_1922_;
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec_ref(v_code_1899_);
v_a_1941_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1917_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1917_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object* v_params_1949_, lean_object* v_code_1950_, lean_object* v_args_1951_, lean_object* v_mustInline_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
uint8_t v_mustInline_boxed_1961_; lean_object* v_res_1962_; 
v_mustInline_boxed_1961_ = lean_unbox(v_mustInline_1952_);
v_res_1962_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1949_, v_code_1950_, v_args_1951_, v_mustInline_boxed_1961_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec_ref(v_params_1949_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0(lean_object* v_00_u03b2_1963_, lean_object* v_m_1964_, lean_object* v_a_1965_, lean_object* v_b_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_m_1964_, v_a_1965_, v_b_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(lean_object* v_as_1968_, size_t v_sz_1969_, size_t v_i_1970_, lean_object* v_b_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_1968_, v_sz_1969_, v_i_1970_, v_b_1971_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___boxed(lean_object* v_as_1981_, lean_object* v_sz_1982_, lean_object* v_i_1983_, lean_object* v_b_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
size_t v_sz_boxed_1993_; size_t v_i_boxed_1994_; lean_object* v_res_1995_; 
v_sz_boxed_1993_ = lean_unbox_usize(v_sz_1982_);
lean_dec(v_sz_1982_);
v_i_boxed_1994_ = lean_unbox_usize(v_i_1983_);
lean_dec(v_i_1983_);
v_res_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(v_as_1981_, v_sz_boxed_1993_, v_i_boxed_1994_, v_b_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec_ref(v_as_1981_);
return v_res_1995_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(lean_object* v_00_u03b2_1996_, lean_object* v_a_1997_, lean_object* v_x_1998_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1997_, v_x_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2000_, lean_object* v_a_2001_, lean_object* v_x_2002_){
_start:
{
uint8_t v_res_2003_; lean_object* v_r_2004_; 
v_res_2003_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(v_00_u03b2_2000_, v_a_2001_, v_x_2002_);
lean_dec(v_x_2002_);
lean_dec(v_a_2001_);
v_r_2004_ = lean_box(v_res_2003_);
return v_r_2004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1(lean_object* v_00_u03b2_2005_, lean_object* v_data_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(v_data_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2(lean_object* v_00_u03b2_2008_, lean_object* v_a_2009_, lean_object* v_b_2010_, lean_object* v_x_2011_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_2009_, v_b_2010_, v_x_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2013_, lean_object* v_i_2014_, lean_object* v_source_2015_, lean_object* v_target_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(v_i_2014_, v_source_2015_, v_target_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2019_, v_x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object* v_decl_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
uint8_t v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = 0;
v___x_2027_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2026_, v_decl_2022_, v_a_2024_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v___x_2028_; 
lean_dec_ref_known(v___x_2027_, 1);
v___x_2028_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2023_);
return v___x_2028_;
}
else
{
return v___x_2027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg___boxed(lean_object* v_decl_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2029_, v_a_2030_, v_a_2031_);
lean_dec(v_a_2031_);
lean_dec(v_a_2030_);
lean_dec_ref(v_decl_2029_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object* v_decl_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2034_, v_a_2036_, v_a_2039_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object* v_decl_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(v_decl_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
lean_dec_ref(v_decl_2044_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object* v_decl_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
uint8_t v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = 0;
v___x_2059_ = 1;
v___x_2060_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_2058_, v_decl_2054_, v___x_2059_, v_a_2056_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v___x_2061_; 
lean_dec_ref_known(v___x_2060_, 1);
v___x_2061_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2055_);
return v___x_2061_;
}
else
{
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg___boxed(lean_object* v_decl_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2062_, v_a_2063_, v_a_2064_);
lean_dec(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_decl_2062_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object* v_decl_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2067_, v_a_2069_, v_a_2072_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object* v_decl_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(v_decl_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec_ref(v_decl_2077_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object* v_fvarId_2087_, lean_object* v_fvarId_x27_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v___x_2095_; lean_object* v_subst_2096_; lean_object* v_used_2097_; lean_object* v_binderRenaming_2098_; lean_object* v_funDeclInfoMap_2099_; uint8_t v_simplified_2100_; lean_object* v_visited_2101_; lean_object* v_inline_2102_; lean_object* v_inlineLocal_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2173_; 
v___x_2095_ = lean_st_ref_take(v_a_2089_);
v_subst_2096_ = lean_ctor_get(v___x_2095_, 0);
v_used_2097_ = lean_ctor_get(v___x_2095_, 1);
v_binderRenaming_2098_ = lean_ctor_get(v___x_2095_, 2);
v_funDeclInfoMap_2099_ = lean_ctor_get(v___x_2095_, 3);
v_simplified_2100_ = lean_ctor_get_uint8(v___x_2095_, sizeof(void*)*7);
v_visited_2101_ = lean_ctor_get(v___x_2095_, 4);
v_inline_2102_ = lean_ctor_get(v___x_2095_, 5);
v_inlineLocal_2103_ = lean_ctor_get(v___x_2095_, 6);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2105_ = v___x_2095_;
v_isShared_2106_ = v_isSharedCheck_2173_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_inlineLocal_2103_);
lean_inc(v_inline_2102_);
lean_inc(v_visited_2101_);
lean_inc(v_funDeclInfoMap_2099_);
lean_inc(v_binderRenaming_2098_);
lean_inc(v_used_2097_);
lean_inc(v_subst_2096_);
lean_dec(v___x_2095_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2173_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2110_; 
lean_inc(v_fvarId_x27_2088_);
v___x_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2107_, 0, v_fvarId_x27_2088_);
lean_inc(v_fvarId_2087_);
v___x_2108_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_subst_2096_, v_fvarId_2087_, v___x_2107_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2108_);
v___x_2110_ = v___x_2105_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_used_2097_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_binderRenaming_2098_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_funDeclInfoMap_2099_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_visited_2101_);
lean_ctor_set(v_reuseFailAlloc_2172_, 5, v_inline_2102_);
lean_ctor_set(v_reuseFailAlloc_2172_, 6, v_inlineLocal_2103_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*7, v_simplified_2100_);
v___x_2110_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_st_ref_set(v_a_2089_, v___x_2110_);
v___x_2112_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_2087_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2163_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2163_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2163_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
uint8_t v___x_2117_; 
v___x_2117_ = l_Lean_Name_isInternal(v_a_2113_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
lean_del_object(v___x_2115_);
lean_inc(v_fvarId_x27_2088_);
v___x_2118_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_x27_2088_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2150_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2150_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2150_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
uint8_t v___x_2123_; 
v___x_2123_ = l_Lean_Name_isInternal(v_a_2119_);
lean_dec(v_a_2119_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
lean_dec(v_a_2113_);
lean_dec(v_fvarId_x27_2088_);
v___x_2124_ = lean_box(0);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2124_);
v___x_2126_ = v___x_2121_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
else
{
lean_object* v___x_2128_; lean_object* v_subst_2129_; lean_object* v_used_2130_; lean_object* v_binderRenaming_2131_; lean_object* v_funDeclInfoMap_2132_; uint8_t v_simplified_2133_; lean_object* v_visited_2134_; lean_object* v_inline_2135_; lean_object* v_inlineLocal_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2149_; 
v___x_2128_ = lean_st_ref_take(v_a_2089_);
v_subst_2129_ = lean_ctor_get(v___x_2128_, 0);
v_used_2130_ = lean_ctor_get(v___x_2128_, 1);
v_binderRenaming_2131_ = lean_ctor_get(v___x_2128_, 2);
v_funDeclInfoMap_2132_ = lean_ctor_get(v___x_2128_, 3);
v_simplified_2133_ = lean_ctor_get_uint8(v___x_2128_, sizeof(void*)*7);
v_visited_2134_ = lean_ctor_get(v___x_2128_, 4);
v_inline_2135_ = lean_ctor_get(v___x_2128_, 5);
v_inlineLocal_2136_ = lean_ctor_get(v___x_2128_, 6);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2138_ = v___x_2128_;
v_isShared_2139_ = v_isSharedCheck_2149_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_inlineLocal_2136_);
lean_inc(v_inline_2135_);
lean_inc(v_visited_2134_);
lean_inc(v_funDeclInfoMap_2132_);
lean_inc(v_binderRenaming_2131_);
lean_inc(v_used_2130_);
lean_inc(v_subst_2129_);
lean_dec(v___x_2128_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2149_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_x27_2088_, v_a_2113_, v_binderRenaming_2131_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 2, v___x_2140_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_subst_2129_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_used_2130_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2148_, 3, v_funDeclInfoMap_2132_);
lean_ctor_set(v_reuseFailAlloc_2148_, 4, v_visited_2134_);
lean_ctor_set(v_reuseFailAlloc_2148_, 5, v_inline_2135_);
lean_ctor_set(v_reuseFailAlloc_2148_, 6, v_inlineLocal_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2148_, sizeof(void*)*7, v_simplified_2133_);
v___x_2142_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2143_ = lean_st_ref_set(v_a_2089_, v___x_2142_);
v___x_2144_ = lean_box(0);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2144_);
v___x_2146_ = v___x_2121_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_a_2113_);
lean_dec(v_fvarId_x27_2088_);
v_a_2151_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2118_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2118_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_dec(v_a_2113_);
lean_dec(v_fvarId_x27_2088_);
v___x_2159_ = lean_box(0);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2159_);
v___x_2161_ = v___x_2115_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_fvarId_x27_2088_);
v_a_2164_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2112_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2112_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg___boxed(lean_object* v_fvarId_2174_, lean_object* v_fvarId_x27_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2174_, v_fvarId_x27_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object* v_fvarId_2183_, lean_object* v_fvarId_x27_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2183_, v_fvarId_x27_2184_, v_a_2186_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___boxed(lean_object* v_fvarId_2194_, lean_object* v_fvarId_x27_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst(v_fvarId_2194_, v_fvarId_x27_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
return v_res_2204_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
