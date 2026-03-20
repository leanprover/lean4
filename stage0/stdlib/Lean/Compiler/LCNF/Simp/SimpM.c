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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_sizeLe(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_35_);
v___x_37_ = lean_apply_9(v___y_26_, v_a_36_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, lean_box(0));
return v___x_37_;
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
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
return v_res_58_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0, &l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0);
v___x_61_ = l_ReaderT_instMonad___redArg(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM(void){
_start:
{
lean_object* v___x_68_; lean_object* v_toApplicative_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_157_; 
v___x_68_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1, &l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1);
v_toApplicative_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v___x_68_, 1);
lean_dec(v_unused_158_);
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_157_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_toApplicative_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_157_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_toFunctor_73_; lean_object* v_toSeq_74_; lean_object* v_toSeqLeft_75_; lean_object* v_toSeqRight_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_155_; 
v_toFunctor_73_ = lean_ctor_get(v_toApplicative_69_, 0);
v_toSeq_74_ = lean_ctor_get(v_toApplicative_69_, 2);
v_toSeqLeft_75_ = lean_ctor_get(v_toApplicative_69_, 3);
v_toSeqRight_76_ = lean_ctor_get(v_toApplicative_69_, 4);
v_isSharedCheck_155_ = !lean_is_exclusive(v_toApplicative_69_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; 
v_unused_156_ = lean_ctor_get(v_toApplicative_69_, 1);
lean_dec(v_unused_156_);
v___x_78_ = v_toApplicative_69_;
v_isShared_79_ = v_isSharedCheck_155_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_toSeqRight_76_);
lean_inc(v_toSeqLeft_75_);
lean_inc(v_toSeq_74_);
lean_inc(v_toFunctor_73_);
lean_dec(v_toApplicative_69_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_155_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___f_85_; lean_object* v___f_86_; lean_object* v___f_87_; lean_object* v___x_89_; 
v___f_80_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2));
v___f_81_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3));
lean_inc_ref(v_toFunctor_73_);
v___f_82_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_82_, 0, v_toFunctor_73_);
v___f_83_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_83_, 0, v_toFunctor_73_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v___f_82_);
lean_ctor_set(v___x_84_, 1, v___f_83_);
v___f_85_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_85_, 0, v_toSeqRight_76_);
v___f_86_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_86_, 0, v_toSeqLeft_75_);
v___f_87_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_87_, 0, v_toSeq_74_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 4, v___f_85_);
lean_ctor_set(v___x_78_, 3, v___f_86_);
lean_ctor_set(v___x_78_, 2, v___f_87_);
lean_ctor_set(v___x_78_, 1, v___f_80_);
lean_ctor_set(v___x_78_, 0, v___x_84_);
v___x_89_ = v___x_78_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___f_80_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v___f_87_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v___f_86_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v___f_85_);
v___x_89_ = v_reuseFailAlloc_154_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_91_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v___f_81_);
lean_ctor_set(v___x_71_, 0, v___x_89_);
v___x_91_ = v___x_71_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___f_81_);
v___x_91_ = v_reuseFailAlloc_153_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v_toApplicative_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_151_; 
v___x_92_ = l_ReaderT_instMonad___redArg(v___x_91_);
v_toApplicative_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; 
v_unused_152_ = lean_ctor_get(v___x_92_, 1);
lean_dec(v_unused_152_);
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_151_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_toApplicative_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_151_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v_toFunctor_97_; lean_object* v_toSeq_98_; lean_object* v_toSeqLeft_99_; lean_object* v_toSeqRight_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_149_; 
v_toFunctor_97_ = lean_ctor_get(v_toApplicative_93_, 0);
v_toSeq_98_ = lean_ctor_get(v_toApplicative_93_, 2);
v_toSeqLeft_99_ = lean_ctor_get(v_toApplicative_93_, 3);
v_toSeqRight_100_ = lean_ctor_get(v_toApplicative_93_, 4);
v_isSharedCheck_149_ = !lean_is_exclusive(v_toApplicative_93_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; 
v_unused_150_ = lean_ctor_get(v_toApplicative_93_, 1);
lean_dec(v_unused_150_);
v___x_102_ = v_toApplicative_93_;
v_isShared_103_ = v_isSharedCheck_149_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_toSeqRight_100_);
lean_inc(v_toSeqLeft_99_);
lean_inc(v_toSeq_98_);
lean_inc(v_toFunctor_97_);
lean_dec(v_toApplicative_93_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_149_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___f_104_; lean_object* v___f_105_; lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___x_108_; lean_object* v___f_109_; lean_object* v___f_110_; lean_object* v___f_111_; lean_object* v___x_113_; 
v___f_104_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4));
v___f_105_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5));
lean_inc_ref(v_toFunctor_97_);
v___f_106_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_106_, 0, v_toFunctor_97_);
v___f_107_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_107_, 0, v_toFunctor_97_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v___f_106_);
lean_ctor_set(v___x_108_, 1, v___f_107_);
v___f_109_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_109_, 0, v_toSeqRight_100_);
v___f_110_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_110_, 0, v_toSeqLeft_99_);
v___f_111_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_111_, 0, v_toSeq_98_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 4, v___f_109_);
lean_ctor_set(v___x_102_, 3, v___f_110_);
lean_ctor_set(v___x_102_, 2, v___f_111_);
lean_ctor_set(v___x_102_, 1, v___f_104_);
lean_ctor_set(v___x_102_, 0, v___x_108_);
v___x_113_ = v___x_102_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___f_104_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v___f_111_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v___f_110_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v___f_109_);
v___x_113_ = v_reuseFailAlloc_148_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_115_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 1, v___f_105_);
lean_ctor_set(v___x_95_, 0, v___x_113_);
v___x_115_ = v___x_95_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___f_105_);
v___x_115_ = v_reuseFailAlloc_147_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_toApplicative_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_145_; 
v___x_116_ = l_ReaderT_instMonad___redArg(v___x_115_);
v___x_117_ = l_ReaderT_instMonad___redArg(v___x_116_);
v_toApplicative_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v___x_117_, 1);
lean_dec(v_unused_146_);
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_145_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_toApplicative_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_145_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v_toFunctor_122_; lean_object* v_toSeq_123_; lean_object* v_toSeqLeft_124_; lean_object* v_toSeqRight_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_143_; 
v_toFunctor_122_ = lean_ctor_get(v_toApplicative_118_, 0);
v_toSeq_123_ = lean_ctor_get(v_toApplicative_118_, 2);
v_toSeqLeft_124_ = lean_ctor_get(v_toApplicative_118_, 3);
v_toSeqRight_125_ = lean_ctor_get(v_toApplicative_118_, 4);
v_isSharedCheck_143_ = !lean_is_exclusive(v_toApplicative_118_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v_toApplicative_118_, 1);
lean_dec(v_unused_144_);
v___x_127_ = v_toApplicative_118_;
v_isShared_128_ = v_isSharedCheck_143_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_toSeqRight_125_);
lean_inc(v_toSeqLeft_124_);
lean_inc(v_toSeq_123_);
lean_inc(v_toFunctor_122_);
lean_dec(v_toApplicative_118_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_143_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___f_129_; lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___x_133_; lean_object* v___f_134_; lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___x_138_; 
v___f_129_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6));
v___f_130_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7));
lean_inc_ref(v_toFunctor_122_);
v___f_131_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_131_, 0, v_toFunctor_122_);
v___f_132_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_132_, 0, v_toFunctor_122_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___f_131_);
lean_ctor_set(v___x_133_, 1, v___f_132_);
v___f_134_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_134_, 0, v_toSeqRight_125_);
v___f_135_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_135_, 0, v_toSeqLeft_124_);
v___f_136_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_136_, 0, v_toSeq_123_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v___f_134_);
lean_ctor_set(v___x_127_, 3, v___f_135_);
lean_ctor_set(v___x_127_, 2, v___f_136_);
lean_ctor_set(v___x_127_, 1, v___f_129_);
lean_ctor_set(v___x_127_, 0, v___x_133_);
v___x_138_ = v___x_127_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___f_129_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v___f_136_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v___f_135_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v___f_134_);
v___x_138_ = v_reuseFailAlloc_142_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_140_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___f_130_);
lean_ctor_set(v___x_120_, 0, v___x_138_);
v___x_140_ = v___x_120_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___f_130_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0(lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; lean_object* v_subst_168_; lean_object* v___x_169_; 
v___x_167_ = lean_st_ref_get(v___y_160_);
v_subst_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc_ref(v_subst_168_);
lean_dec(v___x_167_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v_subst_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0___boxed(lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0(v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0(lean_object* v_f_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; lean_object* v_subst_191_; lean_object* v_used_192_; lean_object* v_binderRenaming_193_; lean_object* v_funDeclInfoMap_194_; uint8_t v_simplified_195_; lean_object* v_visited_196_; lean_object* v_inline_197_; lean_object* v_inlineLocal_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_209_; 
v___x_190_ = lean_st_ref_take(v___y_183_);
v_subst_191_ = lean_ctor_get(v___x_190_, 0);
v_used_192_ = lean_ctor_get(v___x_190_, 1);
v_binderRenaming_193_ = lean_ctor_get(v___x_190_, 2);
v_funDeclInfoMap_194_ = lean_ctor_get(v___x_190_, 3);
v_simplified_195_ = lean_ctor_get_uint8(v___x_190_, sizeof(void*)*7);
v_visited_196_ = lean_ctor_get(v___x_190_, 4);
v_inline_197_ = lean_ctor_get(v___x_190_, 5);
v_inlineLocal_198_ = lean_ctor_get(v___x_190_, 6);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_209_ == 0)
{
v___x_200_ = v___x_190_;
v_isShared_201_ = v_isSharedCheck_209_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_inlineLocal_198_);
lean_inc(v_inline_197_);
lean_inc(v_visited_196_);
lean_inc(v_funDeclInfoMap_194_);
lean_inc(v_binderRenaming_193_);
lean_inc(v_used_192_);
lean_inc(v_subst_191_);
lean_dec(v___x_190_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_209_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_apply_1(v_f_181_, v_subst_191_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_202_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_used_192_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_binderRenaming_193_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v_funDeclInfoMap_194_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v_visited_196_);
lean_ctor_set(v_reuseFailAlloc_208_, 5, v_inline_197_);
lean_ctor_set(v_reuseFailAlloc_208_, 6, v_inlineLocal_198_);
lean_ctor_set_uint8(v_reuseFailAlloc_208_, sizeof(void*)*7, v_simplified_195_);
v___x_204_ = v_reuseFailAlloc_208_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_st_ref_set(v___y_183_, v___x_204_);
v___x_206_ = lean_box(0);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0___boxed(lean_object* v_f_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0(v_f_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object* v_a_222_){
_start:
{
lean_object* v___x_224_; lean_object* v_subst_225_; lean_object* v_used_226_; lean_object* v_binderRenaming_227_; lean_object* v_funDeclInfoMap_228_; lean_object* v_visited_229_; lean_object* v_inline_230_; lean_object* v_inlineLocal_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_242_; 
v___x_224_ = lean_st_ref_take(v_a_222_);
v_subst_225_ = lean_ctor_get(v___x_224_, 0);
v_used_226_ = lean_ctor_get(v___x_224_, 1);
v_binderRenaming_227_ = lean_ctor_get(v___x_224_, 2);
v_funDeclInfoMap_228_ = lean_ctor_get(v___x_224_, 3);
v_visited_229_ = lean_ctor_get(v___x_224_, 4);
v_inline_230_ = lean_ctor_get(v___x_224_, 5);
v_inlineLocal_231_ = lean_ctor_get(v___x_224_, 6);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_242_ == 0)
{
v___x_233_ = v___x_224_;
v_isShared_234_ = v_isSharedCheck_242_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_inlineLocal_231_);
lean_inc(v_inline_230_);
lean_inc(v_visited_229_);
lean_inc(v_funDeclInfoMap_228_);
lean_inc(v_binderRenaming_227_);
lean_inc(v_used_226_);
lean_inc(v_subst_225_);
lean_dec(v___x_224_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_242_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
uint8_t v___x_235_; lean_object* v___x_237_; 
v___x_235_ = 1;
if (v_isShared_234_ == 0)
{
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_subst_225_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_used_226_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_binderRenaming_227_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_funDeclInfoMap_228_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_visited_229_);
lean_ctor_set(v_reuseFailAlloc_241_, 5, v_inline_230_);
lean_ctor_set(v_reuseFailAlloc_241_, 6, v_inlineLocal_231_);
v___x_237_ = v_reuseFailAlloc_241_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*7, v___x_235_);
v___x_238_ = lean_st_ref_set(v_a_222_, v___x_237_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg___boxed(lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_243_);
lean_dec(v_a_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified(lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_247_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___boxed(lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Compiler_LCNF_Simp_markSimplified(v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object* v_a_264_){
_start:
{
lean_object* v___x_266_; lean_object* v_subst_267_; lean_object* v_used_268_; lean_object* v_binderRenaming_269_; lean_object* v_funDeclInfoMap_270_; uint8_t v_simplified_271_; lean_object* v_visited_272_; lean_object* v_inline_273_; lean_object* v_inlineLocal_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_286_; 
v___x_266_ = lean_st_ref_take(v_a_264_);
v_subst_267_ = lean_ctor_get(v___x_266_, 0);
v_used_268_ = lean_ctor_get(v___x_266_, 1);
v_binderRenaming_269_ = lean_ctor_get(v___x_266_, 2);
v_funDeclInfoMap_270_ = lean_ctor_get(v___x_266_, 3);
v_simplified_271_ = lean_ctor_get_uint8(v___x_266_, sizeof(void*)*7);
v_visited_272_ = lean_ctor_get(v___x_266_, 4);
v_inline_273_ = lean_ctor_get(v___x_266_, 5);
v_inlineLocal_274_ = lean_ctor_get(v___x_266_, 6);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_286_ == 0)
{
v___x_276_ = v___x_266_;
v_isShared_277_ = v_isSharedCheck_286_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_inlineLocal_274_);
lean_inc(v_inline_273_);
lean_inc(v_visited_272_);
lean_inc(v_funDeclInfoMap_270_);
lean_inc(v_binderRenaming_269_);
lean_inc(v_used_268_);
lean_inc(v_subst_267_);
lean_dec(v___x_266_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_286_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_visited_272_, v___x_278_);
lean_dec(v_visited_272_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 4, v___x_279_);
v___x_281_ = v___x_276_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_subst_267_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_used_268_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_binderRenaming_269_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v_funDeclInfoMap_270_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_285_, 5, v_inline_273_);
lean_ctor_set(v_reuseFailAlloc_285_, 6, v_inlineLocal_274_);
lean_ctor_set_uint8(v_reuseFailAlloc_285_, sizeof(void*)*7, v_simplified_271_);
v___x_281_ = v_reuseFailAlloc_285_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_st_ref_set(v_a_264_, v___x_281_);
v___x_283_ = lean_box(0);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg___boxed(lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_287_);
lean_dec(v_a_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited(lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_291_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___boxed(lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Compiler_LCNF_Simp_incVisited(v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___redArg(lean_object* v_a_308_){
_start:
{
lean_object* v___x_310_; lean_object* v_subst_311_; lean_object* v_used_312_; lean_object* v_binderRenaming_313_; lean_object* v_funDeclInfoMap_314_; uint8_t v_simplified_315_; lean_object* v_visited_316_; lean_object* v_inline_317_; lean_object* v_inlineLocal_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_330_; 
v___x_310_ = lean_st_ref_take(v_a_308_);
v_subst_311_ = lean_ctor_get(v___x_310_, 0);
v_used_312_ = lean_ctor_get(v___x_310_, 1);
v_binderRenaming_313_ = lean_ctor_get(v___x_310_, 2);
v_funDeclInfoMap_314_ = lean_ctor_get(v___x_310_, 3);
v_simplified_315_ = lean_ctor_get_uint8(v___x_310_, sizeof(void*)*7);
v_visited_316_ = lean_ctor_get(v___x_310_, 4);
v_inline_317_ = lean_ctor_get(v___x_310_, 5);
v_inlineLocal_318_ = lean_ctor_get(v___x_310_, 6);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_330_ == 0)
{
v___x_320_ = v___x_310_;
v_isShared_321_ = v_isSharedCheck_330_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_inlineLocal_318_);
lean_inc(v_inline_317_);
lean_inc(v_visited_316_);
lean_inc(v_funDeclInfoMap_314_);
lean_inc(v_binderRenaming_313_);
lean_inc(v_used_312_);
lean_inc(v_subst_311_);
lean_dec(v___x_310_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_330_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_inline_317_, v___x_322_);
lean_dec(v_inline_317_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 5, v___x_323_);
v___x_325_ = v___x_320_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_subst_311_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_used_312_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v_binderRenaming_313_);
lean_ctor_set(v_reuseFailAlloc_329_, 3, v_funDeclInfoMap_314_);
lean_ctor_set(v_reuseFailAlloc_329_, 4, v_visited_316_);
lean_ctor_set(v_reuseFailAlloc_329_, 5, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_329_, 6, v_inlineLocal_318_);
lean_ctor_set_uint8(v_reuseFailAlloc_329_, sizeof(void*)*7, v_simplified_315_);
v___x_325_ = v_reuseFailAlloc_329_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_st_ref_set(v_a_308_, v___x_325_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___redArg___boxed(lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Compiler_LCNF_Simp_incInline___redArg(v_a_331_);
lean_dec(v_a_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline(lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Compiler_LCNF_Simp_incInline___redArg(v_a_335_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___boxed(lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Compiler_LCNF_Simp_incInline(v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; lean_object* v_subst_355_; lean_object* v_used_356_; lean_object* v_binderRenaming_357_; lean_object* v_funDeclInfoMap_358_; uint8_t v_simplified_359_; lean_object* v_visited_360_; lean_object* v_inline_361_; lean_object* v_inlineLocal_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_374_; 
v___x_354_ = lean_st_ref_take(v_a_352_);
v_subst_355_ = lean_ctor_get(v___x_354_, 0);
v_used_356_ = lean_ctor_get(v___x_354_, 1);
v_binderRenaming_357_ = lean_ctor_get(v___x_354_, 2);
v_funDeclInfoMap_358_ = lean_ctor_get(v___x_354_, 3);
v_simplified_359_ = lean_ctor_get_uint8(v___x_354_, sizeof(void*)*7);
v_visited_360_ = lean_ctor_get(v___x_354_, 4);
v_inline_361_ = lean_ctor_get(v___x_354_, 5);
v_inlineLocal_362_ = lean_ctor_get(v___x_354_, 6);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_374_ == 0)
{
v___x_364_ = v___x_354_;
v_isShared_365_ = v_isSharedCheck_374_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_inlineLocal_362_);
lean_inc(v_inline_361_);
lean_inc(v_visited_360_);
lean_inc(v_funDeclInfoMap_358_);
lean_inc(v_binderRenaming_357_);
lean_inc(v_used_356_);
lean_inc(v_subst_355_);
lean_dec(v___x_354_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_374_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_nat_add(v_inlineLocal_362_, v___x_366_);
lean_dec(v_inlineLocal_362_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 6, v___x_367_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_subst_355_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_used_356_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_binderRenaming_357_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_funDeclInfoMap_358_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_visited_360_);
lean_ctor_set(v_reuseFailAlloc_373_, 5, v_inline_361_);
lean_ctor_set(v_reuseFailAlloc_373_, 6, v___x_367_);
lean_ctor_set_uint8(v_reuseFailAlloc_373_, sizeof(void*)*7, v_simplified_359_);
v___x_369_ = v_reuseFailAlloc_373_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_st_ref_set(v_a_352_, v___x_369_);
v___x_371_ = lean_box(0);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg___boxed(lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(v_a_375_);
lean_dec(v_a_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal(lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(v_a_379_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___boxed(lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal(v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(lean_object* v_fvarId_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; lean_object* v_subst_400_; lean_object* v_used_401_; lean_object* v_binderRenaming_402_; lean_object* v_funDeclInfoMap_403_; uint8_t v_simplified_404_; lean_object* v_visited_405_; lean_object* v_inline_406_; lean_object* v_inlineLocal_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_418_; 
v___x_399_ = lean_st_ref_take(v_a_397_);
v_subst_400_ = lean_ctor_get(v___x_399_, 0);
v_used_401_ = lean_ctor_get(v___x_399_, 1);
v_binderRenaming_402_ = lean_ctor_get(v___x_399_, 2);
v_funDeclInfoMap_403_ = lean_ctor_get(v___x_399_, 3);
v_simplified_404_ = lean_ctor_get_uint8(v___x_399_, sizeof(void*)*7);
v_visited_405_ = lean_ctor_get(v___x_399_, 4);
v_inline_406_ = lean_ctor_get(v___x_399_, 5);
v_inlineLocal_407_ = lean_ctor_get(v___x_399_, 6);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_418_ == 0)
{
v___x_409_ = v___x_399_;
v_isShared_410_ = v_isSharedCheck_418_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_inlineLocal_407_);
lean_inc(v_inline_406_);
lean_inc(v_visited_405_);
lean_inc(v_funDeclInfoMap_403_);
lean_inc(v_binderRenaming_402_);
lean_inc(v_used_401_);
lean_inc(v_subst_400_);
lean_dec(v___x_399_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_418_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(v_funDeclInfoMap_403_, v_fvarId_396_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 3, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_subst_400_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_used_401_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_binderRenaming_402_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v_visited_405_);
lean_ctor_set(v_reuseFailAlloc_417_, 5, v_inline_406_);
lean_ctor_set(v_reuseFailAlloc_417_, 6, v_inlineLocal_407_);
lean_ctor_set_uint8(v_reuseFailAlloc_417_, sizeof(void*)*7, v_simplified_404_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_st_ref_set(v_a_397_, v___x_413_);
v___x_415_ = lean_box(0);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___redArg___boxed(lean_object* v_fvarId_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_419_, v_a_420_);
lean_dec(v_a_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline(lean_object* v_fvarId_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_423_, v_a_425_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___boxed(lean_object* v_fvarId_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Compiler_LCNF_Simp_addMustInline(v_fvarId_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(lean_object* v_fvarId_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_446_; lean_object* v_subst_447_; lean_object* v_used_448_; lean_object* v_binderRenaming_449_; lean_object* v_funDeclInfoMap_450_; uint8_t v_simplified_451_; lean_object* v_visited_452_; lean_object* v_inline_453_; lean_object* v_inlineLocal_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_465_; 
v___x_446_ = lean_st_ref_take(v_a_444_);
v_subst_447_ = lean_ctor_get(v___x_446_, 0);
v_used_448_ = lean_ctor_get(v___x_446_, 1);
v_binderRenaming_449_ = lean_ctor_get(v___x_446_, 2);
v_funDeclInfoMap_450_ = lean_ctor_get(v___x_446_, 3);
v_simplified_451_ = lean_ctor_get_uint8(v___x_446_, sizeof(void*)*7);
v_visited_452_ = lean_ctor_get(v___x_446_, 4);
v_inline_453_ = lean_ctor_get(v___x_446_, 5);
v_inlineLocal_454_ = lean_ctor_get(v___x_446_, 6);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_465_ == 0)
{
v___x_456_ = v___x_446_;
v_isShared_457_ = v_isSharedCheck_465_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_inlineLocal_454_);
lean_inc(v_inline_453_);
lean_inc(v_visited_452_);
lean_inc(v_funDeclInfoMap_450_);
lean_inc(v_binderRenaming_449_);
lean_inc(v_used_448_);
lean_inc(v_subst_447_);
lean_dec(v___x_446_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_465_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v_funDeclInfoMap_450_, v_fvarId_443_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 3, v___x_458_);
v___x_460_ = v___x_456_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_subst_447_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_used_448_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_binderRenaming_449_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v_visited_452_);
lean_ctor_set(v_reuseFailAlloc_464_, 5, v_inline_453_);
lean_ctor_set(v_reuseFailAlloc_464_, 6, v_inlineLocal_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*7, v_simplified_451_);
v___x_460_ = v_reuseFailAlloc_464_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_st_ref_set(v_a_444_, v___x_460_);
v___x_462_ = lean_box(0);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg___boxed(lean_object* v_fvarId_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(v_fvarId_466_, v_a_467_);
lean_dec(v_a_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc(lean_object* v_fvarId_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(v_fvarId_470_, v_a_472_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___boxed(lean_object* v_fvarId_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Compiler_LCNF_Simp_addFunOcc(v_fvarId_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(lean_object* v_fvarId_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_493_; lean_object* v_subst_494_; lean_object* v_used_495_; lean_object* v_binderRenaming_496_; lean_object* v_funDeclInfoMap_497_; uint8_t v_simplified_498_; lean_object* v_visited_499_; lean_object* v_inline_500_; lean_object* v_inlineLocal_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_512_; 
v___x_493_ = lean_st_ref_take(v_a_491_);
v_subst_494_ = lean_ctor_get(v___x_493_, 0);
v_used_495_ = lean_ctor_get(v___x_493_, 1);
v_binderRenaming_496_ = lean_ctor_get(v___x_493_, 2);
v_funDeclInfoMap_497_ = lean_ctor_get(v___x_493_, 3);
v_simplified_498_ = lean_ctor_get_uint8(v___x_493_, sizeof(void*)*7);
v_visited_499_ = lean_ctor_get(v___x_493_, 4);
v_inline_500_ = lean_ctor_get(v___x_493_, 5);
v_inlineLocal_501_ = lean_ctor_get(v___x_493_, 6);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_512_ == 0)
{
v___x_503_ = v___x_493_;
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_inlineLocal_501_);
lean_inc(v_inline_500_);
lean_inc(v_visited_499_);
lean_inc(v_funDeclInfoMap_497_);
lean_inc(v_binderRenaming_496_);
lean_inc(v_used_495_);
lean_inc(v_subst_494_);
lean_dec(v___x_493_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(v_funDeclInfoMap_497_, v_fvarId_490_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 3, v___x_505_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_subst_494_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_used_495_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_binderRenaming_496_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_visited_499_);
lean_ctor_set(v_reuseFailAlloc_511_, 5, v_inline_500_);
lean_ctor_set(v_reuseFailAlloc_511_, 6, v_inlineLocal_501_);
lean_ctor_set_uint8(v_reuseFailAlloc_511_, sizeof(void*)*7, v_simplified_498_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_st_ref_set(v_a_491_, v___x_507_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg___boxed(lean_object* v_fvarId_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(v_fvarId_513_, v_a_514_);
lean_dec(v_a_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc(lean_object* v_fvarId_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(v_fvarId_517_, v_a_519_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___boxed(lean_object* v_fvarId_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc(v_fvarId_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec_ref(v_a_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
return v_res_536_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_box(0);
v___x_538_ = lean_unsigned_to_nat(16u);
v___x_539_ = lean_mk_array(v___x_538_, v___x_537_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___x_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object* v_code_543_, uint8_t v_mustInline_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___x_551_; lean_object* v_subst_552_; lean_object* v_used_553_; lean_object* v_binderRenaming_554_; lean_object* v_funDeclInfoMap_555_; uint8_t v_simplified_556_; lean_object* v_visited_557_; lean_object* v_inline_558_; lean_object* v_inlineLocal_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_603_; 
v___x_551_ = lean_st_ref_take(v_a_545_);
v_subst_552_ = lean_ctor_get(v___x_551_, 0);
v_used_553_ = lean_ctor_get(v___x_551_, 1);
v_binderRenaming_554_ = lean_ctor_get(v___x_551_, 2);
v_funDeclInfoMap_555_ = lean_ctor_get(v___x_551_, 3);
v_simplified_556_ = lean_ctor_get_uint8(v___x_551_, sizeof(void*)*7);
v_visited_557_ = lean_ctor_get(v___x_551_, 4);
v_inline_558_ = lean_ctor_get(v___x_551_, 5);
v_inlineLocal_559_ = lean_ctor_get(v___x_551_, 6);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_603_ == 0)
{
v___x_561_ = v___x_551_;
v_isShared_562_ = v_isSharedCheck_603_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_inlineLocal_559_);
lean_inc(v_inline_558_);
lean_inc(v_visited_557_);
lean_inc(v_funDeclInfoMap_555_);
lean_inc(v_binderRenaming_554_);
lean_inc(v_used_553_);
lean_inc(v_subst_552_);
lean_dec(v___x_551_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_603_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 3, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_subst_552_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_used_553_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v_binderRenaming_554_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v_visited_557_);
lean_ctor_set(v_reuseFailAlloc_602_, 5, v_inline_558_);
lean_ctor_set(v_reuseFailAlloc_602_, 6, v_inlineLocal_559_);
lean_ctor_set_uint8(v_reuseFailAlloc_602_, sizeof(void*)*7, v_simplified_556_);
v___x_565_ = v_reuseFailAlloc_602_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_st_ref_set(v_a_545_, v___x_565_);
v___x_567_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(v_funDeclInfoMap_555_, v_code_543_, v_mustInline_544_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_593_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_593_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_593_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_593_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v_subst_573_; lean_object* v_used_574_; lean_object* v_binderRenaming_575_; uint8_t v_simplified_576_; lean_object* v_visited_577_; lean_object* v_inline_578_; lean_object* v_inlineLocal_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_591_; 
v___x_572_ = lean_st_ref_take(v_a_545_);
v_subst_573_ = lean_ctor_get(v___x_572_, 0);
v_used_574_ = lean_ctor_get(v___x_572_, 1);
v_binderRenaming_575_ = lean_ctor_get(v___x_572_, 2);
v_simplified_576_ = lean_ctor_get_uint8(v___x_572_, sizeof(void*)*7);
v_visited_577_ = lean_ctor_get(v___x_572_, 4);
v_inline_578_ = lean_ctor_get(v___x_572_, 5);
v_inlineLocal_579_ = lean_ctor_get(v___x_572_, 6);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v___x_572_, 3);
lean_dec(v_unused_592_);
v___x_581_ = v___x_572_;
v_isShared_582_ = v_isSharedCheck_591_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_inlineLocal_579_);
lean_inc(v_inline_578_);
lean_inc(v_visited_577_);
lean_inc(v_binderRenaming_575_);
lean_inc(v_used_574_);
lean_inc(v_subst_573_);
lean_dec(v___x_572_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_591_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 3, v_a_568_);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_subst_573_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_used_574_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_binderRenaming_575_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v_a_568_);
lean_ctor_set(v_reuseFailAlloc_590_, 4, v_visited_577_);
lean_ctor_set(v_reuseFailAlloc_590_, 5, v_inline_578_);
lean_ctor_set(v_reuseFailAlloc_590_, 6, v_inlineLocal_579_);
lean_ctor_set_uint8(v_reuseFailAlloc_590_, sizeof(void*)*7, v_simplified_576_);
v___x_584_ = v_reuseFailAlloc_590_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_585_ = lean_st_ref_set(v_a_545_, v___x_584_);
v___x_586_ = lean_box(0);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_586_);
v___x_588_ = v___x_570_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_a_594_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_567_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_567_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___boxed(lean_object* v_code_604_, lean_object* v_mustInline_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
uint8_t v_mustInline_boxed_612_; lean_object* v_res_613_; 
v_mustInline_boxed_612_ = lean_unbox(v_mustInline_605_);
v_res_613_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_604_, v_mustInline_boxed_612_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object* v_code_614_, uint8_t v_mustInline_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_614_, v_mustInline_615_, v_a_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___boxed(lean_object* v_code_625_, lean_object* v_mustInline_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
uint8_t v_mustInline_boxed_635_; lean_object* v_res_636_; 
v_mustInline_boxed_635_ = lean_unbox(v_mustInline_626_);
v_res_636_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(v_code_625_, v_mustInline_boxed_635_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
return v_res_636_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_637_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1);
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
lean_ctor_set(v___x_642_, 2, v___x_641_);
lean_ctor_set(v___x_642_, 3, v___x_640_);
lean_ctor_set(v___x_642_, 4, v___x_640_);
lean_ctor_set(v___x_642_, 5, v___x_640_);
lean_ctor_set(v___x_642_, 6, v___x_640_);
lean_ctor_set(v___x_642_, 7, v___x_640_);
lean_ctor_set(v___x_642_, 8, v___x_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(lean_object* v_msg_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_options_649_; lean_object* v_ref_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_options_649_ = lean_ctor_get(v___y_646_, 2);
v_ref_650_ = lean_ctor_get(v___y_646_, 5);
v___x_651_ = lean_st_ref_get(v___y_647_);
v___x_652_ = lean_st_ref_get(v___y_645_);
v___x_653_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_644_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_676_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_676_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_676_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_676_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_env_658_; lean_object* v_lctx_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_674_; 
v_env_658_ = lean_ctor_get(v___x_651_, 0);
lean_inc_ref(v_env_658_);
lean_dec(v___x_651_);
v_lctx_659_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v___x_652_, 1);
lean_dec(v_unused_675_);
v___x_661_ = v___x_652_;
v_isShared_662_ = v_isSharedCheck_674_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_lctx_659_);
lean_dec(v___x_652_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_674_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
uint8_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_663_ = lean_unbox(v_a_654_);
lean_dec(v_a_654_);
v___x_664_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_659_, v___x_663_);
lean_dec_ref(v_lctx_659_);
v___x_665_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2);
lean_inc_ref(v_options_649_);
v___x_666_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_666_, 0, v_env_658_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
lean_ctor_set(v___x_666_, 2, v___x_664_);
lean_ctor_set(v___x_666_, 3, v_options_649_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 3);
lean_ctor_set(v___x_661_, 1, v_msg_643_);
lean_ctor_set(v___x_661_, 0, v___x_666_);
v___x_668_ = v___x_661_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_msg_643_);
v___x_668_ = v_reuseFailAlloc_673_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
lean_inc(v_ref_650_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v_ref_650_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
if (v_isShared_657_ == 0)
{
lean_ctor_set_tag(v___x_656_, 1);
lean_ctor_set(v___x_656_, 0, v___x_669_);
v___x_671_ = v___x_656_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec_ref(v_msg_643_);
v_a_677_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_653_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_653_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___boxed(lean_object* v_msg_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v_msg_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0(lean_object* v_00_u03b1_692_, lean_object* v_msg_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v_msg_693_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___boxed(lean_object* v_00_u03b1_703_, lean_object* v_msg_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0(v_00_u03b1_703_, v_msg_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(lean_object* v_cls_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_options_720_; uint8_t v_hasTrace_721_; 
v_options_720_ = lean_ctor_get(v___y_718_, 2);
v_hasTrace_721_ = lean_ctor_get_uint8(v_options_720_, sizeof(void*)*1);
if (v_hasTrace_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec(v_cls_717_);
v___x_722_ = lean_box(v_hasTrace_721_);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
else
{
lean_object* v_inheritedTraceOptions_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_inheritedTraceOptions_724_ = lean_ctor_get(v___y_718_, 13);
v___x_725_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1));
v___x_726_ = l_Lean_Name_append(v___x_725_, v_cls_717_);
v___x_727_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_724_, v_options_720_, v___x_726_);
lean_dec(v___x_726_);
v___x_728_ = lean_box(v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___boxed(lean_object* v_cls_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_730_, v___y_731_);
lean_dec_ref(v___y_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(lean_object* v_cls_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_734_, v___y_740_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___boxed(lean_object* v_cls_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(v_cls_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
return v_res_753_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_754_; double v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_float_of_nat(v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg(lean_object* v_cls_759_, lean_object* v_msg_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_options_766_; lean_object* v_ref_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_options_766_ = lean_ctor_get(v___y_763_, 2);
v_ref_767_ = lean_ctor_get(v___y_763_, 5);
v___x_768_ = lean_st_ref_get(v___y_764_);
v___x_769_ = lean_st_ref_get(v___y_762_);
v___x_770_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_761_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_829_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_829_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_829_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_829_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_env_775_; lean_object* v_lctx_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_827_; 
v_env_775_ = lean_ctor_get(v___x_768_, 0);
lean_inc_ref(v_env_775_);
lean_dec(v___x_768_);
v_lctx_776_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v___x_769_, 1);
lean_dec(v_unused_828_);
v___x_778_ = v___x_769_;
v_isShared_779_ = v_isSharedCheck_827_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_lctx_776_);
lean_dec(v___x_769_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_827_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v_traceState_782_; lean_object* v_env_783_; lean_object* v_nextMacroScope_784_; lean_object* v_ngen_785_; lean_object* v_auxDeclNGen_786_; lean_object* v_cache_787_; lean_object* v_messages_788_; lean_object* v_infoState_789_; lean_object* v_snapshotTasks_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_826_; 
v___x_780_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2);
v___x_781_ = lean_st_ref_take(v___y_764_);
v_traceState_782_ = lean_ctor_get(v___x_781_, 4);
v_env_783_ = lean_ctor_get(v___x_781_, 0);
v_nextMacroScope_784_ = lean_ctor_get(v___x_781_, 1);
v_ngen_785_ = lean_ctor_get(v___x_781_, 2);
v_auxDeclNGen_786_ = lean_ctor_get(v___x_781_, 3);
v_cache_787_ = lean_ctor_get(v___x_781_, 5);
v_messages_788_ = lean_ctor_get(v___x_781_, 6);
v_infoState_789_ = lean_ctor_get(v___x_781_, 7);
v_snapshotTasks_790_ = lean_ctor_get(v___x_781_, 8);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_826_ == 0)
{
v___x_792_ = v___x_781_;
v_isShared_793_ = v_isSharedCheck_826_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_snapshotTasks_790_);
lean_inc(v_infoState_789_);
lean_inc(v_messages_788_);
lean_inc(v_cache_787_);
lean_inc(v_traceState_782_);
lean_inc(v_auxDeclNGen_786_);
lean_inc(v_ngen_785_);
lean_inc(v_nextMacroScope_784_);
lean_inc(v_env_783_);
lean_dec(v___x_781_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_826_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
uint64_t v_tid_794_; lean_object* v_traces_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_825_; 
v_tid_794_ = lean_ctor_get_uint64(v_traceState_782_, sizeof(void*)*1);
v_traces_795_ = lean_ctor_get(v_traceState_782_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v_traceState_782_);
if (v_isSharedCheck_825_ == 0)
{
v___x_797_ = v_traceState_782_;
v_isShared_798_ = v_isSharedCheck_825_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_traces_795_);
lean_dec(v_traceState_782_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_825_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_799_ = lean_unbox(v_a_771_);
lean_dec(v_a_771_);
v___x_800_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_776_, v___x_799_);
lean_dec_ref(v_lctx_776_);
lean_inc_ref(v_options_766_);
v___x_801_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_801_, 0, v_env_775_);
lean_ctor_set(v___x_801_, 1, v___x_780_);
lean_ctor_set(v___x_801_, 2, v___x_800_);
lean_ctor_set(v___x_801_, 3, v_options_766_);
if (v_isShared_779_ == 0)
{
lean_ctor_set_tag(v___x_778_, 3);
lean_ctor_set(v___x_778_, 1, v_msg_760_);
lean_ctor_set(v___x_778_, 0, v___x_801_);
v___x_803_ = v___x_778_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_msg_760_);
v___x_803_ = v_reuseFailAlloc_824_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; double v___x_805_; uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_804_ = lean_box(0);
v___x_805_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__0);
v___x_806_ = 0;
v___x_807_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__1));
v___x_808_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_808_, 0, v_cls_759_);
lean_ctor_set(v___x_808_, 1, v___x_804_);
lean_ctor_set(v___x_808_, 2, v___x_807_);
lean_ctor_set_float(v___x_808_, sizeof(void*)*3, v___x_805_);
lean_ctor_set_float(v___x_808_, sizeof(void*)*3 + 8, v___x_805_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*3 + 16, v___x_806_);
v___x_809_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___closed__2));
v___x_810_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_803_);
lean_ctor_set(v___x_810_, 2, v___x_809_);
lean_inc(v_ref_767_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_ref_767_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l_Lean_PersistentArray_push___redArg(v_traces_795_, v___x_811_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_812_);
v___x_814_ = v___x_797_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_812_);
lean_ctor_set_uint64(v_reuseFailAlloc_823_, sizeof(void*)*1, v_tid_794_);
v___x_814_ = v_reuseFailAlloc_823_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 4, v___x_814_);
v___x_816_ = v___x_792_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_env_783_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_nextMacroScope_784_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_ngen_785_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_auxDeclNGen_786_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_822_, 5, v_cache_787_);
lean_ctor_set(v_reuseFailAlloc_822_, 6, v_messages_788_);
lean_ctor_set(v_reuseFailAlloc_822_, 7, v_infoState_789_);
lean_ctor_set(v_reuseFailAlloc_822_, 8, v_snapshotTasks_790_);
v___x_816_ = v_reuseFailAlloc_822_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_817_ = lean_st_ref_set(v___y_764_, v___x_816_);
v___x_818_ = lean_box(0);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_818_);
v___x_820_ = v___x_773_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
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
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v___x_769_);
lean_dec(v___x_768_);
lean_dec_ref(v_msg_760_);
lean_dec(v_cls_759_);
v_a_830_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_770_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_770_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg___boxed(lean_object* v_cls_838_, lean_object* v_msg_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg(v_cls_838_, v_msg_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3(lean_object* v_cls_846_, lean_object* v_msg_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg(v_cls_846_, v_msg_847_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___boxed(lean_object* v_cls_857_, lean_object* v_msg_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3(v_cls_857_, v_msg_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__4___redArg(lean_object* v_keys_868_, lean_object* v_vals_869_, lean_object* v_i_870_, lean_object* v_k_871_){
_start:
{
lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_872_ = lean_array_get_size(v_keys_868_);
v___x_873_ = lean_nat_dec_lt(v_i_870_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec(v_i_870_);
v___x_874_ = lean_box(0);
return v___x_874_;
}
else
{
lean_object* v_k_x27_875_; uint8_t v___x_876_; 
v_k_x27_875_ = lean_array_fget_borrowed(v_keys_868_, v_i_870_);
v___x_876_ = lean_name_eq(v_k_871_, v_k_x27_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_unsigned_to_nat(1u);
v___x_878_ = lean_nat_add(v_i_870_, v___x_877_);
lean_dec(v_i_870_);
v_i_870_ = v___x_878_;
goto _start;
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_array_fget_borrowed(v_vals_869_, v_i_870_);
lean_dec(v_i_870_);
lean_inc(v___x_880_);
v___x_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_keys_882_, lean_object* v_vals_883_, lean_object* v_i_884_, lean_object* v_k_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__4___redArg(v_keys_882_, v_vals_883_, v_i_884_, v_k_885_);
lean_dec(v_k_885_);
lean_dec_ref(v_vals_883_);
lean_dec_ref(v_keys_882_);
return v_res_886_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_887_; size_t v___x_888_; size_t v___x_889_; 
v___x_887_ = ((size_t)5ULL);
v___x_888_ = ((size_t)1ULL);
v___x_889_ = lean_usize_shift_left(v___x_888_, v___x_887_);
return v___x_889_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_890_; size_t v___x_891_; size_t v___x_892_; 
v___x_890_ = ((size_t)1ULL);
v___x_891_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__0);
v___x_892_ = lean_usize_sub(v___x_891_, v___x_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(lean_object* v_x_893_, size_t v_x_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_object* v_es_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_917_; 
v_es_896_ = lean_ctor_get(v_x_893_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_x_893_);
if (v_isSharedCheck_917_ == 0)
{
v___x_898_ = v_x_893_;
v_isShared_899_ = v_isSharedCheck_917_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_es_896_);
lean_dec(v_x_893_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_917_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; lean_object* v_j_904_; lean_object* v___x_905_; 
v___x_900_ = lean_box(2);
v___x_901_ = ((size_t)5ULL);
v___x_902_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__1);
v___x_903_ = lean_usize_land(v_x_894_, v___x_902_);
v_j_904_ = lean_usize_to_nat(v___x_903_);
v___x_905_ = lean_array_get(v___x_900_, v_es_896_, v_j_904_);
lean_dec(v_j_904_);
lean_dec_ref(v_es_896_);
switch(lean_obj_tag(v___x_905_))
{
case 0:
{
lean_object* v_key_906_; lean_object* v_val_907_; uint8_t v___x_908_; 
v_key_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_key_906_);
v_val_907_ = lean_ctor_get(v___x_905_, 1);
lean_inc(v_val_907_);
lean_dec_ref(v___x_905_);
v___x_908_ = lean_name_eq(v_x_895_, v_key_906_);
lean_dec(v_key_906_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
lean_dec(v_val_907_);
lean_del_object(v___x_898_);
v___x_909_ = lean_box(0);
return v___x_909_;
}
else
{
lean_object* v___x_911_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set_tag(v___x_898_, 1);
lean_ctor_set(v___x_898_, 0, v_val_907_);
v___x_911_ = v___x_898_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_val_907_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
case 1:
{
lean_object* v_node_913_; size_t v___x_914_; 
lean_del_object(v___x_898_);
v_node_913_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_node_913_);
lean_dec_ref(v___x_905_);
v___x_914_ = lean_usize_shift_right(v_x_894_, v___x_901_);
v_x_893_ = v_node_913_;
v_x_894_ = v___x_914_;
goto _start;
}
default: 
{
lean_object* v___x_916_; 
lean_del_object(v___x_898_);
v___x_916_ = lean_box(0);
return v___x_916_;
}
}
}
}
else
{
lean_object* v_ks_918_; lean_object* v_vs_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_ks_918_ = lean_ctor_get(v_x_893_, 0);
lean_inc_ref(v_ks_918_);
v_vs_919_ = lean_ctor_get(v_x_893_, 1);
lean_inc_ref(v_vs_919_);
lean_dec_ref(v_x_893_);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__4___redArg(v_ks_918_, v_vs_919_, v___x_920_, v_x_895_);
lean_dec_ref(v_vs_919_);
lean_dec_ref(v_ks_918_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___boxed(lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
size_t v_x_7596__boxed_925_; lean_object* v_res_926_; 
v_x_7596__boxed_925_ = lean_unbox_usize(v_x_923_);
lean_dec(v_x_923_);
v_res_926_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_922_, v_x_7596__boxed_925_, v_x_924_);
lean_dec(v_x_924_);
return v_res_926_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_927_; uint64_t v___x_928_; 
v___x_927_ = lean_unsigned_to_nat(1723u);
v___x_928_ = lean_uint64_of_nat(v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(lean_object* v_x_929_, lean_object* v_x_930_){
_start:
{
uint64_t v___y_932_; 
if (lean_obj_tag(v_x_930_) == 0)
{
uint64_t v___x_935_; 
v___x_935_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0);
v___y_932_ = v___x_935_;
goto v___jp_931_;
}
else
{
uint64_t v_hash_936_; 
v_hash_936_ = lean_ctor_get_uint64(v_x_930_, sizeof(void*)*2);
v___y_932_ = v_hash_936_;
goto v___jp_931_;
}
v___jp_931_:
{
size_t v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_uint64_to_usize(v___y_932_);
v___x_934_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_929_, v___x_933_, v_x_930_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___boxed(lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_x_937_, v_x_938_);
lean_dec(v_x_938_);
return v_res_939_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__0));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__2));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__4));
v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t v_recursive_956_, lean_object* v_declName_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___y_967_; uint8_t v_inlineIfReduce_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v_cls_1090_; lean_object* v___x_1091_; lean_object* v_a_1092_; uint8_t v___x_1093_; 
v_cls_1090_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9));
v___x_1091_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_1090_, v_a_963_);
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref(v___x_1091_);
v___x_1093_ = lean_unbox(v_a_1092_);
lean_dec(v_a_1092_);
if (v___x_1093_ == 0)
{
v___y_1079_ = v_a_958_;
v___y_1080_ = v_a_959_;
v___y_1081_ = v_a_960_;
v___y_1082_ = v_a_961_;
v___y_1083_ = v_a_962_;
v___y_1084_ = v_a_963_;
v___y_1085_ = v_a_964_;
goto v___jp_1078_;
}
else
{
uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = 0;
lean_inc(v_declName_957_);
v___x_1095_ = l_Lean_MessageData_ofConstName(v_declName_957_, v___x_1094_);
v___x_1096_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__3___redArg(v_cls_1090_, v___x_1095_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_dec_ref(v___x_1096_);
v___y_1079_ = v_a_958_;
v___y_1080_ = v_a_959_;
v___y_1081_ = v_a_960_;
v___y_1082_ = v_a_961_;
v___y_1083_ = v_a_962_;
v___y_1084_ = v_a_963_;
v___y_1085_ = v_a_964_;
goto v___jp_1078_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v_a_958_);
lean_dec(v_declName_957_);
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1096_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
v___jp_966_:
{
lean_object* v___x_976_; 
lean_dec_ref(v___y_969_);
v___x_976_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_972_);
if (lean_obj_tag(v___x_976_) == 0)
{
if (v_recursive_956_ == 0)
{
lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_declName_957_);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v___x_976_, 0);
lean_dec(v_unused_984_);
v___x_978_ = v___x_976_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_dec(v___x_976_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___y_967_);
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___y_967_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
else
{
if (v_inlineIfReduce_968_ == 0)
{
lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_declName_957_);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v___x_976_, 0);
lean_dec(v_unused_992_);
v___x_986_ = v___x_976_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_dec(v___x_976_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___y_967_);
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___y_967_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1034_; 
v_a_993_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_995_ = v___x_976_;
v_isShared_996_ = v_isSharedCheck_1034_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_976_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1034_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v_maxRecInlineIfReduce_997_; uint8_t v___x_998_; 
v_maxRecInlineIfReduce_997_ = lean_ctor_get(v_a_993_, 2);
lean_inc(v_maxRecInlineIfReduce_997_);
lean_dec(v_a_993_);
v___x_998_ = lean_nat_dec_lt(v_maxRecInlineIfReduce_997_, v___y_967_);
lean_dec(v_maxRecInlineIfReduce_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_1000_; 
lean_dec(v_declName_957_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___y_967_);
v___x_1000_ = v___x_995_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___y_967_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
else
{
lean_object* v___x_1002_; 
lean_del_object(v___x_995_);
lean_dec(v___y_967_);
v___x_1002_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_972_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v_maxRecInlineIfReduce_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref(v___x_1002_);
v_maxRecInlineIfReduce_1004_ = lean_ctor_get(v_a_1003_, 2);
lean_inc(v_maxRecInlineIfReduce_1004_);
lean_dec(v_a_1003_);
v___x_1005_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1);
v___x_1006_ = 0;
v___x_1007_ = l_Lean_MessageData_ofConstName(v_declName_957_, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1005_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Nat_reprFast(v_maxRecInlineIfReduce_1004_);
v___x_1012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = l_Lean_MessageData_ofFormat(v___x_1012_);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1010_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_1016_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_declName_957_);
v_a_1026_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1002_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1002_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
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
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v___y_967_);
lean_dec(v_declName_957_);
v_a_1035_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_976_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_976_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
v___jp_1043_:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_1045_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = lean_unbox(v_a_1053_);
lean_dec(v_a_1053_);
lean_inc(v_declName_957_);
v___x_1055_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_957_, v___x_1054_, v___y_1047_, v___y_1046_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref(v___x_1055_);
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v___y_1051_, v___x_1057_);
lean_dec(v___y_1051_);
if (lean_obj_tag(v_a_1056_) == 1)
{
lean_object* v_val_1059_; uint8_t v___x_1060_; 
v_val_1059_ = lean_ctor_get(v_a_1056_, 0);
lean_inc(v_val_1059_);
lean_dec_ref(v_a_1056_);
v___x_1060_ = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(v_val_1059_);
lean_dec(v_val_1059_);
v___y_967_ = v___x_1058_;
v_inlineIfReduce_968_ = v___x_1060_;
v___y_969_ = v___y_1044_;
v___y_970_ = v___y_1050_;
v___y_971_ = v___y_1049_;
v___y_972_ = v___y_1045_;
v___y_973_ = v___y_1048_;
v___y_974_ = v___y_1047_;
v___y_975_ = v___y_1046_;
goto v___jp_966_;
}
else
{
uint8_t v___x_1061_; 
lean_dec(v_a_1056_);
v___x_1061_ = 0;
v___y_967_ = v___x_1058_;
v_inlineIfReduce_968_ = v___x_1061_;
v___y_969_ = v___y_1044_;
v___y_970_ = v___y_1050_;
v___y_971_ = v___y_1049_;
v___y_972_ = v___y_1045_;
v___y_973_ = v___y_1048_;
v___y_974_ = v___y_1047_;
v___y_975_ = v___y_1046_;
goto v___jp_966_;
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1044_);
lean_dec(v_declName_957_);
v_a_1062_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1055_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1055_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1044_);
lean_dec(v_declName_957_);
v_a_1070_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1052_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1052_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
v___jp_1078_:
{
lean_object* v_inlineStackOccs_1086_; lean_object* v___x_1087_; 
v_inlineStackOccs_1086_ = lean_ctor_get(v___y_1079_, 3);
lean_inc_ref(v_inlineStackOccs_1086_);
v___x_1087_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_inlineStackOccs_1086_, v_declName_957_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_unsigned_to_nat(0u);
v___y_1044_ = v___y_1079_;
v___y_1045_ = v___y_1082_;
v___y_1046_ = v___y_1085_;
v___y_1047_ = v___y_1084_;
v___y_1048_ = v___y_1083_;
v___y_1049_ = v___y_1081_;
v___y_1050_ = v___y_1080_;
v___y_1051_ = v___x_1088_;
goto v___jp_1043_;
}
else
{
lean_object* v_val_1089_; 
v_val_1089_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_val_1089_);
lean_dec_ref(v___x_1087_);
v___y_1044_ = v___y_1079_;
v___y_1045_ = v___y_1082_;
v___y_1046_ = v___y_1085_;
v___y_1047_ = v___y_1084_;
v___y_1048_ = v___y_1083_;
v___y_1049_ = v___y_1081_;
v___y_1050_ = v___y_1080_;
v___y_1051_ = v_val_1089_;
goto v___jp_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___boxed(lean_object* v_recursive_1105_, lean_object* v_declName_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
uint8_t v_recursive_boxed_1115_; lean_object* v_res_1116_; 
v_recursive_boxed_1115_ = lean_unbox(v_recursive_1105_);
v_res_1116_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_boxed_1115_, v_declName_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1(lean_object* v_00_u03b2_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_x_1118_, v_x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___boxed(lean_object* v_00_u03b2_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1(v_00_u03b2_1121_, v_x_1122_, v_x_1123_);
lean_dec(v_x_1123_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(lean_object* v_00_u03b2_1125_, lean_object* v_x_1126_, size_t v_x_1127_, lean_object* v_x_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_1126_, v_x_1127_, v_x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_){
_start:
{
size_t v_x_8036__boxed_1134_; lean_object* v_res_1135_; 
v_x_8036__boxed_1134_ = lean_unbox_usize(v_x_1132_);
lean_dec(v_x_1132_);
v_res_1135_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(v_00_u03b2_1130_, v_x_1131_, v_x_8036__boxed_1134_, v_x_1133_);
lean_dec(v_x_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_1136_, lean_object* v_keys_1137_, lean_object* v_vals_1138_, lean_object* v_heq_1139_, lean_object* v_i_1140_, lean_object* v_k_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__4___redArg(v_keys_1137_, v_vals_1138_, v_i_1140_, v_k_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1143_, lean_object* v_keys_1144_, lean_object* v_vals_1145_, lean_object* v_heq_1146_, lean_object* v_i_1147_, lean_object* v_k_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__4(v_00_u03b2_1143_, v_keys_1144_, v_vals_1145_, v_heq_1146_, v_i_1147_, v_k_1148_);
lean_dec(v_k_1148_);
lean_dec_ref(v_vals_1145_);
lean_dec_ref(v_keys_1144_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg(lean_object* v_value_1152_, uint8_t v_recursive_1153_, lean_object* v_x_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
if (lean_obj_tag(v_value_1152_) == 3)
{
lean_object* v_declName_1163_; lean_object* v___x_1164_; 
v_declName_1163_ = lean_ctor_get(v_value_1152_, 0);
lean_inc(v_declName_1163_);
lean_dec_ref(v_value_1152_);
lean_inc_ref(v_a_1155_);
lean_inc(v_declName_1163_);
v___x_1164_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1153_, v_declName_1163_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v_declName_1166_; lean_object* v_config_1167_; lean_object* v_inlineStack_1168_; lean_object* v_inlineStackOccs_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1181_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref(v___x_1164_);
v_declName_1166_ = lean_ctor_get(v_a_1155_, 0);
v_config_1167_ = lean_ctor_get(v_a_1155_, 1);
v_inlineStack_1168_ = lean_ctor_get(v_a_1155_, 2);
v_inlineStackOccs_1169_ = lean_ctor_get(v_a_1155_, 3);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_a_1155_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1171_ = v_a_1155_;
v_isShared_1172_ = v_isSharedCheck_1181_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_inlineStackOccs_1169_);
lean_inc(v_inlineStack_1168_);
lean_inc(v_config_1167_);
lean_inc(v_declName_1166_);
lean_dec(v_a_1155_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1181_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1173_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0));
v___x_1174_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1));
lean_inc(v_declName_1163_);
v___x_1175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_declName_1163_);
lean_ctor_set(v___x_1175_, 1, v_inlineStack_1168_);
v___x_1176_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1173_, v___x_1174_, v_inlineStackOccs_1169_, v_declName_1163_, v_a_1165_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 3, v___x_1176_);
lean_ctor_set(v___x_1171_, 2, v___x_1175_);
v___x_1178_ = v___x_1171_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_declName_1166_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_config_1167_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_apply_8(v_x_1154_, v___x_1178_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, lean_box(0));
return v___x_1179_;
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v_declName_1163_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec_ref(v_x_1154_);
v_a_1182_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1164_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1164_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_object* v___x_1190_; 
lean_dec(v_value_1152_);
v___x_1190_ = lean_apply_8(v_x_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, lean_box(0));
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg___boxed(lean_object* v_value_1191_, lean_object* v_recursive_1192_, lean_object* v_x_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
uint8_t v_recursive_boxed_1202_; lean_object* v_res_1203_; 
v_recursive_boxed_1202_ = lean_unbox(v_recursive_1192_);
v_res_1203_ = l_Lean_Compiler_LCNF_Simp_withInlining___redArg(v_value_1191_, v_recursive_boxed_1202_, v_x_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining(lean_object* v_00_u03b1_1204_, lean_object* v_value_1205_, uint8_t v_recursive_1206_, lean_object* v_x_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
if (lean_obj_tag(v_value_1205_) == 3)
{
lean_object* v_declName_1216_; lean_object* v___x_1217_; 
v_declName_1216_ = lean_ctor_get(v_value_1205_, 0);
lean_inc(v_declName_1216_);
lean_dec_ref(v_value_1205_);
lean_inc_ref(v_a_1208_);
lean_inc(v_declName_1216_);
v___x_1217_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1206_, v_declName_1216_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v_declName_1219_; lean_object* v_config_1220_; lean_object* v_inlineStack_1221_; lean_object* v_inlineStackOccs_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1234_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref(v___x_1217_);
v_declName_1219_ = lean_ctor_get(v_a_1208_, 0);
v_config_1220_ = lean_ctor_get(v_a_1208_, 1);
v_inlineStack_1221_ = lean_ctor_get(v_a_1208_, 2);
v_inlineStackOccs_1222_ = lean_ctor_get(v_a_1208_, 3);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_a_1208_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1224_ = v_a_1208_;
v_isShared_1225_ = v_isSharedCheck_1234_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_inlineStackOccs_1222_);
lean_inc(v_inlineStack_1221_);
lean_inc(v_config_1220_);
lean_inc(v_declName_1219_);
lean_dec(v_a_1208_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1234_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1226_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0));
v___x_1227_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1));
lean_inc(v_declName_1216_);
v___x_1228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_declName_1216_);
lean_ctor_set(v___x_1228_, 1, v_inlineStack_1221_);
v___x_1229_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1226_, v___x_1227_, v_inlineStackOccs_1222_, v_declName_1216_, v_a_1218_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 3, v___x_1229_);
lean_ctor_set(v___x_1224_, 2, v___x_1228_);
v___x_1231_ = v___x_1224_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_declName_1219_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_config_1220_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_apply_8(v_x_1207_, v___x_1231_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, lean_box(0));
return v___x_1232_;
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec(v_declName_1216_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec_ref(v_x_1207_);
v_a_1235_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1217_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1217_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_object* v___x_1243_; 
lean_dec(v_value_1205_);
v___x_1243_ = lean_apply_8(v_x_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, lean_box(0));
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___boxed(lean_object* v_00_u03b1_1244_, lean_object* v_value_1245_, lean_object* v_recursive_1246_, lean_object* v_x_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
uint8_t v_recursive_boxed_1256_; lean_object* v_res_1257_; 
v_recursive_boxed_1256_ = lean_unbox(v_recursive_1246_);
v_res_1257_ = l_Lean_Compiler_LCNF_Simp_withInlining(v_00_u03b1_1244_, v_value_1245_, v_recursive_boxed_1256_, v_x_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
return v_res_1257_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__0));
v___x_1260_ = l_Lean_stringToMessageData(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__3));
v___x_1265_ = l_Lean_MessageData_ofFormat(v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(lean_object* v_as_x27_1266_, lean_object* v_b_1267_){
_start:
{
if (lean_obj_tag(v_as_x27_1266_) == 0)
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v_b_1267_);
return v___x_1269_;
}
else
{
lean_object* v_snd_1270_; lean_object* v_head_1271_; lean_object* v_tail_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1323_; 
v_snd_1270_ = lean_ctor_get(v_b_1267_, 1);
lean_inc(v_snd_1270_);
v_head_1271_ = lean_ctor_get(v_as_x27_1266_, 0);
v_tail_1272_ = lean_ctor_get(v_as_x27_1266_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_as_x27_1266_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1274_ = v_as_x27_1266_;
v_isShared_1275_ = v_isSharedCheck_1323_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_tail_1272_);
lean_inc(v_head_1271_);
lean_dec(v_as_x27_1266_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1323_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v_fst_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1321_; 
v_fst_1276_ = lean_ctor_get(v_b_1267_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_b_1267_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; 
v_unused_1322_ = lean_ctor_get(v_b_1267_, 1);
lean_dec(v_unused_1322_);
v___x_1278_ = v_b_1267_;
v_isShared_1279_ = v_isSharedCheck_1321_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_fst_1276_);
lean_dec(v_b_1267_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1321_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_fst_1280_; lean_object* v_snd_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1320_; 
v_fst_1280_ = lean_ctor_get(v_snd_1270_, 0);
v_snd_1281_ = lean_ctor_get(v_snd_1270_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_snd_1270_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1283_ = v_snd_1270_;
v_isShared_1284_ = v_isSharedCheck_1320_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_snd_1281_);
lean_inc(v_fst_1280_);
lean_dec(v_snd_1270_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1320_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
uint8_t v___x_1285_; 
v___x_1285_ = lean_name_eq(v_fst_1280_, v_head_1271_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
lean_dec(v_snd_1281_);
lean_dec(v_fst_1280_);
v___x_1286_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1);
lean_inc(v_head_1271_);
v___x_1287_ = l_Lean_MessageData_ofConstName(v_head_1271_, v___x_1285_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set_tag(v___x_1274_, 7);
lean_ctor_set(v___x_1274_, 1, v___x_1286_);
lean_ctor_set(v___x_1274_, 0, v___x_1287_);
v___x_1289_ = v___x_1274_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___x_1286_);
v___x_1289_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1290_, 0, v_fst_1276_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = lean_box(v___x_1285_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 1, v___x_1291_);
lean_ctor_set(v___x_1283_, 0, v_head_1271_);
v___x_1293_ = v___x_1283_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_head_1271_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1295_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v___x_1293_);
lean_ctor_set(v___x_1278_, 0, v___x_1290_);
v___x_1295_ = v___x_1278_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
v_as_x27_1266_ = v_tail_1272_;
v_b_1267_ = v___x_1295_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_1300_; 
lean_dec(v_head_1271_);
v___x_1300_ = lean_unbox(v_snd_1281_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
lean_dec(v_snd_1281_);
v___x_1301_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4);
if (v_isShared_1275_ == 0)
{
lean_ctor_set_tag(v___x_1274_, 7);
lean_ctor_set(v___x_1274_, 1, v___x_1301_);
lean_ctor_set(v___x_1274_, 0, v_fst_1276_);
v___x_1303_ = v___x_1274_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_fst_1276_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_box(v___x_1285_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 1, v___x_1304_);
v___x_1306_ = v___x_1283_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_fst_1280_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v___x_1306_);
lean_ctor_set(v___x_1278_, 0, v___x_1303_);
v___x_1308_ = v___x_1278_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
v_as_x27_1266_ = v_tail_1272_;
v_b_1267_ = v___x_1308_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1314_; 
lean_del_object(v___x_1274_);
if (v_isShared_1284_ == 0)
{
v___x_1314_ = v___x_1283_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_fst_1280_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_snd_1281_);
v___x_1314_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v___x_1314_);
v___x_1316_ = v___x_1278_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_fst_1276_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
v_as_x27_1266_ = v_tail_1272_;
v_b_1267_ = v___x_1316_;
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___boxed(lean_object* v_as_x27_1324_, lean_object* v_b_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_1324_, v_b_1325_);
return v_res_1327_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = l_Lean_maxRecDepthErrorMessage;
v___x_1329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0);
v___x_1331_ = l_Lean_MessageData_ofFormat(v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__2));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_inlineStack_1343_; 
v_inlineStack_1343_ = lean_ctor_get(v_a_1335_, 2);
lean_inc(v_inlineStack_1343_);
lean_dec_ref(v_a_1335_);
if (lean_obj_tag(v_inlineStack_1343_) == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1);
v___x_1345_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_1344_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
return v___x_1345_;
}
else
{
lean_object* v_head_1346_; lean_object* v_tail_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1373_; 
v_head_1346_ = lean_ctor_get(v_inlineStack_1343_, 0);
v_tail_1347_ = lean_ctor_get(v_inlineStack_1343_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_inlineStack_1343_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1349_ = v_inlineStack_1343_;
v_isShared_1350_ = v_isSharedCheck_1373_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_tail_1347_);
lean_inc(v_head_1346_);
lean_dec(v_inlineStack_1343_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1373_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1351_ = 0;
lean_inc(v_head_1346_);
v___x_1352_ = l_Lean_MessageData_ofConstName(v_head_1346_, v___x_1351_);
v___x_1353_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1);
if (v_isShared_1350_ == 0)
{
lean_ctor_set_tag(v___x_1349_, 7);
lean_ctor_set(v___x_1349_, 1, v___x_1353_);
lean_ctor_set(v___x_1349_, 0, v___x_1352_);
v___x_1355_ = v___x_1349_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v_a_1360_; lean_object* v_fst_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1370_; 
v___x_1356_ = lean_box(v___x_1351_);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v_head_1346_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1355_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_tail_1347_, v___x_1358_);
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
v_fst_1361_ = lean_ctor_get(v_a_1360_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_a_1360_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; 
v_unused_1371_ = lean_ctor_get(v_a_1360_, 1);
lean_dec(v_unused_1371_);
v___x_1363_ = v_a_1360_;
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_fst_1361_);
lean_dec(v_a_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3);
if (v_isShared_1364_ == 0)
{
lean_ctor_set_tag(v___x_1363_, 7);
lean_ctor_set(v___x_1363_, 1, v_fst_1361_);
lean_ctor_set(v___x_1363_, 0, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_fst_1361_);
v___x_1367_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_1367_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
return v___x_1368_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___boxed(lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object* v_00_u03b1_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___boxed(lean_object* v_00_u03b1_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(v_00_u03b1_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(lean_object* v_as_1403_, lean_object* v_as_x27_1404_, lean_object* v_b_1405_, lean_object* v_a_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_1404_, v_b_1405_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___boxed(lean_object* v_as_1416_, lean_object* v_as_x27_1417_, lean_object* v_b_1418_, lean_object* v_a_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(v_as_1416_, v_as_x27_1417_, v_b_1418_, v_a_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v_as_1416_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(lean_object* v_x_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_fileName_1438_; lean_object* v_fileMap_1439_; lean_object* v_options_1440_; lean_object* v_currRecDepth_1441_; lean_object* v_maxRecDepth_1442_; lean_object* v_ref_1443_; lean_object* v_currNamespace_1444_; lean_object* v_openDecls_1445_; lean_object* v_initHeartbeats_1446_; lean_object* v_maxHeartbeats_1447_; lean_object* v_quotContext_1448_; lean_object* v_currMacroScope_1449_; uint8_t v_diag_1450_; lean_object* v_cancelTk_x3f_1451_; uint8_t v_suppressElabErrors_1452_; lean_object* v_inheritedTraceOptions_1453_; uint8_t v___x_1454_; 
v_fileName_1438_ = lean_ctor_get(v_a_1435_, 0);
v_fileMap_1439_ = lean_ctor_get(v_a_1435_, 1);
v_options_1440_ = lean_ctor_get(v_a_1435_, 2);
v_currRecDepth_1441_ = lean_ctor_get(v_a_1435_, 3);
v_maxRecDepth_1442_ = lean_ctor_get(v_a_1435_, 4);
v_ref_1443_ = lean_ctor_get(v_a_1435_, 5);
v_currNamespace_1444_ = lean_ctor_get(v_a_1435_, 6);
v_openDecls_1445_ = lean_ctor_get(v_a_1435_, 7);
v_initHeartbeats_1446_ = lean_ctor_get(v_a_1435_, 8);
v_maxHeartbeats_1447_ = lean_ctor_get(v_a_1435_, 9);
v_quotContext_1448_ = lean_ctor_get(v_a_1435_, 10);
v_currMacroScope_1449_ = lean_ctor_get(v_a_1435_, 11);
v_diag_1450_ = lean_ctor_get_uint8(v_a_1435_, sizeof(void*)*14);
v_cancelTk_x3f_1451_ = lean_ctor_get(v_a_1435_, 12);
v_suppressElabErrors_1452_ = lean_ctor_get_uint8(v_a_1435_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1453_ = lean_ctor_get(v_a_1435_, 13);
v___x_1454_ = lean_nat_dec_eq(v_currRecDepth_1441_, v_maxRecDepth_1442_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1464_; 
lean_inc_ref(v_inheritedTraceOptions_1453_);
lean_inc(v_cancelTk_x3f_1451_);
lean_inc(v_currMacroScope_1449_);
lean_inc(v_quotContext_1448_);
lean_inc(v_maxHeartbeats_1447_);
lean_inc(v_initHeartbeats_1446_);
lean_inc(v_openDecls_1445_);
lean_inc(v_currNamespace_1444_);
lean_inc(v_ref_1443_);
lean_inc(v_maxRecDepth_1442_);
lean_inc(v_currRecDepth_1441_);
lean_inc_ref(v_options_1440_);
lean_inc_ref(v_fileMap_1439_);
lean_inc_ref(v_fileName_1438_);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_a_1435_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; lean_object* v_unused_1473_; lean_object* v_unused_1474_; lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; lean_object* v_unused_1478_; 
v_unused_1465_ = lean_ctor_get(v_a_1435_, 13);
lean_dec(v_unused_1465_);
v_unused_1466_ = lean_ctor_get(v_a_1435_, 12);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_a_1435_, 11);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_a_1435_, 10);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_a_1435_, 9);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_a_1435_, 8);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_a_1435_, 7);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_a_1435_, 6);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_a_1435_, 5);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_a_1435_, 4);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_a_1435_, 3);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_a_1435_, 2);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_a_1435_, 1);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_a_1435_, 0);
lean_dec(v_unused_1478_);
v___x_1456_ = v_a_1435_;
v_isShared_1457_ = v_isSharedCheck_1464_;
goto v_resetjp_1455_;
}
else
{
lean_dec(v_a_1435_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1464_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1459_ = lean_nat_add(v_currRecDepth_1441_, v___x_1458_);
lean_dec(v_currRecDepth_1441_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 3, v___x_1459_);
v___x_1461_ = v___x_1456_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_fileName_1438_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_fileMap_1439_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_options_1440_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v_maxRecDepth_1442_);
lean_ctor_set(v_reuseFailAlloc_1463_, 5, v_ref_1443_);
lean_ctor_set(v_reuseFailAlloc_1463_, 6, v_currNamespace_1444_);
lean_ctor_set(v_reuseFailAlloc_1463_, 7, v_openDecls_1445_);
lean_ctor_set(v_reuseFailAlloc_1463_, 8, v_initHeartbeats_1446_);
lean_ctor_set(v_reuseFailAlloc_1463_, 9, v_maxHeartbeats_1447_);
lean_ctor_set(v_reuseFailAlloc_1463_, 10, v_quotContext_1448_);
lean_ctor_set(v_reuseFailAlloc_1463_, 11, v_currMacroScope_1449_);
lean_ctor_set(v_reuseFailAlloc_1463_, 12, v_cancelTk_x3f_1451_);
lean_ctor_set(v_reuseFailAlloc_1463_, 13, v_inheritedTraceOptions_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1463_, sizeof(void*)*14, v_diag_1450_);
lean_ctor_set_uint8(v_reuseFailAlloc_1463_, sizeof(void*)*14 + 1, v_suppressElabErrors_1452_);
v___x_1461_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_apply_8(v_x_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v___x_1461_, v_a_1436_, lean_box(0));
return v___x_1462_;
}
}
}
else
{
lean_object* v___x_1479_; 
lean_dec_ref(v_x_1429_);
v___x_1479_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec_ref(v_a_1432_);
lean_dec(v_a_1431_);
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg___boxed(lean_object* v_x_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(v_x_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth(lean_object* v_00_u03b1_1490_, lean_object* v_x_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_fileName_1500_; lean_object* v_fileMap_1501_; lean_object* v_options_1502_; lean_object* v_currRecDepth_1503_; lean_object* v_maxRecDepth_1504_; lean_object* v_ref_1505_; lean_object* v_currNamespace_1506_; lean_object* v_openDecls_1507_; lean_object* v_initHeartbeats_1508_; lean_object* v_maxHeartbeats_1509_; lean_object* v_quotContext_1510_; lean_object* v_currMacroScope_1511_; uint8_t v_diag_1512_; lean_object* v_cancelTk_x3f_1513_; uint8_t v_suppressElabErrors_1514_; lean_object* v_inheritedTraceOptions_1515_; uint8_t v___x_1516_; 
v_fileName_1500_ = lean_ctor_get(v_a_1497_, 0);
v_fileMap_1501_ = lean_ctor_get(v_a_1497_, 1);
v_options_1502_ = lean_ctor_get(v_a_1497_, 2);
v_currRecDepth_1503_ = lean_ctor_get(v_a_1497_, 3);
v_maxRecDepth_1504_ = lean_ctor_get(v_a_1497_, 4);
v_ref_1505_ = lean_ctor_get(v_a_1497_, 5);
v_currNamespace_1506_ = lean_ctor_get(v_a_1497_, 6);
v_openDecls_1507_ = lean_ctor_get(v_a_1497_, 7);
v_initHeartbeats_1508_ = lean_ctor_get(v_a_1497_, 8);
v_maxHeartbeats_1509_ = lean_ctor_get(v_a_1497_, 9);
v_quotContext_1510_ = lean_ctor_get(v_a_1497_, 10);
v_currMacroScope_1511_ = lean_ctor_get(v_a_1497_, 11);
v_diag_1512_ = lean_ctor_get_uint8(v_a_1497_, sizeof(void*)*14);
v_cancelTk_x3f_1513_ = lean_ctor_get(v_a_1497_, 12);
v_suppressElabErrors_1514_ = lean_ctor_get_uint8(v_a_1497_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1515_ = lean_ctor_get(v_a_1497_, 13);
v___x_1516_ = lean_nat_dec_eq(v_currRecDepth_1503_, v_maxRecDepth_1504_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1526_; 
lean_inc_ref(v_inheritedTraceOptions_1515_);
lean_inc(v_cancelTk_x3f_1513_);
lean_inc(v_currMacroScope_1511_);
lean_inc(v_quotContext_1510_);
lean_inc(v_maxHeartbeats_1509_);
lean_inc(v_initHeartbeats_1508_);
lean_inc(v_openDecls_1507_);
lean_inc(v_currNamespace_1506_);
lean_inc(v_ref_1505_);
lean_inc(v_maxRecDepth_1504_);
lean_inc(v_currRecDepth_1503_);
lean_inc_ref(v_options_1502_);
lean_inc_ref(v_fileMap_1501_);
lean_inc_ref(v_fileName_1500_);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_a_1497_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; lean_object* v_unused_1528_; lean_object* v_unused_1529_; lean_object* v_unused_1530_; lean_object* v_unused_1531_; lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; lean_object* v_unused_1535_; lean_object* v_unused_1536_; lean_object* v_unused_1537_; lean_object* v_unused_1538_; lean_object* v_unused_1539_; lean_object* v_unused_1540_; 
v_unused_1527_ = lean_ctor_get(v_a_1497_, 13);
lean_dec(v_unused_1527_);
v_unused_1528_ = lean_ctor_get(v_a_1497_, 12);
lean_dec(v_unused_1528_);
v_unused_1529_ = lean_ctor_get(v_a_1497_, 11);
lean_dec(v_unused_1529_);
v_unused_1530_ = lean_ctor_get(v_a_1497_, 10);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v_a_1497_, 9);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v_a_1497_, 8);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_a_1497_, 7);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_a_1497_, 6);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v_a_1497_, 5);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_a_1497_, 4);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v_a_1497_, 3);
lean_dec(v_unused_1537_);
v_unused_1538_ = lean_ctor_get(v_a_1497_, 2);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v_a_1497_, 1);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_a_1497_, 0);
lean_dec(v_unused_1540_);
v___x_1518_ = v_a_1497_;
v_isShared_1519_ = v_isSharedCheck_1526_;
goto v_resetjp_1517_;
}
else
{
lean_dec(v_a_1497_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1526_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = lean_nat_add(v_currRecDepth_1503_, v___x_1520_);
lean_dec(v_currRecDepth_1503_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 3, v___x_1521_);
v___x_1523_ = v___x_1518_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_fileName_1500_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_fileMap_1501_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_options_1502_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_maxRecDepth_1504_);
lean_ctor_set(v_reuseFailAlloc_1525_, 5, v_ref_1505_);
lean_ctor_set(v_reuseFailAlloc_1525_, 6, v_currNamespace_1506_);
lean_ctor_set(v_reuseFailAlloc_1525_, 7, v_openDecls_1507_);
lean_ctor_set(v_reuseFailAlloc_1525_, 8, v_initHeartbeats_1508_);
lean_ctor_set(v_reuseFailAlloc_1525_, 9, v_maxHeartbeats_1509_);
lean_ctor_set(v_reuseFailAlloc_1525_, 10, v_quotContext_1510_);
lean_ctor_set(v_reuseFailAlloc_1525_, 11, v_currMacroScope_1511_);
lean_ctor_set(v_reuseFailAlloc_1525_, 12, v_cancelTk_x3f_1513_);
lean_ctor_set(v_reuseFailAlloc_1525_, 13, v_inheritedTraceOptions_1515_);
lean_ctor_set_uint8(v_reuseFailAlloc_1525_, sizeof(void*)*14, v_diag_1512_);
lean_ctor_set_uint8(v_reuseFailAlloc_1525_, sizeof(void*)*14 + 1, v_suppressElabErrors_1514_);
v___x_1523_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_apply_8(v_x_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v___x_1523_, v_a_1498_, lean_box(0));
return v___x_1524_;
}
}
}
else
{
lean_object* v___x_1541_; 
lean_dec_ref(v_x_1491_);
v___x_1541_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___boxed(lean_object* v_00_u03b1_1542_, lean_object* v_x_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth(v_00_u03b1_1542_, v_x_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(lean_object* v_a_1553_, lean_object* v_fvarId_1554_, lean_object* v___x_1555_, lean_object* v_a_x3f_1556_){
_start:
{
lean_object* v___x_1558_; lean_object* v_subst_1559_; lean_object* v_used_1560_; lean_object* v_binderRenaming_1561_; lean_object* v_funDeclInfoMap_1562_; uint8_t v_simplified_1563_; lean_object* v_visited_1564_; lean_object* v_inline_1565_; lean_object* v_inlineLocal_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1577_; 
v___x_1558_ = lean_st_ref_take(v_a_1553_);
v_subst_1559_ = lean_ctor_get(v___x_1558_, 0);
v_used_1560_ = lean_ctor_get(v___x_1558_, 1);
v_binderRenaming_1561_ = lean_ctor_get(v___x_1558_, 2);
v_funDeclInfoMap_1562_ = lean_ctor_get(v___x_1558_, 3);
v_simplified_1563_ = lean_ctor_get_uint8(v___x_1558_, sizeof(void*)*7);
v_visited_1564_ = lean_ctor_get(v___x_1558_, 4);
v_inline_1565_ = lean_ctor_get(v___x_1558_, 5);
v_inlineLocal_1566_ = lean_ctor_get(v___x_1558_, 6);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1568_ = v___x_1558_;
v_isShared_1569_ = v_isSharedCheck_1577_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_inlineLocal_1566_);
lean_inc(v_inline_1565_);
lean_inc(v_visited_1564_);
lean_inc(v_funDeclInfoMap_1562_);
lean_inc(v_binderRenaming_1561_);
lean_inc(v_used_1560_);
lean_inc(v_subst_1559_);
lean_dec(v___x_1558_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1577_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1570_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(v_funDeclInfoMap_1562_, v_fvarId_1554_, v___x_1555_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 3, v___x_1570_);
v___x_1572_ = v___x_1568_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_subst_1559_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_used_1560_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v_binderRenaming_1561_);
lean_ctor_set(v_reuseFailAlloc_1576_, 3, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1576_, 4, v_visited_1564_);
lean_ctor_set(v_reuseFailAlloc_1576_, 5, v_inline_1565_);
lean_ctor_set(v_reuseFailAlloc_1576_, 6, v_inlineLocal_1566_);
lean_ctor_set_uint8(v_reuseFailAlloc_1576_, sizeof(void*)*7, v_simplified_1563_);
v___x_1572_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = lean_st_ref_set(v_a_1553_, v___x_1572_);
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0___boxed(lean_object* v_a_1578_, lean_object* v_fvarId_1579_, lean_object* v___x_1580_, lean_object* v_a_x3f_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1578_, v_fvarId_1579_, v___x_1580_, v_a_x3f_1581_);
lean_dec(v_a_x3f_1581_);
lean_dec(v_a_1578_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(lean_object* v_a_1584_, lean_object* v_x_1585_){
_start:
{
if (lean_obj_tag(v_x_1585_) == 0)
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_box(0);
return v___x_1586_;
}
else
{
lean_object* v_key_1587_; lean_object* v_value_1588_; lean_object* v_tail_1589_; uint8_t v___x_1590_; 
v_key_1587_ = lean_ctor_get(v_x_1585_, 0);
v_value_1588_ = lean_ctor_get(v_x_1585_, 1);
v_tail_1589_ = lean_ctor_get(v_x_1585_, 2);
v___x_1590_ = l_Lean_instBEqFVarId_beq(v_key_1587_, v_a_1584_);
if (v___x_1590_ == 0)
{
v_x_1585_ = v_tail_1589_;
goto _start;
}
else
{
lean_object* v___x_1592_; 
lean_inc(v_value_1588_);
v___x_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1592_, 0, v_value_1588_);
return v___x_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg___boxed(lean_object* v_a_1593_, lean_object* v_x_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1593_, v_x_1594_);
lean_dec(v_x_1594_);
lean_dec(v_a_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(lean_object* v_m_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_buckets_1598_; lean_object* v___x_1599_; uint64_t v___x_1600_; uint64_t v___x_1601_; uint64_t v___x_1602_; uint64_t v_fold_1603_; uint64_t v___x_1604_; uint64_t v___x_1605_; uint64_t v___x_1606_; size_t v___x_1607_; size_t v___x_1608_; size_t v___x_1609_; size_t v___x_1610_; size_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v_buckets_1598_ = lean_ctor_get(v_m_1596_, 1);
v___x_1599_ = lean_array_get_size(v_buckets_1598_);
v___x_1600_ = l_Lean_instHashableFVarId_hash(v_a_1597_);
v___x_1601_ = 32ULL;
v___x_1602_ = lean_uint64_shift_right(v___x_1600_, v___x_1601_);
v_fold_1603_ = lean_uint64_xor(v___x_1600_, v___x_1602_);
v___x_1604_ = 16ULL;
v___x_1605_ = lean_uint64_shift_right(v_fold_1603_, v___x_1604_);
v___x_1606_ = lean_uint64_xor(v_fold_1603_, v___x_1605_);
v___x_1607_ = lean_uint64_to_usize(v___x_1606_);
v___x_1608_ = lean_usize_of_nat(v___x_1599_);
v___x_1609_ = ((size_t)1ULL);
v___x_1610_ = lean_usize_sub(v___x_1608_, v___x_1609_);
v___x_1611_ = lean_usize_land(v___x_1607_, v___x_1610_);
v___x_1612_ = lean_array_uget_borrowed(v_buckets_1598_, v___x_1611_);
v___x_1613_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1597_, v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg___boxed(lean_object* v_m_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_1614_, v_a_1615_);
lean_dec(v_a_1615_);
lean_dec_ref(v_m_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(lean_object* v_fvarId_1617_, lean_object* v_x_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v___x_1627_; lean_object* v_funDeclInfoMap_1628_; lean_object* v___x_1629_; lean_object* v_a_1631_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1627_ = lean_st_ref_get(v_a_1620_);
v_funDeclInfoMap_1628_ = lean_ctor_get(v___x_1627_, 3);
lean_inc_ref(v_funDeclInfoMap_1628_);
lean_dec(v___x_1627_);
v___x_1629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_1628_, v_fvarId_1617_);
lean_dec_ref(v_funDeclInfoMap_1628_);
lean_inc(v_fvarId_1617_);
v___x_1642_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_1617_, v_a_1620_);
lean_dec_ref(v___x_1642_);
lean_inc(v_a_1620_);
v___x_1643_ = lean_apply_8(v_x_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, lean_box(0));
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1660_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1660_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1660_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
lean_inc(v_a_1644_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 1);
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v___x_1650_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1620_, v_fvarId_1617_, v___x_1629_, v___x_1649_);
lean_dec_ref(v___x_1649_);
lean_dec(v_a_1620_);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v___x_1650_, 0);
lean_dec(v_unused_1658_);
v___x_1652_ = v___x_1650_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_dec(v___x_1650_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v_a_1644_);
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1644_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
else
{
lean_object* v_a_1661_; 
v_a_1661_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1661_);
lean_dec_ref(v___x_1643_);
v_a_1631_ = v_a_1661_;
goto v___jp_1630_;
}
v___jp_1630_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
v___x_1632_ = lean_box(0);
v___x_1633_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1620_, v_fvarId_1617_, v___x_1629_, v___x_1632_);
lean_dec(v_a_1620_);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; 
v_unused_1641_ = lean_ctor_get(v___x_1633_, 0);
lean_dec(v_unused_1641_);
v___x_1635_ = v___x_1633_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_dec(v___x_1633_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 1);
lean_ctor_set(v___x_1635_, 0, v_a_1631_);
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1631_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___boxed(lean_object* v_fvarId_1662_, lean_object* v_x_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1662_, v_x_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object* v_00_u03b1_1673_, lean_object* v_fvarId_1674_, lean_object* v_x_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1674_, v_x_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___boxed(lean_object* v_00_u03b1_1685_, lean_object* v_fvarId_1686_, lean_object* v_x_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline(v_00_u03b1_1685_, v_fvarId_1686_, v_x_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(lean_object* v_00_u03b2_1697_, lean_object* v_m_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_1698_, v_a_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___boxed(lean_object* v_00_u03b2_1701_, lean_object* v_m_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(v_00_u03b2_1701_, v_m_1702_, v_a_1703_);
lean_dec(v_a_1703_);
lean_dec_ref(v_m_1702_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(lean_object* v_00_u03b2_1705_, lean_object* v_a_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1706_, v_x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1709_, lean_object* v_a_1710_, lean_object* v_x_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(v_00_u03b2_1709_, v_a_1710_, v_x_1711_);
lean_dec(v_x_1711_);
lean_dec(v_a_1710_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object* v_fvarId_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1724_; lean_object* v_funDeclInfoMap_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_st_ref_get(v_a_1714_);
v_funDeclInfoMap_1725_ = lean_ctor_get(v___x_1724_, 3);
lean_inc_ref(v_funDeclInfoMap_1725_);
lean_dec(v___x_1724_);
v___x_1726_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_1725_, v_fvarId_1713_);
lean_dec_ref(v_funDeclInfoMap_1725_);
if (lean_obj_tag(v___x_1726_) == 1)
{
lean_object* v_val_1727_; uint8_t v___x_1728_; 
v_val_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_val_1727_);
lean_dec_ref(v___x_1726_);
v___x_1728_ = lean_unbox(v_val_1727_);
lean_dec(v_val_1727_);
switch(v___x_1728_)
{
case 0:
{
goto v___jp_1720_;
}
case 2:
{
goto v___jp_1720_;
}
default: 
{
goto v___jp_1716_;
}
}
}
else
{
lean_dec(v___x_1726_);
goto v___jp_1716_;
}
v___jp_1716_:
{
uint8_t v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = 0;
v___x_1718_ = lean_box(v___x_1717_);
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
return v___x_1719_;
}
v___jp_1720_:
{
uint8_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = 1;
v___x_1722_ = lean_box(v___x_1721_);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg___boxed(lean_object* v_fvarId_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec(v_fvarId_1729_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object* v_fvarId_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1733_, v_a_1735_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object* v_fvarId_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(v_fvarId_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
lean_dec(v_a_1750_);
lean_dec_ref(v_a_1749_);
lean_dec(v_a_1748_);
lean_dec_ref(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_fvarId_1743_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg(lean_object* v_code_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_1754_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1768_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1768_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1768_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v_smallThreshold_1761_; uint8_t v___x_1762_; uint8_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v_smallThreshold_1761_ = lean_ctor_get(v_a_1757_, 0);
lean_inc(v_smallThreshold_1761_);
lean_dec(v_a_1757_);
v___x_1762_ = 0;
v___x_1763_ = l_Lean_Compiler_LCNF_Code_sizeLe(v___x_1762_, v_code_1753_, v_smallThreshold_1761_);
lean_dec(v_smallThreshold_1761_);
v___x_1764_ = lean_box(v___x_1763_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1764_);
v___x_1766_ = v___x_1759_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
v_a_1769_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1756_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1756_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg___boxed(lean_object* v_code_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1777_, v_a_1778_);
lean_dec_ref(v_a_1778_);
lean_dec_ref(v_code_1777_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object* v_code_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1781_, v_a_1785_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object* v_code_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Compiler_LCNF_Simp_isSmall(v_code_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec_ref(v_code_1791_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object* v_decl_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v_fvarId_1805_; lean_object* v_value_1806_; lean_object* v___x_1807_; lean_object* v_a_1808_; uint8_t v___x_1809_; 
v_fvarId_1805_ = lean_ctor_get(v_decl_1801_, 0);
v_value_1806_ = lean_ctor_get(v_decl_1801_, 4);
v___x_1807_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1805_, v_a_1802_);
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
v___x_1809_ = lean_unbox(v_a_1808_);
lean_dec(v_a_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; 
lean_dec_ref(v___x_1807_);
v___x_1810_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_value_1806_, v_a_1803_);
return v___x_1810_;
}
else
{
return v___x_1807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg___boxed(lean_object* v_decl_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1811_, v_a_1812_, v_a_1813_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_decl_1811_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object* v_decl_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1816_, v_a_1818_, v_a_1820_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object* v_decl_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(v_decl_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec_ref(v_decl_1826_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(lean_object* v_a_1836_, lean_object* v_b_1837_, lean_object* v_x_1838_){
_start:
{
if (lean_obj_tag(v_x_1838_) == 0)
{
lean_dec(v_b_1837_);
lean_dec(v_a_1836_);
return v_x_1838_;
}
else
{
lean_object* v_key_1839_; lean_object* v_value_1840_; lean_object* v_tail_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1853_; 
v_key_1839_ = lean_ctor_get(v_x_1838_, 0);
v_value_1840_ = lean_ctor_get(v_x_1838_, 1);
v_tail_1841_ = lean_ctor_get(v_x_1838_, 2);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_x_1838_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1843_ = v_x_1838_;
v_isShared_1844_ = v_isSharedCheck_1853_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_tail_1841_);
lean_inc(v_value_1840_);
lean_inc(v_key_1839_);
lean_dec(v_x_1838_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1853_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
uint8_t v___x_1845_; 
v___x_1845_ = l_Lean_instBEqFVarId_beq(v_key_1839_, v_a_1836_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_1836_, v_b_1837_, v_tail_1841_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 2, v___x_1846_);
v___x_1848_ = v___x_1843_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_key_1839_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_value_1840_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
else
{
lean_object* v___x_1851_; 
lean_dec(v_value_1840_);
lean_dec(v_key_1839_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v_b_1837_);
lean_ctor_set(v___x_1843_, 0, v_a_1836_);
v___x_1851_ = v___x_1843_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1836_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_b_1837_);
lean_ctor_set(v_reuseFailAlloc_1852_, 2, v_tail_1841_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(lean_object* v_a_1854_, lean_object* v_x_1855_){
_start:
{
if (lean_obj_tag(v_x_1855_) == 0)
{
uint8_t v___x_1856_; 
v___x_1856_ = 0;
return v___x_1856_;
}
else
{
lean_object* v_key_1857_; lean_object* v_tail_1858_; uint8_t v___x_1859_; 
v_key_1857_ = lean_ctor_get(v_x_1855_, 0);
v_tail_1858_ = lean_ctor_get(v_x_1855_, 2);
v___x_1859_ = l_Lean_instBEqFVarId_beq(v_key_1857_, v_a_1854_);
if (v___x_1859_ == 0)
{
v_x_1855_ = v_tail_1858_;
goto _start;
}
else
{
return v___x_1859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg___boxed(lean_object* v_a_1861_, lean_object* v_x_1862_){
_start:
{
uint8_t v_res_1863_; lean_object* v_r_1864_; 
v_res_1863_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1861_, v_x_1862_);
lean_dec(v_x_1862_);
lean_dec(v_a_1861_);
v_r_1864_ = lean_box(v_res_1863_);
return v_r_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_1865_, lean_object* v_x_1866_){
_start:
{
if (lean_obj_tag(v_x_1866_) == 0)
{
return v_x_1865_;
}
else
{
lean_object* v_key_1867_; lean_object* v_value_1868_; lean_object* v_tail_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1892_; 
v_key_1867_ = lean_ctor_get(v_x_1866_, 0);
v_value_1868_ = lean_ctor_get(v_x_1866_, 1);
v_tail_1869_ = lean_ctor_get(v_x_1866_, 2);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_x_1866_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1871_ = v_x_1866_;
v_isShared_1872_ = v_isSharedCheck_1892_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_tail_1869_);
lean_inc(v_value_1868_);
lean_inc(v_key_1867_);
lean_dec(v_x_1866_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1892_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; uint64_t v___x_1874_; uint64_t v___x_1875_; uint64_t v___x_1876_; uint64_t v_fold_1877_; uint64_t v___x_1878_; uint64_t v___x_1879_; uint64_t v___x_1880_; size_t v___x_1881_; size_t v___x_1882_; size_t v___x_1883_; size_t v___x_1884_; size_t v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1873_ = lean_array_get_size(v_x_1865_);
v___x_1874_ = l_Lean_instHashableFVarId_hash(v_key_1867_);
v___x_1875_ = 32ULL;
v___x_1876_ = lean_uint64_shift_right(v___x_1874_, v___x_1875_);
v_fold_1877_ = lean_uint64_xor(v___x_1874_, v___x_1876_);
v___x_1878_ = 16ULL;
v___x_1879_ = lean_uint64_shift_right(v_fold_1877_, v___x_1878_);
v___x_1880_ = lean_uint64_xor(v_fold_1877_, v___x_1879_);
v___x_1881_ = lean_uint64_to_usize(v___x_1880_);
v___x_1882_ = lean_usize_of_nat(v___x_1873_);
v___x_1883_ = ((size_t)1ULL);
v___x_1884_ = lean_usize_sub(v___x_1882_, v___x_1883_);
v___x_1885_ = lean_usize_land(v___x_1881_, v___x_1884_);
v___x_1886_ = lean_array_uget_borrowed(v_x_1865_, v___x_1885_);
lean_inc(v___x_1886_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 2, v___x_1886_);
v___x_1888_ = v___x_1871_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_key_1867_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_value_1868_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_array_uset(v_x_1865_, v___x_1885_, v___x_1888_);
v_x_1865_ = v___x_1889_;
v_x_1866_ = v_tail_1869_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1893_, lean_object* v_source_1894_, lean_object* v_target_1895_){
_start:
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = lean_array_get_size(v_source_1894_);
v___x_1897_ = lean_nat_dec_lt(v_i_1893_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_dec_ref(v_source_1894_);
lean_dec(v_i_1893_);
return v_target_1895_;
}
else
{
lean_object* v_es_1898_; lean_object* v___x_1899_; lean_object* v_source_1900_; lean_object* v_target_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v_es_1898_ = lean_array_fget(v_source_1894_, v_i_1893_);
v___x_1899_ = lean_box(0);
v_source_1900_ = lean_array_fset(v_source_1894_, v_i_1893_, v___x_1899_);
v_target_1901_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(v_target_1895_, v_es_1898_);
v___x_1902_ = lean_unsigned_to_nat(1u);
v___x_1903_ = lean_nat_add(v_i_1893_, v___x_1902_);
lean_dec(v_i_1893_);
v_i_1893_ = v___x_1903_;
v_source_1894_ = v_source_1900_;
v_target_1895_ = v_target_1901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(lean_object* v_data_1905_){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_nbuckets_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1906_ = lean_array_get_size(v_data_1905_);
v___x_1907_ = lean_unsigned_to_nat(2u);
v_nbuckets_1908_ = lean_nat_mul(v___x_1906_, v___x_1907_);
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = lean_box(0);
v___x_1911_ = lean_mk_array(v_nbuckets_1908_, v___x_1910_);
v___x_1912_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(v___x_1909_, v_data_1905_, v___x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(lean_object* v_m_1913_, lean_object* v_a_1914_, lean_object* v_b_1915_){
_start:
{
lean_object* v_size_1916_; lean_object* v_buckets_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1960_; 
v_size_1916_ = lean_ctor_get(v_m_1913_, 0);
v_buckets_1917_ = lean_ctor_get(v_m_1913_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_m_1913_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1919_ = v_m_1913_;
v_isShared_1920_ = v_isSharedCheck_1960_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_buckets_1917_);
lean_inc(v_size_1916_);
lean_dec(v_m_1913_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1960_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; uint64_t v___x_1922_; uint64_t v___x_1923_; uint64_t v___x_1924_; uint64_t v_fold_1925_; uint64_t v___x_1926_; uint64_t v___x_1927_; uint64_t v___x_1928_; size_t v___x_1929_; size_t v___x_1930_; size_t v___x_1931_; size_t v___x_1932_; size_t v___x_1933_; lean_object* v_bkt_1934_; uint8_t v___x_1935_; 
v___x_1921_ = lean_array_get_size(v_buckets_1917_);
v___x_1922_ = l_Lean_instHashableFVarId_hash(v_a_1914_);
v___x_1923_ = 32ULL;
v___x_1924_ = lean_uint64_shift_right(v___x_1922_, v___x_1923_);
v_fold_1925_ = lean_uint64_xor(v___x_1922_, v___x_1924_);
v___x_1926_ = 16ULL;
v___x_1927_ = lean_uint64_shift_right(v_fold_1925_, v___x_1926_);
v___x_1928_ = lean_uint64_xor(v_fold_1925_, v___x_1927_);
v___x_1929_ = lean_uint64_to_usize(v___x_1928_);
v___x_1930_ = lean_usize_of_nat(v___x_1921_);
v___x_1931_ = ((size_t)1ULL);
v___x_1932_ = lean_usize_sub(v___x_1930_, v___x_1931_);
v___x_1933_ = lean_usize_land(v___x_1929_, v___x_1932_);
v_bkt_1934_ = lean_array_uget_borrowed(v_buckets_1917_, v___x_1933_);
v___x_1935_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1914_, v_bkt_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v_size_x27_1937_; lean_object* v___x_1938_; lean_object* v_buckets_x27_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1936_ = lean_unsigned_to_nat(1u);
v_size_x27_1937_ = lean_nat_add(v_size_1916_, v___x_1936_);
lean_dec(v_size_1916_);
lean_inc(v_bkt_1934_);
v___x_1938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1938_, 0, v_a_1914_);
lean_ctor_set(v___x_1938_, 1, v_b_1915_);
lean_ctor_set(v___x_1938_, 2, v_bkt_1934_);
v_buckets_x27_1939_ = lean_array_uset(v_buckets_1917_, v___x_1933_, v___x_1938_);
v___x_1940_ = lean_unsigned_to_nat(4u);
v___x_1941_ = lean_nat_mul(v_size_x27_1937_, v___x_1940_);
v___x_1942_ = lean_unsigned_to_nat(3u);
v___x_1943_ = lean_nat_div(v___x_1941_, v___x_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_array_get_size(v_buckets_x27_1939_);
v___x_1945_ = lean_nat_dec_le(v___x_1943_, v___x_1944_);
lean_dec(v___x_1943_);
if (v___x_1945_ == 0)
{
lean_object* v_val_1946_; lean_object* v___x_1948_; 
v_val_1946_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(v_buckets_x27_1939_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v_val_1946_);
lean_ctor_set(v___x_1919_, 0, v_size_x27_1937_);
v___x_1948_ = v___x_1919_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_size_x27_1937_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_val_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
else
{
lean_object* v___x_1951_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v_buckets_x27_1939_);
lean_ctor_set(v___x_1919_, 0, v_size_x27_1937_);
v___x_1951_ = v___x_1919_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_size_x27_1937_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_buckets_x27_1939_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
else
{
lean_object* v___x_1953_; lean_object* v_buckets_x27_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1958_; 
lean_inc(v_bkt_1934_);
v___x_1953_ = lean_box(0);
v_buckets_x27_1954_ = lean_array_uset(v_buckets_1917_, v___x_1933_, v___x_1953_);
v___x_1955_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_1914_, v_b_1915_, v_bkt_1934_);
v___x_1956_ = lean_array_uset(v_buckets_x27_1954_, v___x_1933_, v___x_1955_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v___x_1956_);
v___x_1958_ = v___x_1919_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_size_1916_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(lean_object* v_as_1961_, size_t v_sz_1962_, size_t v_i_1963_, lean_object* v_b_1964_){
_start:
{
uint8_t v___x_1966_; 
v___x_1966_ = lean_usize_dec_lt(v_i_1963_, v_sz_1962_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_b_1964_);
return v___x_1967_;
}
else
{
lean_object* v_snd_1968_; lean_object* v_fst_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2003_; 
v_snd_1968_ = lean_ctor_get(v_b_1964_, 1);
v_fst_1969_ = lean_ctor_get(v_b_1964_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_b_1964_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1971_ = v_b_1964_;
v_isShared_1972_ = v_isSharedCheck_2003_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_snd_1968_);
lean_inc(v_fst_1969_);
lean_dec(v_b_1964_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2003_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_array_1973_; lean_object* v_start_1974_; lean_object* v_stop_1975_; uint8_t v___x_1976_; 
v_array_1973_ = lean_ctor_get(v_snd_1968_, 0);
v_start_1974_ = lean_ctor_get(v_snd_1968_, 1);
v_stop_1975_ = lean_ctor_get(v_snd_1968_, 2);
v___x_1976_ = lean_nat_dec_lt(v_start_1974_, v_stop_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1978_; 
if (v_isShared_1972_ == 0)
{
v___x_1978_ = v___x_1971_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_fst_1969_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_snd_1968_);
v___x_1978_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
return v___x_1979_;
}
}
else
{
lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1999_; 
lean_inc(v_stop_1975_);
lean_inc(v_start_1974_);
lean_inc_ref(v_array_1973_);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_snd_1968_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; lean_object* v_unused_2001_; lean_object* v_unused_2002_; 
v_unused_2000_ = lean_ctor_get(v_snd_1968_, 2);
lean_dec(v_unused_2000_);
v_unused_2001_ = lean_ctor_get(v_snd_1968_, 1);
lean_dec(v_unused_2001_);
v_unused_2002_ = lean_ctor_get(v_snd_1968_, 0);
lean_dec(v_unused_2002_);
v___x_1982_ = v_snd_1968_;
v_isShared_1983_ = v_isSharedCheck_1999_;
goto v_resetjp_1981_;
}
else
{
lean_dec(v_snd_1968_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1999_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v_a_1984_; lean_object* v_fvarId_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v_a_1984_ = lean_array_uget_borrowed(v_as_1961_, v_i_1963_);
v_fvarId_1985_ = lean_ctor_get(v_a_1984_, 0);
v___x_1986_ = lean_array_fget(v_array_1973_, v_start_1974_);
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = lean_nat_add(v_start_1974_, v___x_1987_);
lean_dec(v_start_1974_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 1, v___x_1988_);
v___x_1990_ = v___x_1982_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_array_1973_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1998_, 2, v_stop_1975_);
v___x_1990_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
lean_inc(v_fvarId_1985_);
v___x_1991_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_fst_1969_, v_fvarId_1985_, v___x_1986_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 1, v___x_1990_);
lean_ctor_set(v___x_1971_, 0, v___x_1991_);
v___x_1993_ = v___x_1971_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___x_1990_);
v___x_1993_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
size_t v___x_1994_; size_t v___x_1995_; 
v___x_1994_ = ((size_t)1ULL);
v___x_1995_ = lean_usize_add(v_i_1963_, v___x_1994_);
v_i_1963_ = v___x_1995_;
v_b_1964_ = v___x_1993_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg___boxed(lean_object* v_as_2004_, lean_object* v_sz_2005_, lean_object* v_i_2006_, lean_object* v_b_2007_, lean_object* v___y_2008_){
_start:
{
size_t v_sz_boxed_2009_; size_t v_i_boxed_2010_; lean_object* v_res_2011_; 
v_sz_boxed_2009_ = lean_unbox_usize(v_sz_2005_);
lean_dec(v_sz_2005_);
v_i_boxed_2010_ = lean_unbox_usize(v_i_2006_);
lean_dec(v_i_2006_);
v_res_2011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_2004_, v_sz_boxed_2009_, v_i_boxed_2010_, v_b_2007_);
lean_dec_ref(v_as_2004_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object* v_params_2012_, lean_object* v_code_2013_, lean_object* v_args_2014_, uint8_t v_mustInline_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___x_2024_; lean_object* v_subst_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; size_t v_sz_2029_; size_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2024_ = lean_unsigned_to_nat(0u);
v_subst_2025_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1);
v___x_2026_ = lean_array_get_size(v_args_2014_);
v___x_2027_ = l_Array_toSubarray___redArg(v_args_2014_, v___x_2024_, v___x_2026_);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v_subst_2025_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v_sz_2029_ = lean_array_size(v_params_2012_);
v___x_2030_ = ((size_t)0ULL);
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_params_2012_, v_sz_2029_, v___x_2030_, v___x_2028_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v_fst_2033_; uint8_t v___x_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref(v___x_2031_);
v_fst_2033_ = lean_ctor_get(v_a_2032_, 0);
lean_inc(v_fst_2033_);
lean_dec(v_a_2032_);
v___x_2034_ = 0;
v___x_2035_ = 0;
lean_inc(v_a_2022_);
lean_inc_ref(v_a_2021_);
lean_inc(v_a_2020_);
lean_inc_ref(v_a_2019_);
v___x_2036_ = l_Lean_Compiler_LCNF_Code_internalize(v___x_2034_, v_code_2013_, v_fst_2033_, v___x_2035_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref(v___x_2036_);
lean_inc(v_a_2037_);
v___x_2038_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_a_2037_, v_mustInline_2015_, v_a_2017_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v___x_2038_, 0);
lean_dec(v_unused_2046_);
v___x_2040_ = v___x_2038_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_dec(v___x_2038_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v_a_2037_);
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2037_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_a_2037_);
v_a_2047_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2038_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2038_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
return v___x_2036_;
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec_ref(v_code_2013_);
v_a_2055_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2031_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2031_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object* v_params_2063_, lean_object* v_code_2064_, lean_object* v_args_2065_, lean_object* v_mustInline_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
uint8_t v_mustInline_boxed_2075_; lean_object* v_res_2076_; 
v_mustInline_boxed_2075_ = lean_unbox(v_mustInline_2066_);
v_res_2076_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_2063_, v_code_2064_, v_args_2065_, v_mustInline_boxed_2075_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec_ref(v_a_2069_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
lean_dec_ref(v_params_2063_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0(lean_object* v_00_u03b2_2077_, lean_object* v_m_2078_, lean_object* v_a_2079_, lean_object* v_b_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_m_2078_, v_a_2079_, v_b_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(lean_object* v_as_2082_, size_t v_sz_2083_, size_t v_i_2084_, lean_object* v_b_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_2082_, v_sz_2083_, v_i_2084_, v_b_2085_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___boxed(lean_object* v_as_2095_, lean_object* v_sz_2096_, lean_object* v_i_2097_, lean_object* v_b_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
size_t v_sz_boxed_2107_; size_t v_i_boxed_2108_; lean_object* v_res_2109_; 
v_sz_boxed_2107_ = lean_unbox_usize(v_sz_2096_);
lean_dec(v_sz_2096_);
v_i_boxed_2108_ = lean_unbox_usize(v_i_2097_);
lean_dec(v_i_2097_);
v_res_2109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(v_as_2095_, v_sz_boxed_2107_, v_i_boxed_2108_, v_b_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec_ref(v_as_2095_);
return v_res_2109_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(lean_object* v_00_u03b2_2110_, lean_object* v_a_2111_, lean_object* v_x_2112_){
_start:
{
uint8_t v___x_2113_; 
v___x_2113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_2111_, v_x_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2114_, lean_object* v_a_2115_, lean_object* v_x_2116_){
_start:
{
uint8_t v_res_2117_; lean_object* v_r_2118_; 
v_res_2117_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(v_00_u03b2_2114_, v_a_2115_, v_x_2116_);
lean_dec(v_x_2116_);
lean_dec(v_a_2115_);
v_r_2118_ = lean_box(v_res_2117_);
return v_r_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1(lean_object* v_00_u03b2_2119_, lean_object* v_data_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(v_data_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2(lean_object* v_00_u03b2_2122_, lean_object* v_a_2123_, lean_object* v_b_2124_, lean_object* v_x_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_2123_, v_b_2124_, v_x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2127_, lean_object* v_i_2128_, lean_object* v_source_2129_, lean_object* v_target_2130_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(v_i_2128_, v_source_2129_, v_target_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2133_, v_x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object* v_decl_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
uint8_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = 0;
v___x_2141_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2140_, v_decl_2136_, v_a_2138_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v___x_2142_; 
lean_dec_ref(v___x_2141_);
v___x_2142_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2137_);
return v___x_2142_;
}
else
{
return v___x_2141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg___boxed(lean_object* v_decl_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2143_, v_a_2144_, v_a_2145_);
lean_dec(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_decl_2143_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object* v_decl_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2148_, v_a_2150_, v_a_2153_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object* v_decl_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(v_decl_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec_ref(v_decl_2158_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object* v_decl_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
uint8_t v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = 0;
v___x_2173_ = 1;
v___x_2174_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_2172_, v_decl_2168_, v___x_2173_, v_a_2170_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v___x_2175_; 
lean_dec_ref(v___x_2174_);
v___x_2175_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2169_);
return v___x_2175_;
}
else
{
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg___boxed(lean_object* v_decl_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2176_, v_a_2177_, v_a_2178_);
lean_dec(v_a_2178_);
lean_dec(v_a_2177_);
lean_dec_ref(v_decl_2176_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object* v_decl_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2181_, v_a_2183_, v_a_2186_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object* v_decl_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(v_decl_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
lean_dec_ref(v_decl_2191_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object* v_fvarId_2201_, lean_object* v_fvarId_x27_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v___x_2209_; lean_object* v_subst_2210_; lean_object* v_used_2211_; lean_object* v_binderRenaming_2212_; lean_object* v_funDeclInfoMap_2213_; uint8_t v_simplified_2214_; lean_object* v_visited_2215_; lean_object* v_inline_2216_; lean_object* v_inlineLocal_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2287_; 
v___x_2209_ = lean_st_ref_take(v_a_2203_);
v_subst_2210_ = lean_ctor_get(v___x_2209_, 0);
v_used_2211_ = lean_ctor_get(v___x_2209_, 1);
v_binderRenaming_2212_ = lean_ctor_get(v___x_2209_, 2);
v_funDeclInfoMap_2213_ = lean_ctor_get(v___x_2209_, 3);
v_simplified_2214_ = lean_ctor_get_uint8(v___x_2209_, sizeof(void*)*7);
v_visited_2215_ = lean_ctor_get(v___x_2209_, 4);
v_inline_2216_ = lean_ctor_get(v___x_2209_, 5);
v_inlineLocal_2217_ = lean_ctor_get(v___x_2209_, 6);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2219_ = v___x_2209_;
v_isShared_2220_ = v_isSharedCheck_2287_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_inlineLocal_2217_);
lean_inc(v_inline_2216_);
lean_inc(v_visited_2215_);
lean_inc(v_funDeclInfoMap_2213_);
lean_inc(v_binderRenaming_2212_);
lean_inc(v_used_2211_);
lean_inc(v_subst_2210_);
lean_dec(v___x_2209_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2287_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
lean_inc(v_fvarId_x27_2202_);
v___x_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2221_, 0, v_fvarId_x27_2202_);
lean_inc(v_fvarId_2201_);
v___x_2222_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_subst_2210_, v_fvarId_2201_, v___x_2221_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v___x_2222_);
v___x_2224_ = v___x_2219_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_used_2211_);
lean_ctor_set(v_reuseFailAlloc_2286_, 2, v_binderRenaming_2212_);
lean_ctor_set(v_reuseFailAlloc_2286_, 3, v_funDeclInfoMap_2213_);
lean_ctor_set(v_reuseFailAlloc_2286_, 4, v_visited_2215_);
lean_ctor_set(v_reuseFailAlloc_2286_, 5, v_inline_2216_);
lean_ctor_set(v_reuseFailAlloc_2286_, 6, v_inlineLocal_2217_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*7, v_simplified_2214_);
v___x_2224_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_st_ref_set(v_a_2203_, v___x_2224_);
v___x_2226_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_2201_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2277_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2277_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2277_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
uint8_t v___x_2231_; 
v___x_2231_ = l_Lean_Name_isInternal(v_a_2227_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; 
lean_del_object(v___x_2229_);
lean_inc(v_fvarId_x27_2202_);
v___x_2232_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_x27_2202_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2264_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2264_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2264_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
uint8_t v___x_2237_; 
v___x_2237_ = l_Lean_Name_isInternal(v_a_2233_);
lean_dec(v_a_2233_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
lean_dec(v_a_2227_);
lean_dec(v_fvarId_x27_2202_);
v___x_2238_ = lean_box(0);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2238_);
v___x_2240_ = v___x_2235_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
else
{
lean_object* v___x_2242_; lean_object* v_subst_2243_; lean_object* v_used_2244_; lean_object* v_binderRenaming_2245_; lean_object* v_funDeclInfoMap_2246_; uint8_t v_simplified_2247_; lean_object* v_visited_2248_; lean_object* v_inline_2249_; lean_object* v_inlineLocal_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2263_; 
v___x_2242_ = lean_st_ref_take(v_a_2203_);
v_subst_2243_ = lean_ctor_get(v___x_2242_, 0);
v_used_2244_ = lean_ctor_get(v___x_2242_, 1);
v_binderRenaming_2245_ = lean_ctor_get(v___x_2242_, 2);
v_funDeclInfoMap_2246_ = lean_ctor_get(v___x_2242_, 3);
v_simplified_2247_ = lean_ctor_get_uint8(v___x_2242_, sizeof(void*)*7);
v_visited_2248_ = lean_ctor_get(v___x_2242_, 4);
v_inline_2249_ = lean_ctor_get(v___x_2242_, 5);
v_inlineLocal_2250_ = lean_ctor_get(v___x_2242_, 6);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2252_ = v___x_2242_;
v_isShared_2253_ = v_isSharedCheck_2263_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_inlineLocal_2250_);
lean_inc(v_inline_2249_);
lean_inc(v_visited_2248_);
lean_inc(v_funDeclInfoMap_2246_);
lean_inc(v_binderRenaming_2245_);
lean_inc(v_used_2244_);
lean_inc(v_subst_2243_);
lean_dec(v___x_2242_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2263_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2254_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_x27_2202_, v_a_2227_, v_binderRenaming_2245_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 2, v___x_2254_);
v___x_2256_ = v___x_2252_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_subst_2243_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_used_2244_);
lean_ctor_set(v_reuseFailAlloc_2262_, 2, v___x_2254_);
lean_ctor_set(v_reuseFailAlloc_2262_, 3, v_funDeclInfoMap_2246_);
lean_ctor_set(v_reuseFailAlloc_2262_, 4, v_visited_2248_);
lean_ctor_set(v_reuseFailAlloc_2262_, 5, v_inline_2249_);
lean_ctor_set(v_reuseFailAlloc_2262_, 6, v_inlineLocal_2250_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, sizeof(void*)*7, v_simplified_2247_);
v___x_2256_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2257_ = lean_st_ref_set(v_a_2203_, v___x_2256_);
v___x_2258_ = lean_box(0);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2258_);
v___x_2260_ = v___x_2235_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_a_2227_);
lean_dec(v_fvarId_x27_2202_);
v_a_2265_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2232_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2232_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2275_; 
lean_dec(v_a_2227_);
lean_dec(v_fvarId_x27_2202_);
v___x_2273_ = lean_box(0);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2273_);
v___x_2275_ = v___x_2229_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_fvarId_x27_2202_);
v_a_2278_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2226_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2226_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg___boxed(lean_object* v_fvarId_2288_, lean_object* v_fvarId_x27_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2288_, v_fvarId_x27_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object* v_fvarId_2297_, lean_object* v_fvarId_x27_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2297_, v_fvarId_x27_2298_, v_a_2300_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___boxed(lean_object* v_fvarId_2308_, lean_object* v_fvarId_x27_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst(v_fvarId_2308_, v_fvarId_x27_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
return v_res_2318_;
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
