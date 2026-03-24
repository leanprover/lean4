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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
v___x_92_ = l_StateRefT_x27_instMonad___redArg(v___x_91_);
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
v___x_117_ = l_StateRefT_x27_instMonad___redArg(v___x_116_);
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
size_t v_x_7465__boxed_925_; lean_object* v_res_926_; 
v_x_7465__boxed_925_ = lean_unbox_usize(v_x_923_);
lean_dec(v_x_923_);
v_res_926_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_922_, v_x_7465__boxed_925_, v_x_924_);
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
lean_inc_ref(v_a_958_);
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
lean_inc_ref(v_a_958_);
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
v___x_1052_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_1047_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = lean_unbox(v_a_1053_);
lean_dec(v_a_1053_);
lean_inc(v_declName_957_);
v___x_1055_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_957_, v___x_1054_, v___y_1050_, v___y_1049_);
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
v___y_969_ = v___y_1046_;
v___y_970_ = v___y_1044_;
v___y_971_ = v___y_1048_;
v___y_972_ = v___y_1047_;
v___y_973_ = v___y_1045_;
v___y_974_ = v___y_1050_;
v___y_975_ = v___y_1049_;
goto v___jp_966_;
}
else
{
uint8_t v___x_1061_; 
lean_dec(v_a_1056_);
v___x_1061_ = 0;
v___y_967_ = v___x_1058_;
v_inlineIfReduce_968_ = v___x_1061_;
v___y_969_ = v___y_1046_;
v___y_970_ = v___y_1044_;
v___y_971_ = v___y_1048_;
v___y_972_ = v___y_1047_;
v___y_973_ = v___y_1045_;
v___y_974_ = v___y_1050_;
v___y_975_ = v___y_1049_;
goto v___jp_966_;
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1046_);
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
lean_dec_ref(v___y_1046_);
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
v___y_1044_ = v___y_1080_;
v___y_1045_ = v___y_1083_;
v___y_1046_ = v___y_1079_;
v___y_1047_ = v___y_1082_;
v___y_1048_ = v___y_1081_;
v___y_1049_ = v___y_1085_;
v___y_1050_ = v___y_1084_;
v___y_1051_ = v___x_1088_;
goto v___jp_1043_;
}
else
{
lean_object* v_val_1089_; 
v_val_1089_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_val_1089_);
lean_dec_ref(v___x_1087_);
v___y_1044_ = v___y_1080_;
v___y_1045_ = v___y_1083_;
v___y_1046_ = v___y_1079_;
v___y_1047_ = v___y_1082_;
v___y_1048_ = v___y_1081_;
v___y_1049_ = v___y_1085_;
v___y_1050_ = v___y_1084_;
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
lean_dec_ref(v_a_1107_);
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
size_t v_x_7884__boxed_1134_; lean_object* v_res_1135_; 
v_x_7884__boxed_1134_ = lean_unbox_usize(v_x_1132_);
lean_dec(v_x_1132_);
v_res_1135_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(v_00_u03b2_1130_, v_x_1131_, v_x_7884__boxed_1134_, v_x_1133_);
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
lean_inc(v_declName_1163_);
v___x_1164_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1153_, v_declName_1163_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v_declName_1166_; lean_object* v_config_1167_; lean_object* v_inlineStack_1168_; lean_object* v_inlineStackOccs_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref(v___x_1164_);
v_declName_1166_ = lean_ctor_get(v_a_1155_, 0);
lean_inc(v_declName_1166_);
v_config_1167_ = lean_ctor_get(v_a_1155_, 1);
lean_inc_ref(v_config_1167_);
v_inlineStack_1168_ = lean_ctor_get(v_a_1155_, 2);
lean_inc(v_inlineStack_1168_);
v_inlineStackOccs_1169_ = lean_ctor_get(v_a_1155_, 3);
lean_inc_ref(v_inlineStackOccs_1169_);
lean_dec_ref(v_a_1155_);
v___x_1170_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0));
v___x_1171_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1));
lean_inc(v_declName_1163_);
v___x_1172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1172_, 0, v_declName_1163_);
lean_ctor_set(v___x_1172_, 1, v_inlineStack_1168_);
v___x_1173_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1170_, v___x_1171_, v_inlineStackOccs_1169_, v_declName_1163_, v_a_1165_);
v___x_1174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1174_, 0, v_declName_1166_);
lean_ctor_set(v___x_1174_, 1, v_config_1167_);
lean_ctor_set(v___x_1174_, 2, v___x_1172_);
lean_ctor_set(v___x_1174_, 3, v___x_1173_);
lean_inc(v_a_1161_);
lean_inc_ref(v_a_1160_);
lean_inc(v_a_1159_);
lean_inc_ref(v_a_1158_);
lean_inc_ref(v_a_1157_);
lean_inc(v_a_1156_);
v___x_1175_ = lean_apply_8(v_x_1154_, v___x_1174_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, lean_box(0));
return v___x_1175_;
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_declName_1163_);
lean_dec_ref(v_a_1155_);
lean_dec_ref(v_x_1154_);
v_a_1176_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1164_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1164_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
lean_object* v___x_1184_; 
lean_dec(v_value_1152_);
lean_inc(v_a_1161_);
lean_inc_ref(v_a_1160_);
lean_inc(v_a_1159_);
lean_inc_ref(v_a_1158_);
lean_inc_ref(v_a_1157_);
lean_inc(v_a_1156_);
v___x_1184_ = lean_apply_8(v_x_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, lean_box(0));
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg___boxed(lean_object* v_value_1185_, lean_object* v_recursive_1186_, lean_object* v_x_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
uint8_t v_recursive_boxed_1196_; lean_object* v_res_1197_; 
v_recursive_boxed_1196_ = lean_unbox(v_recursive_1186_);
v_res_1197_ = l_Lean_Compiler_LCNF_Simp_withInlining___redArg(v_value_1185_, v_recursive_boxed_1196_, v_x_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining(lean_object* v_00_u03b1_1198_, lean_object* v_value_1199_, uint8_t v_recursive_1200_, lean_object* v_x_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
if (lean_obj_tag(v_value_1199_) == 3)
{
lean_object* v_declName_1210_; lean_object* v___x_1211_; 
v_declName_1210_ = lean_ctor_get(v_value_1199_, 0);
lean_inc(v_declName_1210_);
lean_dec_ref(v_value_1199_);
lean_inc(v_declName_1210_);
v___x_1211_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1200_, v_declName_1210_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v_declName_1213_; lean_object* v_config_1214_; lean_object* v_inlineStack_1215_; lean_object* v_inlineStackOccs_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref(v___x_1211_);
v_declName_1213_ = lean_ctor_get(v_a_1202_, 0);
lean_inc(v_declName_1213_);
v_config_1214_ = lean_ctor_get(v_a_1202_, 1);
lean_inc_ref(v_config_1214_);
v_inlineStack_1215_ = lean_ctor_get(v_a_1202_, 2);
lean_inc(v_inlineStack_1215_);
v_inlineStackOccs_1216_ = lean_ctor_get(v_a_1202_, 3);
lean_inc_ref(v_inlineStackOccs_1216_);
lean_dec_ref(v_a_1202_);
v___x_1217_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0));
v___x_1218_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1));
lean_inc(v_declName_1210_);
v___x_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_declName_1210_);
lean_ctor_set(v___x_1219_, 1, v_inlineStack_1215_);
v___x_1220_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1217_, v___x_1218_, v_inlineStackOccs_1216_, v_declName_1210_, v_a_1212_);
v___x_1221_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1221_, 0, v_declName_1213_);
lean_ctor_set(v___x_1221_, 1, v_config_1214_);
lean_ctor_set(v___x_1221_, 2, v___x_1219_);
lean_ctor_set(v___x_1221_, 3, v___x_1220_);
lean_inc(v_a_1208_);
lean_inc_ref(v_a_1207_);
lean_inc(v_a_1206_);
lean_inc_ref(v_a_1205_);
lean_inc_ref(v_a_1204_);
lean_inc(v_a_1203_);
v___x_1222_ = lean_apply_8(v_x_1201_, v___x_1221_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, lean_box(0));
return v___x_1222_;
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_declName_1210_);
lean_dec_ref(v_a_1202_);
lean_dec_ref(v_x_1201_);
v_a_1223_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1211_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1211_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
lean_object* v___x_1231_; 
lean_dec(v_value_1199_);
lean_inc(v_a_1208_);
lean_inc_ref(v_a_1207_);
lean_inc(v_a_1206_);
lean_inc_ref(v_a_1205_);
lean_inc_ref(v_a_1204_);
lean_inc(v_a_1203_);
v___x_1231_ = lean_apply_8(v_x_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, lean_box(0));
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___boxed(lean_object* v_00_u03b1_1232_, lean_object* v_value_1233_, lean_object* v_recursive_1234_, lean_object* v_x_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
uint8_t v_recursive_boxed_1244_; lean_object* v_res_1245_; 
v_recursive_boxed_1244_ = lean_unbox(v_recursive_1234_);
v_res_1245_ = l_Lean_Compiler_LCNF_Simp_withInlining(v_00_u03b1_1232_, v_value_1233_, v_recursive_boxed_1244_, v_x_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
return v_res_1245_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__0));
v___x_1248_ = l_Lean_stringToMessageData(v___x_1247_);
return v___x_1248_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__3));
v___x_1253_ = l_Lean_MessageData_ofFormat(v___x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(lean_object* v_as_x27_1254_, lean_object* v_b_1255_){
_start:
{
if (lean_obj_tag(v_as_x27_1254_) == 0)
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_b_1255_);
return v___x_1257_;
}
else
{
lean_object* v_snd_1258_; lean_object* v_head_1259_; lean_object* v_tail_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1311_; 
v_snd_1258_ = lean_ctor_get(v_b_1255_, 1);
lean_inc(v_snd_1258_);
v_head_1259_ = lean_ctor_get(v_as_x27_1254_, 0);
v_tail_1260_ = lean_ctor_get(v_as_x27_1254_, 1);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_as_x27_1254_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1262_ = v_as_x27_1254_;
v_isShared_1263_ = v_isSharedCheck_1311_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_tail_1260_);
lean_inc(v_head_1259_);
lean_dec(v_as_x27_1254_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1311_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_fst_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1309_; 
v_fst_1264_ = lean_ctor_get(v_b_1255_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_b_1255_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v_b_1255_, 1);
lean_dec(v_unused_1310_);
v___x_1266_ = v_b_1255_;
v_isShared_1267_ = v_isSharedCheck_1309_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_fst_1264_);
lean_dec(v_b_1255_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1309_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_fst_1268_; lean_object* v_snd_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1308_; 
v_fst_1268_ = lean_ctor_get(v_snd_1258_, 0);
v_snd_1269_ = lean_ctor_get(v_snd_1258_, 1);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_snd_1258_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1271_ = v_snd_1258_;
v_isShared_1272_ = v_isSharedCheck_1308_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_snd_1269_);
lean_inc(v_fst_1268_);
lean_dec(v_snd_1258_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1308_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_name_eq(v_fst_1268_, v_head_1259_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
lean_dec(v_snd_1269_);
lean_dec(v_fst_1268_);
v___x_1274_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1);
lean_inc(v_head_1259_);
v___x_1275_ = l_Lean_MessageData_ofConstName(v_head_1259_, v___x_1273_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set_tag(v___x_1262_, 7);
lean_ctor_set(v___x_1262_, 1, v___x_1274_);
lean_ctor_set(v___x_1262_, 0, v___x_1275_);
v___x_1277_ = v___x_1262_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v___x_1274_);
v___x_1277_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v_fst_1264_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_box(v___x_1273_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___x_1279_);
lean_ctor_set(v___x_1271_, 0, v_head_1259_);
v___x_1281_ = v___x_1271_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_head_1259_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1283_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1281_);
lean_ctor_set(v___x_1266_, 0, v___x_1278_);
v___x_1283_ = v___x_1266_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
v_as_x27_1254_ = v_tail_1260_;
v_b_1255_ = v___x_1283_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_1288_; 
lean_dec(v_head_1259_);
v___x_1288_ = lean_unbox(v_snd_1269_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
lean_dec(v_snd_1269_);
v___x_1289_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4);
if (v_isShared_1263_ == 0)
{
lean_ctor_set_tag(v___x_1262_, 7);
lean_ctor_set(v___x_1262_, 1, v___x_1289_);
lean_ctor_set(v___x_1262_, 0, v_fst_1264_);
v___x_1291_ = v___x_1262_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_fst_1264_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1292_ = lean_box(v___x_1273_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___x_1292_);
v___x_1294_ = v___x_1271_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_fst_1268_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1296_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1294_);
lean_ctor_set(v___x_1266_, 0, v___x_1291_);
v___x_1296_ = v___x_1266_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
v_as_x27_1254_ = v_tail_1260_;
v_b_1255_ = v___x_1296_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1302_; 
lean_del_object(v___x_1262_);
if (v_isShared_1272_ == 0)
{
v___x_1302_ = v___x_1271_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_fst_1268_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_snd_1269_);
v___x_1302_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1304_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1302_);
v___x_1304_ = v___x_1266_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_fst_1264_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
v_as_x27_1254_ = v_tail_1260_;
v_b_1255_ = v___x_1304_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___boxed(lean_object* v_as_x27_1312_, lean_object* v_b_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_1312_, v_b_1313_);
return v_res_1315_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = l_Lean_maxRecDepthErrorMessage;
v___x_1317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0);
v___x_1319_ = l_Lean_MessageData_ofFormat(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__2));
v___x_1322_ = l_Lean_stringToMessageData(v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_inlineStack_1331_; 
v_inlineStack_1331_ = lean_ctor_get(v_a_1323_, 2);
lean_inc(v_inlineStack_1331_);
lean_dec_ref(v_a_1323_);
if (lean_obj_tag(v_inlineStack_1331_) == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1);
v___x_1333_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_1332_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_);
return v___x_1333_;
}
else
{
lean_object* v_head_1334_; lean_object* v_tail_1335_; uint8_t v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v_a_1344_; lean_object* v_fst_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1354_; 
v_head_1334_ = lean_ctor_get(v_inlineStack_1331_, 0);
lean_inc(v_head_1334_);
v_tail_1335_ = lean_ctor_get(v_inlineStack_1331_, 1);
lean_inc(v_tail_1335_);
lean_dec_ref(v_inlineStack_1331_);
v___x_1336_ = 0;
lean_inc(v_head_1334_);
v___x_1337_ = l_Lean_MessageData_ofConstName(v_head_1334_, v___x_1336_);
v___x_1338_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1);
v___x_1339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = lean_box(v___x_1336_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_head_1334_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
v___x_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1339_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_tail_1335_, v___x_1342_);
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1343_);
v_fst_1345_ = lean_ctor_get(v_a_1344_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_a_1344_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v_a_1344_, 1);
lean_dec(v_unused_1355_);
v___x_1347_ = v_a_1344_;
v_isShared_1348_ = v_isSharedCheck_1354_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_fst_1345_);
lean_dec(v_a_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1354_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3);
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 7);
lean_ctor_set(v___x_1347_, 1, v_fst_1345_);
lean_ctor_set(v___x_1347_, 0, v___x_1349_);
v___x_1351_ = v___x_1347_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_fst_1345_);
v___x_1351_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_1351_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_);
return v___x_1352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___boxed(lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object* v_00_u03b1_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v___x_1374_; 
lean_inc_ref(v_a_1366_);
v___x_1374_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___boxed(lean_object* v_00_u03b1_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(v_00_u03b1_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(lean_object* v_as_1385_, lean_object* v_as_x27_1386_, lean_object* v_b_1387_, lean_object* v_a_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_1386_, v_b_1387_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___boxed(lean_object* v_as_1398_, lean_object* v_as_x27_1399_, lean_object* v_b_1400_, lean_object* v_a_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(v_as_1398_, v_as_x27_1399_, v_b_1400_, v_a_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v_as_1398_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(lean_object* v_x_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v_fileName_1420_; lean_object* v_fileMap_1421_; lean_object* v_options_1422_; lean_object* v_currRecDepth_1423_; lean_object* v_maxRecDepth_1424_; lean_object* v_ref_1425_; lean_object* v_currNamespace_1426_; lean_object* v_openDecls_1427_; lean_object* v_initHeartbeats_1428_; lean_object* v_maxHeartbeats_1429_; lean_object* v_quotContext_1430_; lean_object* v_currMacroScope_1431_; uint8_t v_diag_1432_; lean_object* v_cancelTk_x3f_1433_; uint8_t v_suppressElabErrors_1434_; lean_object* v_inheritedTraceOptions_1435_; uint8_t v___x_1436_; 
v_fileName_1420_ = lean_ctor_get(v_a_1417_, 0);
v_fileMap_1421_ = lean_ctor_get(v_a_1417_, 1);
v_options_1422_ = lean_ctor_get(v_a_1417_, 2);
v_currRecDepth_1423_ = lean_ctor_get(v_a_1417_, 3);
v_maxRecDepth_1424_ = lean_ctor_get(v_a_1417_, 4);
v_ref_1425_ = lean_ctor_get(v_a_1417_, 5);
v_currNamespace_1426_ = lean_ctor_get(v_a_1417_, 6);
v_openDecls_1427_ = lean_ctor_get(v_a_1417_, 7);
v_initHeartbeats_1428_ = lean_ctor_get(v_a_1417_, 8);
v_maxHeartbeats_1429_ = lean_ctor_get(v_a_1417_, 9);
v_quotContext_1430_ = lean_ctor_get(v_a_1417_, 10);
v_currMacroScope_1431_ = lean_ctor_get(v_a_1417_, 11);
v_diag_1432_ = lean_ctor_get_uint8(v_a_1417_, sizeof(void*)*14);
v_cancelTk_x3f_1433_ = lean_ctor_get(v_a_1417_, 12);
v_suppressElabErrors_1434_ = lean_ctor_get_uint8(v_a_1417_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1435_ = lean_ctor_get(v_a_1417_, 13);
v___x_1436_ = lean_nat_dec_eq(v_currRecDepth_1423_, v_maxRecDepth_1424_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1437_ = lean_unsigned_to_nat(1u);
v___x_1438_ = lean_nat_add(v_currRecDepth_1423_, v___x_1437_);
lean_inc_ref(v_inheritedTraceOptions_1435_);
lean_inc(v_cancelTk_x3f_1433_);
lean_inc(v_currMacroScope_1431_);
lean_inc(v_quotContext_1430_);
lean_inc(v_maxHeartbeats_1429_);
lean_inc(v_initHeartbeats_1428_);
lean_inc(v_openDecls_1427_);
lean_inc(v_currNamespace_1426_);
lean_inc(v_ref_1425_);
lean_inc(v_maxRecDepth_1424_);
lean_inc_ref(v_options_1422_);
lean_inc_ref(v_fileMap_1421_);
lean_inc_ref(v_fileName_1420_);
v___x_1439_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1439_, 0, v_fileName_1420_);
lean_ctor_set(v___x_1439_, 1, v_fileMap_1421_);
lean_ctor_set(v___x_1439_, 2, v_options_1422_);
lean_ctor_set(v___x_1439_, 3, v___x_1438_);
lean_ctor_set(v___x_1439_, 4, v_maxRecDepth_1424_);
lean_ctor_set(v___x_1439_, 5, v_ref_1425_);
lean_ctor_set(v___x_1439_, 6, v_currNamespace_1426_);
lean_ctor_set(v___x_1439_, 7, v_openDecls_1427_);
lean_ctor_set(v___x_1439_, 8, v_initHeartbeats_1428_);
lean_ctor_set(v___x_1439_, 9, v_maxHeartbeats_1429_);
lean_ctor_set(v___x_1439_, 10, v_quotContext_1430_);
lean_ctor_set(v___x_1439_, 11, v_currMacroScope_1431_);
lean_ctor_set(v___x_1439_, 12, v_cancelTk_x3f_1433_);
lean_ctor_set(v___x_1439_, 13, v_inheritedTraceOptions_1435_);
lean_ctor_set_uint8(v___x_1439_, sizeof(void*)*14, v_diag_1432_);
lean_ctor_set_uint8(v___x_1439_, sizeof(void*)*14 + 1, v_suppressElabErrors_1434_);
lean_inc(v_a_1418_);
lean_inc(v_a_1416_);
lean_inc_ref(v_a_1415_);
lean_inc_ref(v_a_1414_);
lean_inc(v_a_1413_);
lean_inc_ref(v_a_1412_);
v___x_1440_ = lean_apply_8(v_x_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v___x_1439_, v_a_1418_, lean_box(0));
return v___x_1440_;
}
else
{
lean_object* v___x_1441_; 
lean_dec_ref(v_x_1411_);
lean_inc_ref(v_a_1412_);
v___x_1441_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
return v___x_1441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg___boxed(lean_object* v_x_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(v_x_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth(lean_object* v_00_u03b1_1452_, lean_object* v_x_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v_fileName_1462_; lean_object* v_fileMap_1463_; lean_object* v_options_1464_; lean_object* v_currRecDepth_1465_; lean_object* v_maxRecDepth_1466_; lean_object* v_ref_1467_; lean_object* v_currNamespace_1468_; lean_object* v_openDecls_1469_; lean_object* v_initHeartbeats_1470_; lean_object* v_maxHeartbeats_1471_; lean_object* v_quotContext_1472_; lean_object* v_currMacroScope_1473_; uint8_t v_diag_1474_; lean_object* v_cancelTk_x3f_1475_; uint8_t v_suppressElabErrors_1476_; lean_object* v_inheritedTraceOptions_1477_; uint8_t v___x_1478_; 
v_fileName_1462_ = lean_ctor_get(v_a_1459_, 0);
v_fileMap_1463_ = lean_ctor_get(v_a_1459_, 1);
v_options_1464_ = lean_ctor_get(v_a_1459_, 2);
v_currRecDepth_1465_ = lean_ctor_get(v_a_1459_, 3);
v_maxRecDepth_1466_ = lean_ctor_get(v_a_1459_, 4);
v_ref_1467_ = lean_ctor_get(v_a_1459_, 5);
v_currNamespace_1468_ = lean_ctor_get(v_a_1459_, 6);
v_openDecls_1469_ = lean_ctor_get(v_a_1459_, 7);
v_initHeartbeats_1470_ = lean_ctor_get(v_a_1459_, 8);
v_maxHeartbeats_1471_ = lean_ctor_get(v_a_1459_, 9);
v_quotContext_1472_ = lean_ctor_get(v_a_1459_, 10);
v_currMacroScope_1473_ = lean_ctor_get(v_a_1459_, 11);
v_diag_1474_ = lean_ctor_get_uint8(v_a_1459_, sizeof(void*)*14);
v_cancelTk_x3f_1475_ = lean_ctor_get(v_a_1459_, 12);
v_suppressElabErrors_1476_ = lean_ctor_get_uint8(v_a_1459_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1477_ = lean_ctor_get(v_a_1459_, 13);
v___x_1478_ = lean_nat_dec_eq(v_currRecDepth_1465_, v_maxRecDepth_1466_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1479_ = lean_unsigned_to_nat(1u);
v___x_1480_ = lean_nat_add(v_currRecDepth_1465_, v___x_1479_);
lean_inc_ref(v_inheritedTraceOptions_1477_);
lean_inc(v_cancelTk_x3f_1475_);
lean_inc(v_currMacroScope_1473_);
lean_inc(v_quotContext_1472_);
lean_inc(v_maxHeartbeats_1471_);
lean_inc(v_initHeartbeats_1470_);
lean_inc(v_openDecls_1469_);
lean_inc(v_currNamespace_1468_);
lean_inc(v_ref_1467_);
lean_inc(v_maxRecDepth_1466_);
lean_inc_ref(v_options_1464_);
lean_inc_ref(v_fileMap_1463_);
lean_inc_ref(v_fileName_1462_);
v___x_1481_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1481_, 0, v_fileName_1462_);
lean_ctor_set(v___x_1481_, 1, v_fileMap_1463_);
lean_ctor_set(v___x_1481_, 2, v_options_1464_);
lean_ctor_set(v___x_1481_, 3, v___x_1480_);
lean_ctor_set(v___x_1481_, 4, v_maxRecDepth_1466_);
lean_ctor_set(v___x_1481_, 5, v_ref_1467_);
lean_ctor_set(v___x_1481_, 6, v_currNamespace_1468_);
lean_ctor_set(v___x_1481_, 7, v_openDecls_1469_);
lean_ctor_set(v___x_1481_, 8, v_initHeartbeats_1470_);
lean_ctor_set(v___x_1481_, 9, v_maxHeartbeats_1471_);
lean_ctor_set(v___x_1481_, 10, v_quotContext_1472_);
lean_ctor_set(v___x_1481_, 11, v_currMacroScope_1473_);
lean_ctor_set(v___x_1481_, 12, v_cancelTk_x3f_1475_);
lean_ctor_set(v___x_1481_, 13, v_inheritedTraceOptions_1477_);
lean_ctor_set_uint8(v___x_1481_, sizeof(void*)*14, v_diag_1474_);
lean_ctor_set_uint8(v___x_1481_, sizeof(void*)*14 + 1, v_suppressElabErrors_1476_);
lean_inc(v_a_1460_);
lean_inc(v_a_1458_);
lean_inc_ref(v_a_1457_);
lean_inc_ref(v_a_1456_);
lean_inc(v_a_1455_);
lean_inc_ref(v_a_1454_);
v___x_1482_ = lean_apply_8(v_x_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v___x_1481_, v_a_1460_, lean_box(0));
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; 
lean_dec_ref(v_x_1453_);
lean_inc_ref(v_a_1454_);
v___x_1483_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
return v___x_1483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___boxed(lean_object* v_00_u03b1_1484_, lean_object* v_x_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth(v_00_u03b1_1484_, v_x_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(lean_object* v_a_1495_, lean_object* v_fvarId_1496_, lean_object* v___x_1497_, lean_object* v_a_x3f_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v_subst_1501_; lean_object* v_used_1502_; lean_object* v_binderRenaming_1503_; lean_object* v_funDeclInfoMap_1504_; uint8_t v_simplified_1505_; lean_object* v_visited_1506_; lean_object* v_inline_1507_; lean_object* v_inlineLocal_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1519_; 
v___x_1500_ = lean_st_ref_take(v_a_1495_);
v_subst_1501_ = lean_ctor_get(v___x_1500_, 0);
v_used_1502_ = lean_ctor_get(v___x_1500_, 1);
v_binderRenaming_1503_ = lean_ctor_get(v___x_1500_, 2);
v_funDeclInfoMap_1504_ = lean_ctor_get(v___x_1500_, 3);
v_simplified_1505_ = lean_ctor_get_uint8(v___x_1500_, sizeof(void*)*7);
v_visited_1506_ = lean_ctor_get(v___x_1500_, 4);
v_inline_1507_ = lean_ctor_get(v___x_1500_, 5);
v_inlineLocal_1508_ = lean_ctor_get(v___x_1500_, 6);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1510_ = v___x_1500_;
v_isShared_1511_ = v_isSharedCheck_1519_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_inlineLocal_1508_);
lean_inc(v_inline_1507_);
lean_inc(v_visited_1506_);
lean_inc(v_funDeclInfoMap_1504_);
lean_inc(v_binderRenaming_1503_);
lean_inc(v_used_1502_);
lean_inc(v_subst_1501_);
lean_dec(v___x_1500_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1519_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(v_funDeclInfoMap_1504_, v_fvarId_1496_, v___x_1497_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 3, v___x_1512_);
v___x_1514_ = v___x_1510_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_subst_1501_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_used_1502_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_binderRenaming_1503_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_visited_1506_);
lean_ctor_set(v_reuseFailAlloc_1518_, 5, v_inline_1507_);
lean_ctor_set(v_reuseFailAlloc_1518_, 6, v_inlineLocal_1508_);
lean_ctor_set_uint8(v_reuseFailAlloc_1518_, sizeof(void*)*7, v_simplified_1505_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = lean_st_ref_set(v_a_1495_, v___x_1514_);
v___x_1516_ = lean_box(0);
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
return v___x_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0___boxed(lean_object* v_a_1520_, lean_object* v_fvarId_1521_, lean_object* v___x_1522_, lean_object* v_a_x3f_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1520_, v_fvarId_1521_, v___x_1522_, v_a_x3f_1523_);
lean_dec(v_a_x3f_1523_);
lean_dec(v_a_1520_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(lean_object* v_a_1526_, lean_object* v_x_1527_){
_start:
{
if (lean_obj_tag(v_x_1527_) == 0)
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_box(0);
return v___x_1528_;
}
else
{
lean_object* v_key_1529_; lean_object* v_value_1530_; lean_object* v_tail_1531_; uint8_t v___x_1532_; 
v_key_1529_ = lean_ctor_get(v_x_1527_, 0);
v_value_1530_ = lean_ctor_get(v_x_1527_, 1);
v_tail_1531_ = lean_ctor_get(v_x_1527_, 2);
v___x_1532_ = l_Lean_instBEqFVarId_beq(v_key_1529_, v_a_1526_);
if (v___x_1532_ == 0)
{
v_x_1527_ = v_tail_1531_;
goto _start;
}
else
{
lean_object* v___x_1534_; 
lean_inc(v_value_1530_);
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_value_1530_);
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg___boxed(lean_object* v_a_1535_, lean_object* v_x_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1535_, v_x_1536_);
lean_dec(v_x_1536_);
lean_dec(v_a_1535_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(lean_object* v_m_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_buckets_1540_; lean_object* v___x_1541_; uint64_t v___x_1542_; uint64_t v___x_1543_; uint64_t v___x_1544_; uint64_t v_fold_1545_; uint64_t v___x_1546_; uint64_t v___x_1547_; uint64_t v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; size_t v___x_1551_; size_t v___x_1552_; size_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_buckets_1540_ = lean_ctor_get(v_m_1538_, 1);
v___x_1541_ = lean_array_get_size(v_buckets_1540_);
v___x_1542_ = l_Lean_instHashableFVarId_hash(v_a_1539_);
v___x_1543_ = 32ULL;
v___x_1544_ = lean_uint64_shift_right(v___x_1542_, v___x_1543_);
v_fold_1545_ = lean_uint64_xor(v___x_1542_, v___x_1544_);
v___x_1546_ = 16ULL;
v___x_1547_ = lean_uint64_shift_right(v_fold_1545_, v___x_1546_);
v___x_1548_ = lean_uint64_xor(v_fold_1545_, v___x_1547_);
v___x_1549_ = lean_uint64_to_usize(v___x_1548_);
v___x_1550_ = lean_usize_of_nat(v___x_1541_);
v___x_1551_ = ((size_t)1ULL);
v___x_1552_ = lean_usize_sub(v___x_1550_, v___x_1551_);
v___x_1553_ = lean_usize_land(v___x_1549_, v___x_1552_);
v___x_1554_ = lean_array_uget_borrowed(v_buckets_1540_, v___x_1553_);
v___x_1555_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1539_, v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg___boxed(lean_object* v_m_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_m_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(lean_object* v_fvarId_1559_, lean_object* v_x_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v___x_1569_; lean_object* v_funDeclInfoMap_1570_; lean_object* v___x_1571_; lean_object* v_a_1573_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1569_ = lean_st_ref_get(v_a_1562_);
v_funDeclInfoMap_1570_ = lean_ctor_get(v___x_1569_, 3);
lean_inc_ref(v_funDeclInfoMap_1570_);
lean_dec(v___x_1569_);
v___x_1571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_1570_, v_fvarId_1559_);
lean_dec_ref(v_funDeclInfoMap_1570_);
lean_inc(v_fvarId_1559_);
v___x_1584_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_1559_, v_a_1562_);
lean_dec_ref(v___x_1584_);
lean_inc(v_a_1567_);
lean_inc_ref(v_a_1566_);
lean_inc(v_a_1565_);
lean_inc_ref(v_a_1564_);
lean_inc_ref(v_a_1563_);
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
v___x_1585_ = lean_apply_8(v_x_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, lean_box(0));
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1602_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1602_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1602_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
lean_inc(v_a_1586_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 1);
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
v___x_1592_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1562_, v_fvarId_1559_, v___x_1571_, v___x_1591_);
lean_dec_ref(v___x_1591_);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; 
v_unused_1600_ = lean_ctor_get(v___x_1592_, 0);
lean_dec(v_unused_1600_);
v___x_1594_ = v___x_1592_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v___x_1592_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v_a_1586_);
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1586_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
else
{
lean_object* v_a_1603_; 
v_a_1603_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1603_);
lean_dec_ref(v___x_1585_);
v_a_1573_ = v_a_1603_;
goto v___jp_1572_;
}
v___jp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
v___x_1574_ = lean_box(0);
v___x_1575_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1562_, v_fvarId_1559_, v___x_1571_, v___x_1574_);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v___x_1575_, 0);
lean_dec(v_unused_1583_);
v___x_1577_ = v___x_1575_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_dec(v___x_1575_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set_tag(v___x_1577_, 1);
lean_ctor_set(v___x_1577_, 0, v_a_1573_);
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1573_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___boxed(lean_object* v_fvarId_1604_, lean_object* v_x_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1604_, v_x_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object* v_00_u03b1_1615_, lean_object* v_fvarId_1616_, lean_object* v_x_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1616_, v_x_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___boxed(lean_object* v_00_u03b1_1627_, lean_object* v_fvarId_1628_, lean_object* v_x_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline(v_00_u03b1_1627_, v_fvarId_1628_, v_x_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(lean_object* v_00_u03b2_1639_, lean_object* v_m_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_1640_, v_a_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___boxed(lean_object* v_00_u03b2_1643_, lean_object* v_m_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(v_00_u03b2_1643_, v_m_1644_, v_a_1645_);
lean_dec(v_a_1645_);
lean_dec_ref(v_m_1644_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(lean_object* v_00_u03b2_1647_, lean_object* v_a_1648_, lean_object* v_x_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1648_, v_x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1651_, lean_object* v_a_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(v_00_u03b2_1651_, v_a_1652_, v_x_1653_);
lean_dec(v_x_1653_);
lean_dec(v_a_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object* v_fvarId_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v___x_1666_; lean_object* v_funDeclInfoMap_1667_; lean_object* v___x_1668_; 
v___x_1666_ = lean_st_ref_get(v_a_1656_);
v_funDeclInfoMap_1667_ = lean_ctor_get(v___x_1666_, 3);
lean_inc_ref(v_funDeclInfoMap_1667_);
lean_dec(v___x_1666_);
v___x_1668_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_1667_, v_fvarId_1655_);
lean_dec_ref(v_funDeclInfoMap_1667_);
if (lean_obj_tag(v___x_1668_) == 1)
{
lean_object* v_val_1669_; uint8_t v___x_1670_; 
v_val_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_val_1669_);
lean_dec_ref(v___x_1668_);
v___x_1670_ = lean_unbox(v_val_1669_);
lean_dec(v_val_1669_);
switch(v___x_1670_)
{
case 0:
{
goto v___jp_1662_;
}
case 2:
{
goto v___jp_1662_;
}
default: 
{
goto v___jp_1658_;
}
}
}
else
{
lean_dec(v___x_1668_);
goto v___jp_1658_;
}
v___jp_1658_:
{
uint8_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = 0;
v___x_1660_ = lean_box(v___x_1659_);
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
return v___x_1661_;
}
v___jp_1662_:
{
uint8_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = 1;
v___x_1664_ = lean_box(v___x_1663_);
v___x_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg___boxed(lean_object* v_fvarId_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1671_, v_a_1672_);
lean_dec(v_a_1672_);
lean_dec(v_fvarId_1671_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object* v_fvarId_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1675_, v_a_1677_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object* v_fvarId_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(v_fvarId_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_fvarId_1685_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg(lean_object* v_code_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_1696_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1710_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1710_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1710_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v_smallThreshold_1703_; uint8_t v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v_smallThreshold_1703_ = lean_ctor_get(v_a_1699_, 0);
lean_inc(v_smallThreshold_1703_);
lean_dec(v_a_1699_);
v___x_1704_ = 0;
v___x_1705_ = l_Lean_Compiler_LCNF_Code_sizeLe(v___x_1704_, v_code_1695_, v_smallThreshold_1703_);
lean_dec(v_smallThreshold_1703_);
v___x_1706_ = lean_box(v___x_1705_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1706_);
v___x_1708_ = v___x_1701_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
v_a_1711_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1698_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1698_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg___boxed(lean_object* v_code_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1719_, v_a_1720_);
lean_dec_ref(v_a_1720_);
lean_dec_ref(v_code_1719_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object* v_code_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1723_, v_a_1727_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object* v_code_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Compiler_LCNF_Simp_isSmall(v_code_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec_ref(v_code_1733_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object* v_decl_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_fvarId_1747_; lean_object* v_value_1748_; lean_object* v___x_1749_; lean_object* v_a_1750_; uint8_t v___x_1751_; 
v_fvarId_1747_ = lean_ctor_get(v_decl_1743_, 0);
v_value_1748_ = lean_ctor_get(v_decl_1743_, 4);
v___x_1749_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1747_, v_a_1744_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
v___x_1751_ = lean_unbox(v_a_1750_);
lean_dec(v_a_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
lean_dec_ref(v___x_1749_);
v___x_1752_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_value_1748_, v_a_1745_);
return v___x_1752_;
}
else
{
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg___boxed(lean_object* v_decl_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1753_, v_a_1754_, v_a_1755_);
lean_dec_ref(v_a_1755_);
lean_dec(v_a_1754_);
lean_dec_ref(v_decl_1753_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object* v_decl_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1758_, v_a_1760_, v_a_1762_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object* v_decl_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(v_decl_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec_ref(v_decl_1768_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(lean_object* v_a_1778_, lean_object* v_b_1779_, lean_object* v_x_1780_){
_start:
{
if (lean_obj_tag(v_x_1780_) == 0)
{
lean_dec(v_b_1779_);
lean_dec(v_a_1778_);
return v_x_1780_;
}
else
{
lean_object* v_key_1781_; lean_object* v_value_1782_; lean_object* v_tail_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1795_; 
v_key_1781_ = lean_ctor_get(v_x_1780_, 0);
v_value_1782_ = lean_ctor_get(v_x_1780_, 1);
v_tail_1783_ = lean_ctor_get(v_x_1780_, 2);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_x_1780_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1785_ = v_x_1780_;
v_isShared_1786_ = v_isSharedCheck_1795_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_tail_1783_);
lean_inc(v_value_1782_);
lean_inc(v_key_1781_);
lean_dec(v_x_1780_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1795_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
uint8_t v___x_1787_; 
v___x_1787_ = l_Lean_instBEqFVarId_beq(v_key_1781_, v_a_1778_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1788_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_1778_, v_b_1779_, v_tail_1783_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 2, v___x_1788_);
v___x_1790_ = v___x_1785_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_key_1781_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_value_1782_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
else
{
lean_object* v___x_1793_; 
lean_dec(v_value_1782_);
lean_dec(v_key_1781_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 1, v_b_1779_);
lean_ctor_set(v___x_1785_, 0, v_a_1778_);
v___x_1793_ = v___x_1785_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1778_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_b_1779_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_tail_1783_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(lean_object* v_a_1796_, lean_object* v_x_1797_){
_start:
{
if (lean_obj_tag(v_x_1797_) == 0)
{
uint8_t v___x_1798_; 
v___x_1798_ = 0;
return v___x_1798_;
}
else
{
lean_object* v_key_1799_; lean_object* v_tail_1800_; uint8_t v___x_1801_; 
v_key_1799_ = lean_ctor_get(v_x_1797_, 0);
v_tail_1800_ = lean_ctor_get(v_x_1797_, 2);
v___x_1801_ = l_Lean_instBEqFVarId_beq(v_key_1799_, v_a_1796_);
if (v___x_1801_ == 0)
{
v_x_1797_ = v_tail_1800_;
goto _start;
}
else
{
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg___boxed(lean_object* v_a_1803_, lean_object* v_x_1804_){
_start:
{
uint8_t v_res_1805_; lean_object* v_r_1806_; 
v_res_1805_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1803_, v_x_1804_);
lean_dec(v_x_1804_);
lean_dec(v_a_1803_);
v_r_1806_ = lean_box(v_res_1805_);
return v_r_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_1807_, lean_object* v_x_1808_){
_start:
{
if (lean_obj_tag(v_x_1808_) == 0)
{
return v_x_1807_;
}
else
{
lean_object* v_key_1809_; lean_object* v_value_1810_; lean_object* v_tail_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1834_; 
v_key_1809_ = lean_ctor_get(v_x_1808_, 0);
v_value_1810_ = lean_ctor_get(v_x_1808_, 1);
v_tail_1811_ = lean_ctor_get(v_x_1808_, 2);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_x_1808_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1813_ = v_x_1808_;
v_isShared_1814_ = v_isSharedCheck_1834_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_tail_1811_);
lean_inc(v_value_1810_);
lean_inc(v_key_1809_);
lean_dec(v_x_1808_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1834_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; uint64_t v___x_1816_; uint64_t v___x_1817_; uint64_t v___x_1818_; uint64_t v_fold_1819_; uint64_t v___x_1820_; uint64_t v___x_1821_; uint64_t v___x_1822_; size_t v___x_1823_; size_t v___x_1824_; size_t v___x_1825_; size_t v___x_1826_; size_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1815_ = lean_array_get_size(v_x_1807_);
v___x_1816_ = l_Lean_instHashableFVarId_hash(v_key_1809_);
v___x_1817_ = 32ULL;
v___x_1818_ = lean_uint64_shift_right(v___x_1816_, v___x_1817_);
v_fold_1819_ = lean_uint64_xor(v___x_1816_, v___x_1818_);
v___x_1820_ = 16ULL;
v___x_1821_ = lean_uint64_shift_right(v_fold_1819_, v___x_1820_);
v___x_1822_ = lean_uint64_xor(v_fold_1819_, v___x_1821_);
v___x_1823_ = lean_uint64_to_usize(v___x_1822_);
v___x_1824_ = lean_usize_of_nat(v___x_1815_);
v___x_1825_ = ((size_t)1ULL);
v___x_1826_ = lean_usize_sub(v___x_1824_, v___x_1825_);
v___x_1827_ = lean_usize_land(v___x_1823_, v___x_1826_);
v___x_1828_ = lean_array_uget_borrowed(v_x_1807_, v___x_1827_);
lean_inc(v___x_1828_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 2, v___x_1828_);
v___x_1830_ = v___x_1813_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_key_1809_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_value_1810_);
lean_ctor_set(v_reuseFailAlloc_1833_, 2, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_array_uset(v_x_1807_, v___x_1827_, v___x_1830_);
v_x_1807_ = v___x_1831_;
v_x_1808_ = v_tail_1811_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1835_, lean_object* v_source_1836_, lean_object* v_target_1837_){
_start:
{
lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_array_get_size(v_source_1836_);
v___x_1839_ = lean_nat_dec_lt(v_i_1835_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_dec_ref(v_source_1836_);
lean_dec(v_i_1835_);
return v_target_1837_;
}
else
{
lean_object* v_es_1840_; lean_object* v___x_1841_; lean_object* v_source_1842_; lean_object* v_target_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_es_1840_ = lean_array_fget(v_source_1836_, v_i_1835_);
v___x_1841_ = lean_box(0);
v_source_1842_ = lean_array_fset(v_source_1836_, v_i_1835_, v___x_1841_);
v_target_1843_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(v_target_1837_, v_es_1840_);
v___x_1844_ = lean_unsigned_to_nat(1u);
v___x_1845_ = lean_nat_add(v_i_1835_, v___x_1844_);
lean_dec(v_i_1835_);
v_i_1835_ = v___x_1845_;
v_source_1836_ = v_source_1842_;
v_target_1837_ = v_target_1843_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(lean_object* v_data_1847_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_nbuckets_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1848_ = lean_array_get_size(v_data_1847_);
v___x_1849_ = lean_unsigned_to_nat(2u);
v_nbuckets_1850_ = lean_nat_mul(v___x_1848_, v___x_1849_);
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_box(0);
v___x_1853_ = lean_mk_array(v_nbuckets_1850_, v___x_1852_);
v___x_1854_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(v___x_1851_, v_data_1847_, v___x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(lean_object* v_m_1855_, lean_object* v_a_1856_, lean_object* v_b_1857_){
_start:
{
lean_object* v_size_1858_; lean_object* v_buckets_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1902_; 
v_size_1858_ = lean_ctor_get(v_m_1855_, 0);
v_buckets_1859_ = lean_ctor_get(v_m_1855_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_m_1855_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1861_ = v_m_1855_;
v_isShared_1862_ = v_isSharedCheck_1902_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_buckets_1859_);
lean_inc(v_size_1858_);
lean_dec(v_m_1855_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1902_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; uint64_t v___x_1864_; uint64_t v___x_1865_; uint64_t v___x_1866_; uint64_t v_fold_1867_; uint64_t v___x_1868_; uint64_t v___x_1869_; uint64_t v___x_1870_; size_t v___x_1871_; size_t v___x_1872_; size_t v___x_1873_; size_t v___x_1874_; size_t v___x_1875_; lean_object* v_bkt_1876_; uint8_t v___x_1877_; 
v___x_1863_ = lean_array_get_size(v_buckets_1859_);
v___x_1864_ = l_Lean_instHashableFVarId_hash(v_a_1856_);
v___x_1865_ = 32ULL;
v___x_1866_ = lean_uint64_shift_right(v___x_1864_, v___x_1865_);
v_fold_1867_ = lean_uint64_xor(v___x_1864_, v___x_1866_);
v___x_1868_ = 16ULL;
v___x_1869_ = lean_uint64_shift_right(v_fold_1867_, v___x_1868_);
v___x_1870_ = lean_uint64_xor(v_fold_1867_, v___x_1869_);
v___x_1871_ = lean_uint64_to_usize(v___x_1870_);
v___x_1872_ = lean_usize_of_nat(v___x_1863_);
v___x_1873_ = ((size_t)1ULL);
v___x_1874_ = lean_usize_sub(v___x_1872_, v___x_1873_);
v___x_1875_ = lean_usize_land(v___x_1871_, v___x_1874_);
v_bkt_1876_ = lean_array_uget_borrowed(v_buckets_1859_, v___x_1875_);
v___x_1877_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1856_, v_bkt_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v_size_x27_1879_; lean_object* v___x_1880_; lean_object* v_buckets_x27_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1878_ = lean_unsigned_to_nat(1u);
v_size_x27_1879_ = lean_nat_add(v_size_1858_, v___x_1878_);
lean_dec(v_size_1858_);
lean_inc(v_bkt_1876_);
v___x_1880_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1880_, 0, v_a_1856_);
lean_ctor_set(v___x_1880_, 1, v_b_1857_);
lean_ctor_set(v___x_1880_, 2, v_bkt_1876_);
v_buckets_x27_1881_ = lean_array_uset(v_buckets_1859_, v___x_1875_, v___x_1880_);
v___x_1882_ = lean_unsigned_to_nat(4u);
v___x_1883_ = lean_nat_mul(v_size_x27_1879_, v___x_1882_);
v___x_1884_ = lean_unsigned_to_nat(3u);
v___x_1885_ = lean_nat_div(v___x_1883_, v___x_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_array_get_size(v_buckets_x27_1881_);
v___x_1887_ = lean_nat_dec_le(v___x_1885_, v___x_1886_);
lean_dec(v___x_1885_);
if (v___x_1887_ == 0)
{
lean_object* v_val_1888_; lean_object* v___x_1890_; 
v_val_1888_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(v_buckets_x27_1881_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v_val_1888_);
lean_ctor_set(v___x_1861_, 0, v_size_x27_1879_);
v___x_1890_ = v___x_1861_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_size_x27_1879_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_val_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
else
{
lean_object* v___x_1893_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v_buckets_x27_1881_);
lean_ctor_set(v___x_1861_, 0, v_size_x27_1879_);
v___x_1893_ = v___x_1861_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_size_x27_1879_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_buckets_x27_1881_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
else
{
lean_object* v___x_1895_; lean_object* v_buckets_x27_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
lean_inc(v_bkt_1876_);
v___x_1895_ = lean_box(0);
v_buckets_x27_1896_ = lean_array_uset(v_buckets_1859_, v___x_1875_, v___x_1895_);
v___x_1897_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_1856_, v_b_1857_, v_bkt_1876_);
v___x_1898_ = lean_array_uset(v_buckets_x27_1896_, v___x_1875_, v___x_1897_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v___x_1898_);
v___x_1900_ = v___x_1861_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_size_1858_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(lean_object* v_as_1903_, size_t v_sz_1904_, size_t v_i_1905_, lean_object* v_b_1906_){
_start:
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_usize_dec_lt(v_i_1905_, v_sz_1904_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v_b_1906_);
return v___x_1909_;
}
else
{
lean_object* v_snd_1910_; lean_object* v_fst_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1945_; 
v_snd_1910_ = lean_ctor_get(v_b_1906_, 1);
v_fst_1911_ = lean_ctor_get(v_b_1906_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_b_1906_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1913_ = v_b_1906_;
v_isShared_1914_ = v_isSharedCheck_1945_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_snd_1910_);
lean_inc(v_fst_1911_);
lean_dec(v_b_1906_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1945_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_array_1915_; lean_object* v_start_1916_; lean_object* v_stop_1917_; uint8_t v___x_1918_; 
v_array_1915_ = lean_ctor_get(v_snd_1910_, 0);
v_start_1916_ = lean_ctor_get(v_snd_1910_, 1);
v_stop_1917_ = lean_ctor_get(v_snd_1910_, 2);
v___x_1918_ = lean_nat_dec_lt(v_start_1916_, v_stop_1917_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1920_; 
if (v_isShared_1914_ == 0)
{
v___x_1920_ = v___x_1913_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_fst_1911_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_snd_1910_);
v___x_1920_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
else
{
lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1941_; 
lean_inc(v_stop_1917_);
lean_inc(v_start_1916_);
lean_inc_ref(v_array_1915_);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_snd_1910_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; lean_object* v_unused_1943_; lean_object* v_unused_1944_; 
v_unused_1942_ = lean_ctor_get(v_snd_1910_, 2);
lean_dec(v_unused_1942_);
v_unused_1943_ = lean_ctor_get(v_snd_1910_, 1);
lean_dec(v_unused_1943_);
v_unused_1944_ = lean_ctor_get(v_snd_1910_, 0);
lean_dec(v_unused_1944_);
v___x_1924_ = v_snd_1910_;
v_isShared_1925_ = v_isSharedCheck_1941_;
goto v_resetjp_1923_;
}
else
{
lean_dec(v_snd_1910_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1941_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v_a_1926_; lean_object* v_fvarId_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
v_a_1926_ = lean_array_uget_borrowed(v_as_1903_, v_i_1905_);
v_fvarId_1927_ = lean_ctor_get(v_a_1926_, 0);
v___x_1928_ = lean_array_fget(v_array_1915_, v_start_1916_);
v___x_1929_ = lean_unsigned_to_nat(1u);
v___x_1930_ = lean_nat_add(v_start_1916_, v___x_1929_);
lean_dec(v_start_1916_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v___x_1930_);
v___x_1932_ = v___x_1924_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_array_1915_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_stop_1917_);
v___x_1932_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
lean_inc(v_fvarId_1927_);
v___x_1933_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_fst_1911_, v_fvarId_1927_, v___x_1928_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v___x_1932_);
lean_ctor_set(v___x_1913_, 0, v___x_1933_);
v___x_1935_ = v___x_1913_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1932_);
v___x_1935_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
size_t v___x_1936_; size_t v___x_1937_; 
v___x_1936_ = ((size_t)1ULL);
v___x_1937_ = lean_usize_add(v_i_1905_, v___x_1936_);
v_i_1905_ = v___x_1937_;
v_b_1906_ = v___x_1935_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg___boxed(lean_object* v_as_1946_, lean_object* v_sz_1947_, lean_object* v_i_1948_, lean_object* v_b_1949_, lean_object* v___y_1950_){
_start:
{
size_t v_sz_boxed_1951_; size_t v_i_boxed_1952_; lean_object* v_res_1953_; 
v_sz_boxed_1951_ = lean_unbox_usize(v_sz_1947_);
lean_dec(v_sz_1947_);
v_i_boxed_1952_ = lean_unbox_usize(v_i_1948_);
lean_dec(v_i_1948_);
v_res_1953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_1946_, v_sz_boxed_1951_, v_i_boxed_1952_, v_b_1949_);
lean_dec_ref(v_as_1946_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object* v_params_1954_, lean_object* v_code_1955_, lean_object* v_args_1956_, uint8_t v_mustInline_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v___x_1966_; lean_object* v_subst_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; size_t v_sz_1971_; size_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1966_ = lean_unsigned_to_nat(0u);
v_subst_1967_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1);
v___x_1968_ = lean_array_get_size(v_args_1956_);
v___x_1969_ = l_Array_toSubarray___redArg(v_args_1956_, v___x_1966_, v___x_1968_);
v___x_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1970_, 0, v_subst_1967_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v_sz_1971_ = lean_array_size(v_params_1954_);
v___x_1972_ = ((size_t)0ULL);
v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_params_1954_, v_sz_1971_, v___x_1972_, v___x_1970_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v_fst_1975_; uint8_t v___x_1976_; uint8_t v___x_1977_; lean_object* v___x_1978_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1973_);
v_fst_1975_ = lean_ctor_get(v_a_1974_, 0);
lean_inc(v_fst_1975_);
lean_dec(v_a_1974_);
v___x_1976_ = 0;
v___x_1977_ = 0;
v___x_1978_ = l_Lean_Compiler_LCNF_Code_internalize(v___x_1976_, v_code_1955_, v_fst_1975_, v___x_1977_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref(v___x_1978_);
lean_inc(v_a_1979_);
v___x_1980_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_a_1979_, v_mustInline_1957_, v_a_1959_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v___x_1980_, 0);
lean_dec(v_unused_1988_);
v___x_1982_ = v___x_1980_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_dec(v___x_1980_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v_a_1979_);
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1979_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_a_1979_);
v_a_1989_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1980_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1980_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
return v___x_1978_;
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v_code_1955_);
v_a_1997_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1973_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1973_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object* v_params_2005_, lean_object* v_code_2006_, lean_object* v_args_2007_, lean_object* v_mustInline_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
uint8_t v_mustInline_boxed_2017_; lean_object* v_res_2018_; 
v_mustInline_boxed_2017_ = lean_unbox(v_mustInline_2008_);
v_res_2018_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_2005_, v_code_2006_, v_args_2007_, v_mustInline_boxed_2017_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_params_2005_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0(lean_object* v_00_u03b2_2019_, lean_object* v_m_2020_, lean_object* v_a_2021_, lean_object* v_b_2022_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_m_2020_, v_a_2021_, v_b_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(lean_object* v_as_2024_, size_t v_sz_2025_, size_t v_i_2026_, lean_object* v_b_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_2024_, v_sz_2025_, v_i_2026_, v_b_2027_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___boxed(lean_object* v_as_2037_, lean_object* v_sz_2038_, lean_object* v_i_2039_, lean_object* v_b_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
size_t v_sz_boxed_2049_; size_t v_i_boxed_2050_; lean_object* v_res_2051_; 
v_sz_boxed_2049_ = lean_unbox_usize(v_sz_2038_);
lean_dec(v_sz_2038_);
v_i_boxed_2050_ = lean_unbox_usize(v_i_2039_);
lean_dec(v_i_2039_);
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(v_as_2037_, v_sz_boxed_2049_, v_i_boxed_2050_, v_b_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec_ref(v_as_2037_);
return v_res_2051_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(lean_object* v_00_u03b2_2052_, lean_object* v_a_2053_, lean_object* v_x_2054_){
_start:
{
uint8_t v___x_2055_; 
v___x_2055_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_2053_, v_x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2056_, lean_object* v_a_2057_, lean_object* v_x_2058_){
_start:
{
uint8_t v_res_2059_; lean_object* v_r_2060_; 
v_res_2059_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(v_00_u03b2_2056_, v_a_2057_, v_x_2058_);
lean_dec(v_x_2058_);
lean_dec(v_a_2057_);
v_r_2060_ = lean_box(v_res_2059_);
return v_r_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1(lean_object* v_00_u03b2_2061_, lean_object* v_data_2062_){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(v_data_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2(lean_object* v_00_u03b2_2064_, lean_object* v_a_2065_, lean_object* v_b_2066_, lean_object* v_x_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_2065_, v_b_2066_, v_x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2069_, lean_object* v_i_2070_, lean_object* v_source_2071_, lean_object* v_target_2072_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(v_i_2070_, v_source_2071_, v_target_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2074_, lean_object* v_x_2075_, lean_object* v_x_2076_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2075_, v_x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object* v_decl_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
uint8_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = 0;
v___x_2083_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2082_, v_decl_2078_, v_a_2080_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v___x_2084_; 
lean_dec_ref(v___x_2083_);
v___x_2084_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2079_);
return v___x_2084_;
}
else
{
return v___x_2083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg___boxed(lean_object* v_decl_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2085_, v_a_2086_, v_a_2087_);
lean_dec(v_a_2087_);
lean_dec(v_a_2086_);
lean_dec_ref(v_decl_2085_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object* v_decl_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2090_, v_a_2092_, v_a_2095_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object* v_decl_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(v_decl_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec_ref(v_decl_2100_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object* v_decl_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
uint8_t v___x_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = 0;
v___x_2115_ = 1;
v___x_2116_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_2114_, v_decl_2110_, v___x_2115_, v_a_2112_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; 
lean_dec_ref(v___x_2116_);
v___x_2117_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2111_);
return v___x_2117_;
}
else
{
return v___x_2116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg___boxed(lean_object* v_decl_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2118_, v_a_2119_, v_a_2120_);
lean_dec(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_decl_2118_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object* v_decl_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2123_, v_a_2125_, v_a_2128_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object* v_decl_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(v_decl_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec_ref(v_decl_2133_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object* v_fvarId_2143_, lean_object* v_fvarId_x27_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v___x_2151_; lean_object* v_subst_2152_; lean_object* v_used_2153_; lean_object* v_binderRenaming_2154_; lean_object* v_funDeclInfoMap_2155_; uint8_t v_simplified_2156_; lean_object* v_visited_2157_; lean_object* v_inline_2158_; lean_object* v_inlineLocal_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2229_; 
v___x_2151_ = lean_st_ref_take(v_a_2145_);
v_subst_2152_ = lean_ctor_get(v___x_2151_, 0);
v_used_2153_ = lean_ctor_get(v___x_2151_, 1);
v_binderRenaming_2154_ = lean_ctor_get(v___x_2151_, 2);
v_funDeclInfoMap_2155_ = lean_ctor_get(v___x_2151_, 3);
v_simplified_2156_ = lean_ctor_get_uint8(v___x_2151_, sizeof(void*)*7);
v_visited_2157_ = lean_ctor_get(v___x_2151_, 4);
v_inline_2158_ = lean_ctor_get(v___x_2151_, 5);
v_inlineLocal_2159_ = lean_ctor_get(v___x_2151_, 6);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2161_ = v___x_2151_;
v_isShared_2162_ = v_isSharedCheck_2229_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_inlineLocal_2159_);
lean_inc(v_inline_2158_);
lean_inc(v_visited_2157_);
lean_inc(v_funDeclInfoMap_2155_);
lean_inc(v_binderRenaming_2154_);
lean_inc(v_used_2153_);
lean_inc(v_subst_2152_);
lean_dec(v___x_2151_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2229_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2166_; 
lean_inc(v_fvarId_x27_2144_);
v___x_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2163_, 0, v_fvarId_x27_2144_);
lean_inc(v_fvarId_2143_);
v___x_2164_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_subst_2152_, v_fvarId_2143_, v___x_2163_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2164_);
v___x_2166_ = v___x_2161_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_used_2153_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_binderRenaming_2154_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_funDeclInfoMap_2155_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v_visited_2157_);
lean_ctor_set(v_reuseFailAlloc_2228_, 5, v_inline_2158_);
lean_ctor_set(v_reuseFailAlloc_2228_, 6, v_inlineLocal_2159_);
lean_ctor_set_uint8(v_reuseFailAlloc_2228_, sizeof(void*)*7, v_simplified_2156_);
v___x_2166_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = lean_st_ref_set(v_a_2145_, v___x_2166_);
v___x_2168_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_2143_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2219_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2219_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2219_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
uint8_t v___x_2173_; 
v___x_2173_ = l_Lean_Name_isInternal(v_a_2169_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_del_object(v___x_2171_);
lean_inc(v_fvarId_x27_2144_);
v___x_2174_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_x27_2144_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2206_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2206_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2206_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
uint8_t v___x_2179_; 
v___x_2179_ = l_Lean_Name_isInternal(v_a_2175_);
lean_dec(v_a_2175_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
lean_dec(v_a_2169_);
lean_dec(v_fvarId_x27_2144_);
v___x_2180_ = lean_box(0);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2180_);
v___x_2182_ = v___x_2177_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
else
{
lean_object* v___x_2184_; lean_object* v_subst_2185_; lean_object* v_used_2186_; lean_object* v_binderRenaming_2187_; lean_object* v_funDeclInfoMap_2188_; uint8_t v_simplified_2189_; lean_object* v_visited_2190_; lean_object* v_inline_2191_; lean_object* v_inlineLocal_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2205_; 
v___x_2184_ = lean_st_ref_take(v_a_2145_);
v_subst_2185_ = lean_ctor_get(v___x_2184_, 0);
v_used_2186_ = lean_ctor_get(v___x_2184_, 1);
v_binderRenaming_2187_ = lean_ctor_get(v___x_2184_, 2);
v_funDeclInfoMap_2188_ = lean_ctor_get(v___x_2184_, 3);
v_simplified_2189_ = lean_ctor_get_uint8(v___x_2184_, sizeof(void*)*7);
v_visited_2190_ = lean_ctor_get(v___x_2184_, 4);
v_inline_2191_ = lean_ctor_get(v___x_2184_, 5);
v_inlineLocal_2192_ = lean_ctor_get(v___x_2184_, 6);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2194_ = v___x_2184_;
v_isShared_2195_ = v_isSharedCheck_2205_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_inlineLocal_2192_);
lean_inc(v_inline_2191_);
lean_inc(v_visited_2190_);
lean_inc(v_funDeclInfoMap_2188_);
lean_inc(v_binderRenaming_2187_);
lean_inc(v_used_2186_);
lean_inc(v_subst_2185_);
lean_dec(v___x_2184_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2205_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_x27_2144_, v_a_2169_, v_binderRenaming_2187_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 2, v___x_2196_);
v___x_2198_ = v___x_2194_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_subst_2185_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_used_2186_);
lean_ctor_set(v_reuseFailAlloc_2204_, 2, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2204_, 3, v_funDeclInfoMap_2188_);
lean_ctor_set(v_reuseFailAlloc_2204_, 4, v_visited_2190_);
lean_ctor_set(v_reuseFailAlloc_2204_, 5, v_inline_2191_);
lean_ctor_set(v_reuseFailAlloc_2204_, 6, v_inlineLocal_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*7, v_simplified_2189_);
v___x_2198_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
v___x_2199_ = lean_st_ref_set(v_a_2145_, v___x_2198_);
v___x_2200_ = lean_box(0);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2200_);
v___x_2202_ = v___x_2177_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_a_2169_);
lean_dec(v_fvarId_x27_2144_);
v_a_2207_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2174_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2174_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
lean_dec(v_a_2169_);
lean_dec(v_fvarId_x27_2144_);
v___x_2215_ = lean_box(0);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2215_);
v___x_2217_ = v___x_2171_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_fvarId_x27_2144_);
v_a_2220_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2168_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2168_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg___boxed(lean_object* v_fvarId_2230_, lean_object* v_fvarId_x27_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2230_, v_fvarId_x27_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object* v_fvarId_2239_, lean_object* v_fvarId_x27_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2239_, v_fvarId_x27_2240_, v_a_2242_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___boxed(lean_object* v_fvarId_2250_, lean_object* v_fvarId_x27_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst(v_fvarId_2250_, v_fvarId_x27_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
return v_res_2260_;
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
