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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
v___x_552_ = lean_st_ref_put(v_a_531_, v___x_551_);
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
v___x_571_ = lean_st_ref_put(v_a_531_, v___x_570_);
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
v___x_628_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_628_, 10, v___x_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_options_635_; lean_object* v_ref_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_options_635_ = lean_ctor_get(v___y_632_, 1);
v_ref_636_ = lean_ctor_get(v___y_632_, 4);
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
v_options_712_ = lean_ctor_get(v___y_709_, 1);
v_ref_713_ = lean_ctor_get(v___y_709_, 4);
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
v___x_763_ = lean_st_ref_put(v___y_710_, v___x_762_);
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
size_t v_x_6994__boxed_859_; lean_object* v_res_860_; 
v_x_6994__boxed_859_ = lean_unbox_usize(v_x_857_);
lean_dec(v_x_857_);
v_res_860_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_856_, v_x_6994__boxed_859_, v_x_858_);
lean_dec(v_x_858_);
lean_dec_ref(v_x_856_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
uint64_t v___y_864_; 
if (lean_obj_tag(v_x_862_) == 0)
{
uint64_t v___x_867_; 
v___x_867_ = 1723ULL;
v___y_864_ = v___x_867_;
goto v___jp_863_;
}
else
{
uint64_t v_hash_868_; 
v_hash_868_ = lean_ctor_get_uint64(v_x_862_, sizeof(void*)*2);
v___y_864_ = v_hash_868_;
goto v___jp_863_;
}
v___jp_863_:
{
size_t v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_uint64_to_usize(v___y_864_);
v___x_866_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_861_, v___x_865_, v_x_862_);
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___boxed(lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_x_869_, v_x_870_);
lean_dec(v_x_870_);
lean_dec_ref(v_x_869_);
return v_res_871_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__0));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__2));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__4));
v___x_880_ = l_Lean_stringToMessageData(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12(void){
_start:
{
lean_object* v_cls_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_cls_891_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9));
v___x_892_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__11));
v___x_893_ = l_Lean_Name_append(v___x_892_, v_cls_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t v_recursive_894_, lean_object* v_declName_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___y_905_; uint8_t v_inlineIfReduce_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v_options_1028_; uint8_t v_hasTrace_1029_; 
v_options_1028_ = lean_ctor_get(v_a_901_, 1);
v_hasTrace_1029_ = lean_ctor_get_uint8(v_options_1028_, sizeof(void*)*1);
if (v_hasTrace_1029_ == 0)
{
v___y_1017_ = v_a_896_;
v___y_1018_ = v_a_897_;
v___y_1019_ = v_a_898_;
v___y_1020_ = v_a_899_;
v___y_1021_ = v_a_900_;
v___y_1022_ = v_a_901_;
v___y_1023_ = v_a_902_;
goto v___jp_1016_;
}
else
{
lean_object* v_toCold_1030_; lean_object* v_inheritedTraceOptions_1031_; lean_object* v_cls_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_toCold_1030_ = lean_ctor_get(v_a_901_, 0);
v_inheritedTraceOptions_1031_ = lean_ctor_get(v_toCold_1030_, 4);
v_cls_1032_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9));
v___x_1033_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12);
v___x_1034_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1031_, v_options_1028_, v___x_1033_);
if (v___x_1034_ == 0)
{
v___y_1017_ = v_a_896_;
v___y_1018_ = v_a_897_;
v___y_1019_ = v_a_898_;
v___y_1020_ = v_a_899_;
v___y_1021_ = v_a_900_;
v___y_1022_ = v_a_901_;
v___y_1023_ = v_a_902_;
goto v___jp_1016_;
}
else
{
uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = 0;
lean_inc(v_declName_895_);
v___x_1036_ = l_Lean_MessageData_ofConstName(v_declName_895_, v___x_1035_);
v___x_1037_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_1032_, v___x_1036_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_dec_ref_known(v___x_1037_, 1);
v___y_1017_ = v_a_896_;
v___y_1018_ = v_a_897_;
v___y_1019_ = v_a_898_;
v___y_1020_ = v_a_899_;
v___y_1021_ = v_a_900_;
v___y_1022_ = v_a_901_;
v___y_1023_ = v_a_902_;
goto v___jp_1016_;
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_declName_895_);
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
v___jp_904_:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_910_);
if (lean_obj_tag(v___x_914_) == 0)
{
if (v_recursive_894_ == 0)
{
lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_declName_895_);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v___x_914_, 0);
lean_dec(v_unused_922_);
v___x_916_ = v___x_914_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_dec(v___x_914_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___y_905_);
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___y_905_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
else
{
if (v_inlineIfReduce_906_ == 0)
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_declName_895_);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; 
v_unused_930_ = lean_ctor_get(v___x_914_, 0);
lean_dec(v_unused_930_);
v___x_924_ = v___x_914_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_dec(v___x_914_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___y_905_);
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___y_905_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_972_; 
v_a_931_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_972_ == 0)
{
v___x_933_ = v___x_914_;
v_isShared_934_ = v_isSharedCheck_972_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_914_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_972_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_maxRecInlineIfReduce_935_; uint8_t v___x_936_; 
v_maxRecInlineIfReduce_935_ = lean_ctor_get(v_a_931_, 2);
lean_inc(v_maxRecInlineIfReduce_935_);
lean_dec(v_a_931_);
v___x_936_ = lean_nat_dec_lt(v_maxRecInlineIfReduce_935_, v___y_905_);
lean_dec(v_maxRecInlineIfReduce_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_938_; 
lean_dec(v_declName_895_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___y_905_);
v___x_938_ = v___x_933_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___y_905_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_object* v___x_940_; 
lean_del_object(v___x_933_);
lean_dec(v___y_905_);
v___x_940_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_910_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v_maxRecInlineIfReduce_942_; lean_object* v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v_maxRecInlineIfReduce_942_ = lean_ctor_get(v_a_941_, 2);
lean_inc(v_maxRecInlineIfReduce_942_);
lean_dec(v_a_941_);
v___x_943_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1);
v___x_944_ = 0;
v___x_945_ = l_Lean_MessageData_ofConstName(v_declName_895_, v___x_944_);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_943_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = l_Nat_reprFast(v_maxRecInlineIfReduce_942_);
v___x_950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
v___x_951_ = l_Lean_MessageData_ofFormat(v___x_950_);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_948_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_954_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec(v_declName_895_);
v_a_964_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_940_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_940_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
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
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v___y_905_);
lean_dec(v_declName_895_);
v_a_973_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_914_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_914_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
v___jp_981_:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_985_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; uint8_t v___x_992_; lean_object* v___x_993_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = lean_unbox(v_a_991_);
lean_dec(v_a_991_);
lean_inc(v_declName_895_);
v___x_993_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_895_, v___x_992_, v___y_986_, v___y_988_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
v___x_995_ = lean_unsigned_to_nat(1u);
v___x_996_ = lean_nat_add(v___y_989_, v___x_995_);
lean_dec(v___y_989_);
if (lean_obj_tag(v_a_994_) == 1)
{
lean_object* v_val_997_; uint8_t v___x_998_; 
v_val_997_ = lean_ctor_get(v_a_994_, 0);
lean_inc(v_val_997_);
lean_dec_ref_known(v_a_994_, 1);
v___x_998_ = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(v_val_997_);
lean_dec(v_val_997_);
v___y_905_ = v___x_996_;
v_inlineIfReduce_906_ = v___x_998_;
v___y_907_ = v___y_983_;
v___y_908_ = v___y_982_;
v___y_909_ = v___y_987_;
v___y_910_ = v___y_985_;
v___y_911_ = v___y_984_;
v___y_912_ = v___y_986_;
v___y_913_ = v___y_988_;
goto v___jp_904_;
}
else
{
uint8_t v___x_999_; 
lean_dec(v_a_994_);
v___x_999_ = 0;
v___y_905_ = v___x_996_;
v_inlineIfReduce_906_ = v___x_999_;
v___y_907_ = v___y_983_;
v___y_908_ = v___y_982_;
v___y_909_ = v___y_987_;
v___y_910_ = v___y_985_;
v___y_911_ = v___y_984_;
v___y_912_ = v___y_986_;
v___y_913_ = v___y_988_;
goto v___jp_904_;
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v___y_989_);
lean_dec(v_declName_895_);
v_a_1000_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_993_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_993_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v___y_989_);
lean_dec(v_declName_895_);
v_a_1008_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_990_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_990_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
v___jp_1016_:
{
lean_object* v_inlineStackOccs_1024_; lean_object* v___x_1025_; 
v_inlineStackOccs_1024_ = lean_ctor_get(v___y_1017_, 3);
v___x_1025_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_inlineStackOccs_1024_, v_declName_895_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_unsigned_to_nat(0u);
v___y_982_ = v___y_1018_;
v___y_983_ = v___y_1017_;
v___y_984_ = v___y_1021_;
v___y_985_ = v___y_1020_;
v___y_986_ = v___y_1022_;
v___y_987_ = v___y_1019_;
v___y_988_ = v___y_1023_;
v___y_989_ = v___x_1026_;
goto v___jp_981_;
}
else
{
lean_object* v_val_1027_; 
v_val_1027_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_val_1027_);
lean_dec_ref_known(v___x_1025_, 1);
v___y_982_ = v___y_1018_;
v___y_983_ = v___y_1017_;
v___y_984_ = v___y_1021_;
v___y_985_ = v___y_1020_;
v___y_986_ = v___y_1022_;
v___y_987_ = v___y_1019_;
v___y_988_ = v___y_1023_;
v___y_989_ = v_val_1027_;
goto v___jp_981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___boxed(lean_object* v_recursive_1046_, lean_object* v_declName_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
uint8_t v_recursive_boxed_1056_; lean_object* v_res_1057_; 
v_recursive_boxed_1056_ = lean_unbox(v_recursive_1046_);
v_res_1057_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_boxed_1056_, v_declName_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1(lean_object* v_00_u03b2_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_x_1059_, v_x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___boxed(lean_object* v_00_u03b2_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1(v_00_u03b2_1062_, v_x_1063_, v_x_1064_);
lean_dec(v_x_1064_);
lean_dec_ref(v_x_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(lean_object* v_00_u03b2_1066_, lean_object* v_x_1067_, size_t v_x_1068_, lean_object* v_x_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_1067_, v_x_1068_, v_x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_){
_start:
{
size_t v_x_7404__boxed_1075_; lean_object* v_res_1076_; 
v_x_7404__boxed_1075_ = lean_unbox_usize(v_x_1073_);
lean_dec(v_x_1073_);
v_res_1076_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(v_00_u03b2_1071_, v_x_1072_, v_x_7404__boxed_1075_, v_x_1074_);
lean_dec(v_x_1074_);
lean_dec_ref(v_x_1072_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1077_, lean_object* v_keys_1078_, lean_object* v_vals_1079_, lean_object* v_heq_1080_, lean_object* v_i_1081_, lean_object* v_k_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(v_keys_1078_, v_vals_1079_, v_i_1081_, v_k_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1084_, lean_object* v_keys_1085_, lean_object* v_vals_1086_, lean_object* v_heq_1087_, lean_object* v_i_1088_, lean_object* v_k_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3(v_00_u03b2_1084_, v_keys_1085_, v_vals_1086_, v_heq_1087_, v_i_1088_, v_k_1089_);
lean_dec(v_k_1089_);
lean_dec_ref(v_vals_1086_);
lean_dec_ref(v_keys_1085_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg(lean_object* v_value_1093_, uint8_t v_recursive_1094_, lean_object* v_x_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
if (lean_obj_tag(v_value_1093_) == 3)
{
lean_object* v_declName_1104_; lean_object* v___x_1105_; 
v_declName_1104_ = lean_ctor_get(v_value_1093_, 0);
lean_inc_n(v_declName_1104_, 2);
lean_dec_ref_known(v_value_1093_, 3);
v___x_1105_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1094_, v_declName_1104_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v_declName_1107_; lean_object* v_config_1108_; lean_object* v_inlineStack_1109_; lean_object* v_inlineStackOccs_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_declName_1107_ = lean_ctor_get(v_a_1096_, 0);
v_config_1108_ = lean_ctor_get(v_a_1096_, 1);
v_inlineStack_1109_ = lean_ctor_get(v_a_1096_, 2);
v_inlineStackOccs_1110_ = lean_ctor_get(v_a_1096_, 3);
v___x_1111_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0));
v___x_1112_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1));
lean_inc(v_inlineStack_1109_);
lean_inc(v_declName_1104_);
v___x_1113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1113_, 0, v_declName_1104_);
lean_ctor_set(v___x_1113_, 1, v_inlineStack_1109_);
lean_inc_ref(v_inlineStackOccs_1110_);
v___x_1114_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1111_, v___x_1112_, v_inlineStackOccs_1110_, v_declName_1104_, v_a_1106_);
lean_inc_ref(v_config_1108_);
lean_inc(v_declName_1107_);
v___x_1115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1115_, 0, v_declName_1107_);
lean_ctor_set(v___x_1115_, 1, v_config_1108_);
lean_ctor_set(v___x_1115_, 2, v___x_1113_);
lean_ctor_set(v___x_1115_, 3, v___x_1114_);
lean_inc(v_a_1102_);
lean_inc_ref(v_a_1101_);
lean_inc(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc_ref(v_a_1098_);
lean_inc(v_a_1097_);
v___x_1116_ = lean_apply_8(v_x_1095_, v___x_1115_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, lean_box(0));
return v___x_1116_;
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec(v_declName_1104_);
lean_dec_ref(v_x_1095_);
v_a_1117_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1105_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1105_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
else
{
lean_object* v___x_1125_; 
lean_dec(v_value_1093_);
lean_inc(v_a_1102_);
lean_inc_ref(v_a_1101_);
lean_inc(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc_ref(v_a_1098_);
lean_inc(v_a_1097_);
lean_inc_ref(v_a_1096_);
v___x_1125_ = lean_apply_8(v_x_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, lean_box(0));
return v___x_1125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg___boxed(lean_object* v_value_1126_, lean_object* v_recursive_1127_, lean_object* v_x_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
uint8_t v_recursive_boxed_1137_; lean_object* v_res_1138_; 
v_recursive_boxed_1137_ = lean_unbox(v_recursive_1127_);
v_res_1138_ = l_Lean_Compiler_LCNF_Simp_withInlining___redArg(v_value_1126_, v_recursive_boxed_1137_, v_x_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining(lean_object* v_00_u03b1_1139_, lean_object* v_value_1140_, uint8_t v_recursive_1141_, lean_object* v_x_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
if (lean_obj_tag(v_value_1140_) == 3)
{
lean_object* v_declName_1151_; lean_object* v___x_1152_; 
v_declName_1151_ = lean_ctor_get(v_value_1140_, 0);
lean_inc_n(v_declName_1151_, 2);
lean_dec_ref_known(v_value_1140_, 3);
v___x_1152_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1141_, v_declName_1151_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v_declName_1154_; lean_object* v_config_1155_; lean_object* v_inlineStack_1156_; lean_object* v_inlineStackOccs_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1152_, 1);
v_declName_1154_ = lean_ctor_get(v_a_1143_, 0);
v_config_1155_ = lean_ctor_get(v_a_1143_, 1);
v_inlineStack_1156_ = lean_ctor_get(v_a_1143_, 2);
v_inlineStackOccs_1157_ = lean_ctor_get(v_a_1143_, 3);
v___x_1158_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0));
v___x_1159_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1));
lean_inc(v_inlineStack_1156_);
lean_inc(v_declName_1151_);
v___x_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_declName_1151_);
lean_ctor_set(v___x_1160_, 1, v_inlineStack_1156_);
lean_inc_ref(v_inlineStackOccs_1157_);
v___x_1161_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1158_, v___x_1159_, v_inlineStackOccs_1157_, v_declName_1151_, v_a_1153_);
lean_inc_ref(v_config_1155_);
lean_inc(v_declName_1154_);
v___x_1162_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1162_, 0, v_declName_1154_);
lean_ctor_set(v___x_1162_, 1, v_config_1155_);
lean_ctor_set(v___x_1162_, 2, v___x_1160_);
lean_ctor_set(v___x_1162_, 3, v___x_1161_);
lean_inc(v_a_1149_);
lean_inc_ref(v_a_1148_);
lean_inc(v_a_1147_);
lean_inc_ref(v_a_1146_);
lean_inc_ref(v_a_1145_);
lean_inc(v_a_1144_);
v___x_1163_ = lean_apply_8(v_x_1142_, v___x_1162_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, lean_box(0));
return v___x_1163_;
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_declName_1151_);
lean_dec_ref(v_x_1142_);
v_a_1164_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1152_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1152_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
else
{
lean_object* v___x_1172_; 
lean_dec(v_value_1140_);
lean_inc(v_a_1149_);
lean_inc_ref(v_a_1148_);
lean_inc(v_a_1147_);
lean_inc_ref(v_a_1146_);
lean_inc_ref(v_a_1145_);
lean_inc(v_a_1144_);
lean_inc_ref(v_a_1143_);
v___x_1172_ = lean_apply_8(v_x_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, lean_box(0));
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___boxed(lean_object* v_00_u03b1_1173_, lean_object* v_value_1174_, lean_object* v_recursive_1175_, lean_object* v_x_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
uint8_t v_recursive_boxed_1185_; lean_object* v_res_1186_; 
v_recursive_boxed_1185_ = lean_unbox(v_recursive_1175_);
v_res_1186_ = l_Lean_Compiler_LCNF_Simp_withInlining(v_00_u03b1_1173_, v_value_1174_, v_recursive_boxed_1185_, v_x_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
return v_res_1186_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__0));
v___x_1189_ = l_Lean_stringToMessageData(v___x_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__3));
v___x_1194_ = l_Lean_MessageData_ofFormat(v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(lean_object* v_as_x27_1195_, lean_object* v_b_1196_){
_start:
{
if (lean_obj_tag(v_as_x27_1195_) == 0)
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_b_1196_);
return v___x_1198_;
}
else
{
lean_object* v_snd_1199_; lean_object* v_head_1200_; lean_object* v_tail_1201_; lean_object* v_fst_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1243_; 
v_snd_1199_ = lean_ctor_get(v_b_1196_, 1);
lean_inc(v_snd_1199_);
v_head_1200_ = lean_ctor_get(v_as_x27_1195_, 0);
v_tail_1201_ = lean_ctor_get(v_as_x27_1195_, 1);
v_fst_1202_ = lean_ctor_get(v_b_1196_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_b_1196_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v_b_1196_, 1);
lean_dec(v_unused_1244_);
v___x_1204_ = v_b_1196_;
v_isShared_1205_ = v_isSharedCheck_1243_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_fst_1202_);
lean_dec(v_b_1196_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1243_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_fst_1206_; lean_object* v_snd_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1242_; 
v_fst_1206_ = lean_ctor_get(v_snd_1199_, 0);
v_snd_1207_ = lean_ctor_get(v_snd_1199_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_snd_1199_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1209_ = v_snd_1199_;
v_isShared_1210_ = v_isSharedCheck_1242_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_snd_1207_);
lean_inc(v_fst_1206_);
lean_dec(v_snd_1199_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1242_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
uint8_t v___x_1211_; 
v___x_1211_ = lean_name_eq(v_fst_1206_, v_head_1200_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
lean_dec(v_snd_1207_);
lean_dec(v_fst_1206_);
v___x_1212_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1);
lean_inc_n(v_head_1200_, 2);
v___x_1213_ = l_Lean_MessageData_ofConstName(v_head_1200_, v___x_1211_);
v___x_1214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v___x_1212_);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_fst_1202_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = lean_box(v___x_1211_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v___x_1216_);
lean_ctor_set(v___x_1209_, 0, v_head_1200_);
v___x_1218_ = v___x_1209_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_head_1200_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1220_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1218_);
lean_ctor_set(v___x_1204_, 0, v___x_1215_);
v___x_1220_ = v___x_1204_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
v_as_x27_1195_ = v_tail_1201_;
v_b_1196_ = v___x_1220_;
goto _start;
}
}
}
else
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_unbox(v_snd_1207_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1229_; 
lean_dec(v_snd_1207_);
v___x_1225_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v_fst_1202_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = lean_box(v___x_1211_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v___x_1227_);
v___x_1229_ = v___x_1209_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_fst_1206_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1229_);
lean_ctor_set(v___x_1204_, 0, v___x_1226_);
v___x_1231_ = v___x_1204_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
v_as_x27_1195_ = v_tail_1201_;
v_b_1196_ = v___x_1231_;
goto _start;
}
}
}
else
{
lean_object* v___x_1236_; 
if (v_isShared_1210_ == 0)
{
v___x_1236_ = v___x_1209_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_fst_1206_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_snd_1207_);
v___x_1236_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1238_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1236_);
v___x_1238_ = v___x_1204_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_fst_1202_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
v_as_x27_1195_ = v_tail_1201_;
v_b_1196_ = v___x_1238_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___boxed(lean_object* v_as_x27_1245_, lean_object* v_b_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_1245_, v_b_1246_);
lean_dec(v_as_x27_1245_);
return v_res_1248_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = l_Lean_maxRecDepthErrorMessage;
v___x_1250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0);
v___x_1252_ = l_Lean_MessageData_ofFormat(v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__2));
v___x_1255_ = l_Lean_stringToMessageData(v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_inlineStack_1264_; 
v_inlineStack_1264_ = lean_ctor_get(v_a_1256_, 2);
if (lean_obj_tag(v_inlineStack_1264_) == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1);
v___x_1266_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_1265_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
return v___x_1266_;
}
else
{
lean_object* v_head_1267_; lean_object* v_tail_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v_a_1277_; lean_object* v_fst_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1287_; 
v_head_1267_ = lean_ctor_get(v_inlineStack_1264_, 0);
v_tail_1268_ = lean_ctor_get(v_inlineStack_1264_, 1);
v___x_1269_ = 0;
lean_inc_n(v_head_1267_, 2);
v___x_1270_ = l_Lean_MessageData_ofConstName(v_head_1267_, v___x_1269_);
v___x_1271_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1);
v___x_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lean_box(v___x_1269_);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_head_1267_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1272_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_tail_1268_, v___x_1275_);
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref(v___x_1276_);
v_fst_1278_ = lean_ctor_get(v_a_1277_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_a_1277_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v_a_1277_, 1);
lean_dec(v_unused_1288_);
v___x_1280_ = v_a_1277_;
v_isShared_1281_ = v_isSharedCheck_1287_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_fst_1278_);
lean_dec(v_a_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1287_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3);
if (v_isShared_1281_ == 0)
{
lean_ctor_set_tag(v___x_1280_, 7);
lean_ctor_set(v___x_1280_, 1, v_fst_1278_);
lean_ctor_set(v___x_1280_, 0, v___x_1282_);
v___x_1284_ = v___x_1280_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_fst_1278_);
v___x_1284_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_1284_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
return v___x_1285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___boxed(lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object* v_00_u03b1_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___boxed(lean_object* v_00_u03b1_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(v_00_u03b1_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(lean_object* v_as_1318_, lean_object* v_as_x27_1319_, lean_object* v_b_1320_, lean_object* v_a_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_1319_, v_b_1320_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___boxed(lean_object* v_as_1331_, lean_object* v_as_x27_1332_, lean_object* v_b_1333_, lean_object* v_a_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(v_as_1331_, v_as_x27_1332_, v_b_1333_, v_a_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v_as_x27_1332_);
lean_dec(v_as_1331_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(lean_object* v_x_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_toCold_1353_; lean_object* v_options_1354_; lean_object* v_currRecDepth_1355_; lean_object* v_maxRecDepth_1356_; lean_object* v_ref_1357_; lean_object* v_currNamespace_1358_; lean_object* v_openDecls_1359_; lean_object* v_initHeartbeats_1360_; lean_object* v_maxHeartbeats_1361_; lean_object* v_currMacroScope_1362_; uint8_t v_diag_1363_; uint8_t v_suppressElabErrors_1364_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v_toCold_1353_ = lean_ctor_get(v_a_1350_, 0);
v_options_1354_ = lean_ctor_get(v_a_1350_, 1);
v_currRecDepth_1355_ = lean_ctor_get(v_a_1350_, 2);
v_maxRecDepth_1356_ = lean_ctor_get(v_a_1350_, 3);
v_ref_1357_ = lean_ctor_get(v_a_1350_, 4);
v_currNamespace_1358_ = lean_ctor_get(v_a_1350_, 5);
v_openDecls_1359_ = lean_ctor_get(v_a_1350_, 6);
v_initHeartbeats_1360_ = lean_ctor_get(v_a_1350_, 7);
v_maxHeartbeats_1361_ = lean_ctor_get(v_a_1350_, 8);
v_currMacroScope_1362_ = lean_ctor_get(v_a_1350_, 9);
v_diag_1363_ = lean_ctor_get_uint8(v_a_1350_, sizeof(void*)*10);
v_suppressElabErrors_1364_ = lean_ctor_get_uint8(v_a_1350_, sizeof(void*)*10 + 1);
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = lean_nat_dec_eq(v_maxRecDepth_1356_, v___x_1370_);
if (v___x_1371_ == 0)
{
uint8_t v___x_1372_; 
v___x_1372_ = lean_nat_dec_eq(v_currRecDepth_1355_, v_maxRecDepth_1356_);
if (v___x_1372_ == 0)
{
goto v___jp_1365_;
}
else
{
lean_object* v___x_1373_; 
lean_dec_ref(v_x_1344_);
v___x_1373_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
return v___x_1373_;
}
}
else
{
goto v___jp_1365_;
}
v___jp_1365_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1366_ = lean_unsigned_to_nat(1u);
v___x_1367_ = lean_nat_add(v_currRecDepth_1355_, v___x_1366_);
lean_inc(v_currMacroScope_1362_);
lean_inc(v_maxHeartbeats_1361_);
lean_inc(v_initHeartbeats_1360_);
lean_inc(v_openDecls_1359_);
lean_inc(v_currNamespace_1358_);
lean_inc(v_ref_1357_);
lean_inc(v_maxRecDepth_1356_);
lean_inc_ref(v_options_1354_);
lean_inc_ref(v_toCold_1353_);
v___x_1368_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1368_, 0, v_toCold_1353_);
lean_ctor_set(v___x_1368_, 1, v_options_1354_);
lean_ctor_set(v___x_1368_, 2, v___x_1367_);
lean_ctor_set(v___x_1368_, 3, v_maxRecDepth_1356_);
lean_ctor_set(v___x_1368_, 4, v_ref_1357_);
lean_ctor_set(v___x_1368_, 5, v_currNamespace_1358_);
lean_ctor_set(v___x_1368_, 6, v_openDecls_1359_);
lean_ctor_set(v___x_1368_, 7, v_initHeartbeats_1360_);
lean_ctor_set(v___x_1368_, 8, v_maxHeartbeats_1361_);
lean_ctor_set(v___x_1368_, 9, v_currMacroScope_1362_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*10, v_diag_1363_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*10 + 1, v_suppressElabErrors_1364_);
lean_inc(v_a_1351_);
lean_inc(v_a_1349_);
lean_inc_ref(v_a_1348_);
lean_inc_ref(v_a_1347_);
lean_inc(v_a_1346_);
lean_inc_ref(v_a_1345_);
v___x_1369_ = lean_apply_8(v_x_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v___x_1368_, v_a_1351_, lean_box(0));
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg___boxed(lean_object* v_x_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(v_x_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth(lean_object* v_00_u03b1_1384_, lean_object* v_x_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_toCold_1394_; lean_object* v_options_1395_; lean_object* v_currRecDepth_1396_; lean_object* v_maxRecDepth_1397_; lean_object* v_ref_1398_; lean_object* v_currNamespace_1399_; lean_object* v_openDecls_1400_; lean_object* v_initHeartbeats_1401_; lean_object* v_maxHeartbeats_1402_; lean_object* v_currMacroScope_1403_; uint8_t v_diag_1404_; uint8_t v_suppressElabErrors_1405_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_toCold_1394_ = lean_ctor_get(v_a_1391_, 0);
v_options_1395_ = lean_ctor_get(v_a_1391_, 1);
v_currRecDepth_1396_ = lean_ctor_get(v_a_1391_, 2);
v_maxRecDepth_1397_ = lean_ctor_get(v_a_1391_, 3);
v_ref_1398_ = lean_ctor_get(v_a_1391_, 4);
v_currNamespace_1399_ = lean_ctor_get(v_a_1391_, 5);
v_openDecls_1400_ = lean_ctor_get(v_a_1391_, 6);
v_initHeartbeats_1401_ = lean_ctor_get(v_a_1391_, 7);
v_maxHeartbeats_1402_ = lean_ctor_get(v_a_1391_, 8);
v_currMacroScope_1403_ = lean_ctor_get(v_a_1391_, 9);
v_diag_1404_ = lean_ctor_get_uint8(v_a_1391_, sizeof(void*)*10);
v_suppressElabErrors_1405_ = lean_ctor_get_uint8(v_a_1391_, sizeof(void*)*10 + 1);
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = lean_nat_dec_eq(v_maxRecDepth_1397_, v___x_1411_);
if (v___x_1412_ == 0)
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_nat_dec_eq(v_currRecDepth_1396_, v_maxRecDepth_1397_);
if (v___x_1413_ == 0)
{
goto v___jp_1406_;
}
else
{
lean_object* v___x_1414_; 
lean_dec_ref(v_x_1385_);
v___x_1414_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
return v___x_1414_;
}
}
else
{
goto v___jp_1406_;
}
v___jp_1406_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1407_ = lean_unsigned_to_nat(1u);
v___x_1408_ = lean_nat_add(v_currRecDepth_1396_, v___x_1407_);
lean_inc(v_currMacroScope_1403_);
lean_inc(v_maxHeartbeats_1402_);
lean_inc(v_initHeartbeats_1401_);
lean_inc(v_openDecls_1400_);
lean_inc(v_currNamespace_1399_);
lean_inc(v_ref_1398_);
lean_inc(v_maxRecDepth_1397_);
lean_inc_ref(v_options_1395_);
lean_inc_ref(v_toCold_1394_);
v___x_1409_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1409_, 0, v_toCold_1394_);
lean_ctor_set(v___x_1409_, 1, v_options_1395_);
lean_ctor_set(v___x_1409_, 2, v___x_1408_);
lean_ctor_set(v___x_1409_, 3, v_maxRecDepth_1397_);
lean_ctor_set(v___x_1409_, 4, v_ref_1398_);
lean_ctor_set(v___x_1409_, 5, v_currNamespace_1399_);
lean_ctor_set(v___x_1409_, 6, v_openDecls_1400_);
lean_ctor_set(v___x_1409_, 7, v_initHeartbeats_1401_);
lean_ctor_set(v___x_1409_, 8, v_maxHeartbeats_1402_);
lean_ctor_set(v___x_1409_, 9, v_currMacroScope_1403_);
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*10, v_diag_1404_);
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*10 + 1, v_suppressElabErrors_1405_);
lean_inc(v_a_1392_);
lean_inc(v_a_1390_);
lean_inc_ref(v_a_1389_);
lean_inc_ref(v_a_1388_);
lean_inc(v_a_1387_);
lean_inc_ref(v_a_1386_);
v___x_1410_ = lean_apply_8(v_x_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v___x_1409_, v_a_1392_, lean_box(0));
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_x_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth(v_00_u03b1_1415_, v_x_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(lean_object* v_a_1426_, lean_object* v_fvarId_1427_, lean_object* v___x_1428_, lean_object* v_a_x3f_1429_){
_start:
{
lean_object* v___x_1431_; lean_object* v_subst_1432_; lean_object* v_used_1433_; lean_object* v_binderRenaming_1434_; lean_object* v_funDeclInfoMap_1435_; uint8_t v_simplified_1436_; lean_object* v_visited_1437_; lean_object* v_inline_1438_; lean_object* v_inlineLocal_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1450_; 
v___x_1431_ = lean_st_ref_take(v_a_1426_);
v_subst_1432_ = lean_ctor_get(v___x_1431_, 0);
v_used_1433_ = lean_ctor_get(v___x_1431_, 1);
v_binderRenaming_1434_ = lean_ctor_get(v___x_1431_, 2);
v_funDeclInfoMap_1435_ = lean_ctor_get(v___x_1431_, 3);
v_simplified_1436_ = lean_ctor_get_uint8(v___x_1431_, sizeof(void*)*7);
v_visited_1437_ = lean_ctor_get(v___x_1431_, 4);
v_inline_1438_ = lean_ctor_get(v___x_1431_, 5);
v_inlineLocal_1439_ = lean_ctor_get(v___x_1431_, 6);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1441_ = v___x_1431_;
v_isShared_1442_ = v_isSharedCheck_1450_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_inlineLocal_1439_);
lean_inc(v_inline_1438_);
lean_inc(v_visited_1437_);
lean_inc(v_funDeclInfoMap_1435_);
lean_inc(v_binderRenaming_1434_);
lean_inc(v_used_1433_);
lean_inc(v_subst_1432_);
lean_dec(v___x_1431_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1450_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(v_funDeclInfoMap_1435_, v_fvarId_1427_, v___x_1428_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 3, v___x_1443_);
v___x_1445_ = v___x_1441_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_subst_1432_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_used_1433_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v_binderRenaming_1434_);
lean_ctor_set(v_reuseFailAlloc_1449_, 3, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1449_, 4, v_visited_1437_);
lean_ctor_set(v_reuseFailAlloc_1449_, 5, v_inline_1438_);
lean_ctor_set(v_reuseFailAlloc_1449_, 6, v_inlineLocal_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1449_, sizeof(void*)*7, v_simplified_1436_);
v___x_1445_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = lean_st_ref_put(v_a_1426_, v___x_1445_);
v___x_1447_ = lean_box(0);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0___boxed(lean_object* v_a_1451_, lean_object* v_fvarId_1452_, lean_object* v___x_1453_, lean_object* v_a_x3f_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1451_, v_fvarId_1452_, v___x_1453_, v_a_x3f_1454_);
lean_dec(v_a_x3f_1454_);
lean_dec(v_a_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(lean_object* v_a_1457_, lean_object* v_x_1458_){
_start:
{
if (lean_obj_tag(v_x_1458_) == 0)
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_box(0);
return v___x_1459_;
}
else
{
lean_object* v_key_1460_; lean_object* v_value_1461_; lean_object* v_tail_1462_; uint8_t v___x_1463_; 
v_key_1460_ = lean_ctor_get(v_x_1458_, 0);
v_value_1461_ = lean_ctor_get(v_x_1458_, 1);
v_tail_1462_ = lean_ctor_get(v_x_1458_, 2);
v___x_1463_ = l_Lean_instBEqFVarId_beq(v_key_1460_, v_a_1457_);
if (v___x_1463_ == 0)
{
v_x_1458_ = v_tail_1462_;
goto _start;
}
else
{
lean_object* v___x_1465_; 
lean_inc(v_value_1461_);
v___x_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_value_1461_);
return v___x_1465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg___boxed(lean_object* v_a_1466_, lean_object* v_x_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1466_, v_x_1467_);
lean_dec(v_x_1467_);
lean_dec(v_a_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(lean_object* v_m_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_buckets_1471_; lean_object* v___x_1472_; uint64_t v___x_1473_; uint64_t v___x_1474_; uint64_t v___x_1475_; uint64_t v_fold_1476_; uint64_t v___x_1477_; uint64_t v___x_1478_; uint64_t v___x_1479_; size_t v___x_1480_; size_t v___x_1481_; size_t v___x_1482_; size_t v___x_1483_; size_t v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v_buckets_1471_ = lean_ctor_get(v_m_1469_, 1);
v___x_1472_ = lean_array_get_size(v_buckets_1471_);
v___x_1473_ = l_Lean_instHashableFVarId_hash(v_a_1470_);
v___x_1474_ = 32ULL;
v___x_1475_ = lean_uint64_shift_right(v___x_1473_, v___x_1474_);
v_fold_1476_ = lean_uint64_xor(v___x_1473_, v___x_1475_);
v___x_1477_ = 16ULL;
v___x_1478_ = lean_uint64_shift_right(v_fold_1476_, v___x_1477_);
v___x_1479_ = lean_uint64_xor(v_fold_1476_, v___x_1478_);
v___x_1480_ = lean_uint64_to_usize(v___x_1479_);
v___x_1481_ = lean_usize_of_nat(v___x_1472_);
v___x_1482_ = ((size_t)1ULL);
v___x_1483_ = lean_usize_sub(v___x_1481_, v___x_1482_);
v___x_1484_ = lean_usize_land(v___x_1480_, v___x_1483_);
v___x_1485_ = lean_array_uget_borrowed(v_buckets_1471_, v___x_1484_);
v___x_1486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1470_, v___x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg___boxed(lean_object* v_m_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_1487_, v_a_1488_);
lean_dec(v_a_1488_);
lean_dec_ref(v_m_1487_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(lean_object* v_fvarId_1490_, lean_object* v_x_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v_funDeclInfoMap_1501_; lean_object* v___x_1502_; lean_object* v_a_1504_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1500_ = lean_st_ref_get(v_a_1493_);
v_funDeclInfoMap_1501_ = lean_ctor_get(v___x_1500_, 3);
lean_inc_ref(v_funDeclInfoMap_1501_);
lean_dec(v___x_1500_);
v___x_1502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_1501_, v_fvarId_1490_);
lean_dec_ref(v_funDeclInfoMap_1501_);
lean_inc(v_fvarId_1490_);
v___x_1515_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_1490_, v_a_1493_);
lean_dec_ref(v___x_1515_);
lean_inc(v_a_1498_);
lean_inc_ref(v_a_1497_);
lean_inc(v_a_1496_);
lean_inc_ref(v_a_1495_);
lean_inc_ref(v_a_1494_);
lean_inc(v_a_1493_);
lean_inc_ref(v_a_1492_);
v___x_1516_ = lean_apply_8(v_x_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, lean_box(0));
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1533_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1533_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1533_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
lean_inc(v_a_1517_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 1);
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
v___x_1523_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1493_, v_fvarId_1490_, v___x_1502_, v___x_1522_);
lean_dec_ref(v___x_1522_);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v___x_1523_, 0);
lean_dec(v_unused_1531_);
v___x_1525_ = v___x_1523_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_dec(v___x_1523_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v_a_1517_);
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1517_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
else
{
lean_object* v_a_1534_; 
v_a_1534_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1516_, 1);
v_a_1504_ = v_a_1534_;
goto v___jp_1503_;
}
v___jp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
v___x_1505_ = lean_box(0);
v___x_1506_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1493_, v_fvarId_1490_, v___x_1502_, v___x_1505_);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v___x_1506_, 0);
lean_dec(v_unused_1514_);
v___x_1508_ = v___x_1506_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_dec(v___x_1506_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 1);
lean_ctor_set(v___x_1508_, 0, v_a_1504_);
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1504_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___boxed(lean_object* v_fvarId_1535_, lean_object* v_x_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1535_, v_x_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object* v_00_u03b1_1546_, lean_object* v_fvarId_1547_, lean_object* v_x_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1547_, v_x_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___boxed(lean_object* v_00_u03b1_1558_, lean_object* v_fvarId_1559_, lean_object* v_x_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline(v_00_u03b1_1558_, v_fvarId_1559_, v_x_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(lean_object* v_00_u03b2_1570_, lean_object* v_m_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_1571_, v_a_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___boxed(lean_object* v_00_u03b2_1574_, lean_object* v_m_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(v_00_u03b2_1574_, v_m_1575_, v_a_1576_);
lean_dec(v_a_1576_);
lean_dec_ref(v_m_1575_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(lean_object* v_00_u03b2_1578_, lean_object* v_a_1579_, lean_object* v_x_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1579_, v_x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1582_, lean_object* v_a_1583_, lean_object* v_x_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(v_00_u03b2_1582_, v_a_1583_, v_x_1584_);
lean_dec(v_x_1584_);
lean_dec(v_a_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object* v_fvarId_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v___x_1597_; lean_object* v_funDeclInfoMap_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_st_ref_get(v_a_1587_);
v_funDeclInfoMap_1598_ = lean_ctor_get(v___x_1597_, 3);
lean_inc_ref(v_funDeclInfoMap_1598_);
lean_dec(v___x_1597_);
v___x_1599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_1598_, v_fvarId_1586_);
lean_dec_ref(v_funDeclInfoMap_1598_);
if (lean_obj_tag(v___x_1599_) == 1)
{
lean_object* v_val_1600_; uint8_t v___x_1601_; 
v_val_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_val_1600_);
lean_dec_ref_known(v___x_1599_, 1);
v___x_1601_ = lean_unbox(v_val_1600_);
lean_dec(v_val_1600_);
switch(v___x_1601_)
{
case 0:
{
goto v___jp_1593_;
}
case 2:
{
goto v___jp_1593_;
}
default: 
{
goto v___jp_1589_;
}
}
}
else
{
lean_dec(v___x_1599_);
goto v___jp_1589_;
}
v___jp_1589_:
{
uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = 0;
v___x_1591_ = lean_box(v___x_1590_);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
v___jp_1593_:
{
uint8_t v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = 1;
v___x_1595_ = lean_box(v___x_1594_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg___boxed(lean_object* v_fvarId_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1602_, v_a_1603_);
lean_dec(v_a_1603_);
lean_dec(v_fvarId_1602_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object* v_fvarId_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1606_, v_a_1608_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object* v_fvarId_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(v_fvarId_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_fvarId_1616_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg(lean_object* v_code_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_1627_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1641_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1641_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1641_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v_smallThreshold_1634_; uint8_t v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1639_; 
v_smallThreshold_1634_ = lean_ctor_get(v_a_1630_, 0);
lean_inc(v_smallThreshold_1634_);
lean_dec(v_a_1630_);
v___x_1635_ = 0;
v___x_1636_ = l_Lean_Compiler_LCNF_Code_sizeLe(v___x_1635_, v_code_1626_, v_smallThreshold_1634_);
lean_dec(v_smallThreshold_1634_);
v___x_1637_ = lean_box(v___x_1636_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1637_);
v___x_1639_ = v___x_1632_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_a_1642_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1629_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1629_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg___boxed(lean_object* v_code_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1650_, v_a_1651_);
lean_dec_ref(v_a_1651_);
lean_dec_ref(v_code_1650_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object* v_code_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1654_, v_a_1658_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object* v_code_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Compiler_LCNF_Simp_isSmall(v_code_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec_ref(v_code_1664_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object* v_decl_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_fvarId_1678_; lean_object* v_value_1679_; lean_object* v___x_1680_; lean_object* v_a_1681_; uint8_t v___x_1682_; 
v_fvarId_1678_ = lean_ctor_get(v_decl_1674_, 0);
v_value_1679_ = lean_ctor_get(v_decl_1674_, 4);
v___x_1680_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1678_, v_a_1675_);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
v___x_1682_ = lean_unbox(v_a_1681_);
lean_dec(v_a_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; 
lean_dec_ref(v___x_1680_);
v___x_1683_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_value_1679_, v_a_1676_);
return v___x_1683_;
}
else
{
return v___x_1680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg___boxed(lean_object* v_decl_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1684_, v_a_1685_, v_a_1686_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_decl_1684_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object* v_decl_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1689_, v_a_1691_, v_a_1693_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object* v_decl_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(v_decl_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec_ref(v_a_1702_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec_ref(v_decl_1699_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(lean_object* v_a_1709_, lean_object* v_b_1710_, lean_object* v_x_1711_){
_start:
{
if (lean_obj_tag(v_x_1711_) == 0)
{
lean_dec(v_b_1710_);
lean_dec(v_a_1709_);
return v_x_1711_;
}
else
{
lean_object* v_key_1712_; lean_object* v_value_1713_; lean_object* v_tail_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1726_; 
v_key_1712_ = lean_ctor_get(v_x_1711_, 0);
v_value_1713_ = lean_ctor_get(v_x_1711_, 1);
v_tail_1714_ = lean_ctor_get(v_x_1711_, 2);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_x_1711_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1716_ = v_x_1711_;
v_isShared_1717_ = v_isSharedCheck_1726_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_tail_1714_);
lean_inc(v_value_1713_);
lean_inc(v_key_1712_);
lean_dec(v_x_1711_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1726_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
uint8_t v___x_1718_; 
v___x_1718_ = l_Lean_instBEqFVarId_beq(v_key_1712_, v_a_1709_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1719_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_1709_, v_b_1710_, v_tail_1714_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 2, v___x_1719_);
v___x_1721_ = v___x_1716_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_key_1712_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_value_1713_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
else
{
lean_object* v___x_1724_; 
lean_dec(v_value_1713_);
lean_dec(v_key_1712_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 1, v_b_1710_);
lean_ctor_set(v___x_1716_, 0, v_a_1709_);
v___x_1724_ = v___x_1716_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1709_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_b_1710_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_tail_1714_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(lean_object* v_a_1727_, lean_object* v_x_1728_){
_start:
{
if (lean_obj_tag(v_x_1728_) == 0)
{
uint8_t v___x_1729_; 
v___x_1729_ = 0;
return v___x_1729_;
}
else
{
lean_object* v_key_1730_; lean_object* v_tail_1731_; uint8_t v___x_1732_; 
v_key_1730_ = lean_ctor_get(v_x_1728_, 0);
v_tail_1731_ = lean_ctor_get(v_x_1728_, 2);
v___x_1732_ = l_Lean_instBEqFVarId_beq(v_key_1730_, v_a_1727_);
if (v___x_1732_ == 0)
{
v_x_1728_ = v_tail_1731_;
goto _start;
}
else
{
return v___x_1732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg___boxed(lean_object* v_a_1734_, lean_object* v_x_1735_){
_start:
{
uint8_t v_res_1736_; lean_object* v_r_1737_; 
v_res_1736_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1734_, v_x_1735_);
lean_dec(v_x_1735_);
lean_dec(v_a_1734_);
v_r_1737_ = lean_box(v_res_1736_);
return v_r_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_1738_, lean_object* v_x_1739_){
_start:
{
if (lean_obj_tag(v_x_1739_) == 0)
{
return v_x_1738_;
}
else
{
lean_object* v_key_1740_; lean_object* v_value_1741_; lean_object* v_tail_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1765_; 
v_key_1740_ = lean_ctor_get(v_x_1739_, 0);
v_value_1741_ = lean_ctor_get(v_x_1739_, 1);
v_tail_1742_ = lean_ctor_get(v_x_1739_, 2);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_x_1739_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1744_ = v_x_1739_;
v_isShared_1745_ = v_isSharedCheck_1765_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_tail_1742_);
lean_inc(v_value_1741_);
lean_inc(v_key_1740_);
lean_dec(v_x_1739_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1765_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; uint64_t v___x_1747_; uint64_t v___x_1748_; uint64_t v___x_1749_; uint64_t v_fold_1750_; uint64_t v___x_1751_; uint64_t v___x_1752_; uint64_t v___x_1753_; size_t v___x_1754_; size_t v___x_1755_; size_t v___x_1756_; size_t v___x_1757_; size_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1746_ = lean_array_get_size(v_x_1738_);
v___x_1747_ = l_Lean_instHashableFVarId_hash(v_key_1740_);
v___x_1748_ = 32ULL;
v___x_1749_ = lean_uint64_shift_right(v___x_1747_, v___x_1748_);
v_fold_1750_ = lean_uint64_xor(v___x_1747_, v___x_1749_);
v___x_1751_ = 16ULL;
v___x_1752_ = lean_uint64_shift_right(v_fold_1750_, v___x_1751_);
v___x_1753_ = lean_uint64_xor(v_fold_1750_, v___x_1752_);
v___x_1754_ = lean_uint64_to_usize(v___x_1753_);
v___x_1755_ = lean_usize_of_nat(v___x_1746_);
v___x_1756_ = ((size_t)1ULL);
v___x_1757_ = lean_usize_sub(v___x_1755_, v___x_1756_);
v___x_1758_ = lean_usize_land(v___x_1754_, v___x_1757_);
v___x_1759_ = lean_array_uget_borrowed(v_x_1738_, v___x_1758_);
lean_inc(v___x_1759_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 2, v___x_1759_);
v___x_1761_ = v___x_1744_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_key_1740_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_value_1741_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_array_uset(v_x_1738_, v___x_1758_, v___x_1761_);
v_x_1738_ = v___x_1762_;
v_x_1739_ = v_tail_1742_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1766_, lean_object* v_source_1767_, lean_object* v_target_1768_){
_start:
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = lean_array_get_size(v_source_1767_);
v___x_1770_ = lean_nat_dec_lt(v_i_1766_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_dec_ref(v_source_1767_);
lean_dec(v_i_1766_);
return v_target_1768_;
}
else
{
lean_object* v_es_1771_; lean_object* v___x_1772_; lean_object* v_source_1773_; lean_object* v_target_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_es_1771_ = lean_array_fget(v_source_1767_, v_i_1766_);
v___x_1772_ = lean_box(0);
v_source_1773_ = lean_array_fset(v_source_1767_, v_i_1766_, v___x_1772_);
v_target_1774_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(v_target_1768_, v_es_1771_);
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = lean_nat_add(v_i_1766_, v___x_1775_);
lean_dec(v_i_1766_);
v_i_1766_ = v___x_1776_;
v_source_1767_ = v_source_1773_;
v_target_1768_ = v_target_1774_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(lean_object* v_data_1778_){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v_nbuckets_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1779_ = lean_array_get_size(v_data_1778_);
v___x_1780_ = lean_unsigned_to_nat(2u);
v_nbuckets_1781_ = lean_nat_mul(v___x_1779_, v___x_1780_);
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = lean_box(0);
v___x_1784_ = lean_mk_array(v_nbuckets_1781_, v___x_1783_);
v___x_1785_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(v___x_1782_, v_data_1778_, v___x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(lean_object* v_m_1786_, lean_object* v_a_1787_, lean_object* v_b_1788_){
_start:
{
lean_object* v_size_1789_; lean_object* v_buckets_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1833_; 
v_size_1789_ = lean_ctor_get(v_m_1786_, 0);
v_buckets_1790_ = lean_ctor_get(v_m_1786_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_m_1786_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1792_ = v_m_1786_;
v_isShared_1793_ = v_isSharedCheck_1833_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_buckets_1790_);
lean_inc(v_size_1789_);
lean_dec(v_m_1786_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1833_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; uint64_t v___x_1795_; uint64_t v___x_1796_; uint64_t v___x_1797_; uint64_t v_fold_1798_; uint64_t v___x_1799_; uint64_t v___x_1800_; uint64_t v___x_1801_; size_t v___x_1802_; size_t v___x_1803_; size_t v___x_1804_; size_t v___x_1805_; size_t v___x_1806_; lean_object* v_bkt_1807_; uint8_t v___x_1808_; 
v___x_1794_ = lean_array_get_size(v_buckets_1790_);
v___x_1795_ = l_Lean_instHashableFVarId_hash(v_a_1787_);
v___x_1796_ = 32ULL;
v___x_1797_ = lean_uint64_shift_right(v___x_1795_, v___x_1796_);
v_fold_1798_ = lean_uint64_xor(v___x_1795_, v___x_1797_);
v___x_1799_ = 16ULL;
v___x_1800_ = lean_uint64_shift_right(v_fold_1798_, v___x_1799_);
v___x_1801_ = lean_uint64_xor(v_fold_1798_, v___x_1800_);
v___x_1802_ = lean_uint64_to_usize(v___x_1801_);
v___x_1803_ = lean_usize_of_nat(v___x_1794_);
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_sub(v___x_1803_, v___x_1804_);
v___x_1806_ = lean_usize_land(v___x_1802_, v___x_1805_);
v_bkt_1807_ = lean_array_uget_borrowed(v_buckets_1790_, v___x_1806_);
v___x_1808_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1787_, v_bkt_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v_size_x27_1810_; lean_object* v___x_1811_; lean_object* v_buckets_x27_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1809_ = lean_unsigned_to_nat(1u);
v_size_x27_1810_ = lean_nat_add(v_size_1789_, v___x_1809_);
lean_dec(v_size_1789_);
lean_inc(v_bkt_1807_);
v___x_1811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1811_, 0, v_a_1787_);
lean_ctor_set(v___x_1811_, 1, v_b_1788_);
lean_ctor_set(v___x_1811_, 2, v_bkt_1807_);
v_buckets_x27_1812_ = lean_array_uset(v_buckets_1790_, v___x_1806_, v___x_1811_);
v___x_1813_ = lean_unsigned_to_nat(4u);
v___x_1814_ = lean_nat_mul(v_size_x27_1810_, v___x_1813_);
v___x_1815_ = lean_unsigned_to_nat(3u);
v___x_1816_ = lean_nat_div(v___x_1814_, v___x_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_array_get_size(v_buckets_x27_1812_);
v___x_1818_ = lean_nat_dec_le(v___x_1816_, v___x_1817_);
lean_dec(v___x_1816_);
if (v___x_1818_ == 0)
{
lean_object* v_val_1819_; lean_object* v___x_1821_; 
v_val_1819_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(v_buckets_x27_1812_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 1, v_val_1819_);
lean_ctor_set(v___x_1792_, 0, v_size_x27_1810_);
v___x_1821_ = v___x_1792_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_size_x27_1810_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_val_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
else
{
lean_object* v___x_1824_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 1, v_buckets_x27_1812_);
lean_ctor_set(v___x_1792_, 0, v_size_x27_1810_);
v___x_1824_ = v___x_1792_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_size_x27_1810_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_buckets_x27_1812_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
else
{
lean_object* v___x_1826_; lean_object* v_buckets_x27_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
lean_inc(v_bkt_1807_);
v___x_1826_ = lean_box(0);
v_buckets_x27_1827_ = lean_array_uset(v_buckets_1790_, v___x_1806_, v___x_1826_);
v___x_1828_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_1787_, v_b_1788_, v_bkt_1807_);
v___x_1829_ = lean_array_uset(v_buckets_x27_1827_, v___x_1806_, v___x_1828_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 1, v___x_1829_);
v___x_1831_ = v___x_1792_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_size_1789_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(lean_object* v_as_1834_, size_t v_sz_1835_, size_t v_i_1836_, lean_object* v_b_1837_){
_start:
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_usize_dec_lt(v_i_1836_, v_sz_1835_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_b_1837_);
return v___x_1840_;
}
else
{
lean_object* v_snd_1841_; lean_object* v_fst_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1876_; 
v_snd_1841_ = lean_ctor_get(v_b_1837_, 1);
v_fst_1842_ = lean_ctor_get(v_b_1837_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_b_1837_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1844_ = v_b_1837_;
v_isShared_1845_ = v_isSharedCheck_1876_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_snd_1841_);
lean_inc(v_fst_1842_);
lean_dec(v_b_1837_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1876_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v_array_1846_; lean_object* v_start_1847_; lean_object* v_stop_1848_; uint8_t v___x_1849_; 
v_array_1846_ = lean_ctor_get(v_snd_1841_, 0);
v_start_1847_ = lean_ctor_get(v_snd_1841_, 1);
v_stop_1848_ = lean_ctor_get(v_snd_1841_, 2);
v___x_1849_ = lean_nat_dec_lt(v_start_1847_, v_stop_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1851_; 
if (v_isShared_1845_ == 0)
{
v___x_1851_ = v___x_1844_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_fst_1842_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_snd_1841_);
v___x_1851_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
else
{
lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1872_; 
lean_inc(v_stop_1848_);
lean_inc(v_start_1847_);
lean_inc_ref(v_array_1846_);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_snd_1841_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; lean_object* v_unused_1874_; lean_object* v_unused_1875_; 
v_unused_1873_ = lean_ctor_get(v_snd_1841_, 2);
lean_dec(v_unused_1873_);
v_unused_1874_ = lean_ctor_get(v_snd_1841_, 1);
lean_dec(v_unused_1874_);
v_unused_1875_ = lean_ctor_get(v_snd_1841_, 0);
lean_dec(v_unused_1875_);
v___x_1855_ = v_snd_1841_;
v_isShared_1856_ = v_isSharedCheck_1872_;
goto v_resetjp_1854_;
}
else
{
lean_dec(v_snd_1841_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1872_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_a_1857_; lean_object* v_fvarId_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v_a_1857_ = lean_array_uget_borrowed(v_as_1834_, v_i_1836_);
v_fvarId_1858_ = lean_ctor_get(v_a_1857_, 0);
v___x_1859_ = lean_array_fget(v_array_1846_, v_start_1847_);
v___x_1860_ = lean_unsigned_to_nat(1u);
v___x_1861_ = lean_nat_add(v_start_1847_, v___x_1860_);
lean_dec(v_start_1847_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 1, v___x_1861_);
v___x_1863_ = v___x_1855_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_array_1846_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_stop_1848_);
v___x_1863_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
lean_inc(v_fvarId_1858_);
v___x_1864_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_fst_1842_, v_fvarId_1858_, v___x_1859_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 1, v___x_1863_);
lean_ctor_set(v___x_1844_, 0, v___x_1864_);
v___x_1866_ = v___x_1844_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1863_);
v___x_1866_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
size_t v___x_1867_; size_t v___x_1868_; 
v___x_1867_ = ((size_t)1ULL);
v___x_1868_ = lean_usize_add(v_i_1836_, v___x_1867_);
v_i_1836_ = v___x_1868_;
v_b_1837_ = v___x_1866_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg___boxed(lean_object* v_as_1877_, lean_object* v_sz_1878_, lean_object* v_i_1879_, lean_object* v_b_1880_, lean_object* v___y_1881_){
_start:
{
size_t v_sz_boxed_1882_; size_t v_i_boxed_1883_; lean_object* v_res_1884_; 
v_sz_boxed_1882_ = lean_unbox_usize(v_sz_1878_);
lean_dec(v_sz_1878_);
v_i_boxed_1883_ = lean_unbox_usize(v_i_1879_);
lean_dec(v_i_1879_);
v_res_1884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_1877_, v_sz_boxed_1882_, v_i_boxed_1883_, v_b_1880_);
lean_dec_ref(v_as_1877_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object* v_params_1885_, lean_object* v_code_1886_, lean_object* v_args_1887_, uint8_t v_mustInline_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v___x_1897_; lean_object* v_subst_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; size_t v_sz_1902_; size_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1897_ = lean_unsigned_to_nat(0u);
v_subst_1898_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1);
v___x_1899_ = lean_array_get_size(v_args_1887_);
v___x_1900_ = l_Array_toSubarray___redArg(v_args_1887_, v___x_1897_, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v_subst_1898_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v_sz_1902_ = lean_array_size(v_params_1885_);
v___x_1903_ = ((size_t)0ULL);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_params_1885_, v_sz_1902_, v___x_1903_, v___x_1901_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v_fst_1906_; uint8_t v___x_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v_fst_1906_ = lean_ctor_get(v_a_1905_, 0);
lean_inc(v_fst_1906_);
lean_dec(v_a_1905_);
v___x_1907_ = 0;
v___x_1908_ = 0;
v___x_1909_ = l_Lean_Compiler_LCNF_Code_internalize(v___x_1907_, v_code_1886_, v_fst_1906_, v___x_1908_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc_n(v_a_1910_, 2);
lean_dec_ref_known(v___x_1909_, 1);
v___x_1911_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_a_1910_, v_mustInline_1888_, v_a_1890_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v___x_1911_, 0);
lean_dec(v_unused_1919_);
v___x_1913_ = v___x_1911_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_dec(v___x_1911_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v_a_1910_);
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1910_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v_a_1910_);
v_a_1920_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1911_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1911_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
return v___x_1909_;
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref(v_code_1886_);
v_a_1928_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1904_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1904_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object* v_params_1936_, lean_object* v_code_1937_, lean_object* v_args_1938_, lean_object* v_mustInline_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
uint8_t v_mustInline_boxed_1948_; lean_object* v_res_1949_; 
v_mustInline_boxed_1948_ = lean_unbox(v_mustInline_1939_);
v_res_1949_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1936_, v_code_1937_, v_args_1938_, v_mustInline_boxed_1948_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec_ref(v_params_1936_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0(lean_object* v_00_u03b2_1950_, lean_object* v_m_1951_, lean_object* v_a_1952_, lean_object* v_b_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_m_1951_, v_a_1952_, v_b_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(lean_object* v_as_1955_, size_t v_sz_1956_, size_t v_i_1957_, lean_object* v_b_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_1955_, v_sz_1956_, v_i_1957_, v_b_1958_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___boxed(lean_object* v_as_1968_, lean_object* v_sz_1969_, lean_object* v_i_1970_, lean_object* v_b_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
size_t v_sz_boxed_1980_; size_t v_i_boxed_1981_; lean_object* v_res_1982_; 
v_sz_boxed_1980_ = lean_unbox_usize(v_sz_1969_);
lean_dec(v_sz_1969_);
v_i_boxed_1981_ = lean_unbox_usize(v_i_1970_);
lean_dec(v_i_1970_);
v_res_1982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(v_as_1968_, v_sz_boxed_1980_, v_i_boxed_1981_, v_b_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec_ref(v_as_1968_);
return v_res_1982_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(lean_object* v_00_u03b2_1983_, lean_object* v_a_1984_, lean_object* v_x_1985_){
_start:
{
uint8_t v___x_1986_; 
v___x_1986_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1984_, v_x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1987_, lean_object* v_a_1988_, lean_object* v_x_1989_){
_start:
{
uint8_t v_res_1990_; lean_object* v_r_1991_; 
v_res_1990_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(v_00_u03b2_1987_, v_a_1988_, v_x_1989_);
lean_dec(v_x_1989_);
lean_dec(v_a_1988_);
v_r_1991_ = lean_box(v_res_1990_);
return v_r_1991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1(lean_object* v_00_u03b2_1992_, lean_object* v_data_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(v_data_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2(lean_object* v_00_u03b2_1995_, lean_object* v_a_1996_, lean_object* v_b_1997_, lean_object* v_x_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_1996_, v_b_1997_, v_x_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2000_, lean_object* v_i_2001_, lean_object* v_source_2002_, lean_object* v_target_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(v_i_2001_, v_source_2002_, v_target_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2006_, v_x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object* v_decl_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
uint8_t v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = 0;
v___x_2014_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2013_, v_decl_2009_, v_a_2011_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2015_; 
lean_dec_ref_known(v___x_2014_, 1);
v___x_2015_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2010_);
return v___x_2015_;
}
else
{
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg___boxed(lean_object* v_decl_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2016_, v_a_2017_, v_a_2018_);
lean_dec(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_decl_2016_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object* v_decl_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2021_, v_a_2023_, v_a_2026_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object* v_decl_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(v_decl_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
lean_dec(v_a_2036_);
lean_dec_ref(v_a_2035_);
lean_dec_ref(v_a_2034_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec_ref(v_decl_2031_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object* v_decl_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
uint8_t v___x_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = 0;
v___x_2046_ = 1;
v___x_2047_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_2045_, v_decl_2041_, v___x_2046_, v_a_2043_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2048_; 
lean_dec_ref_known(v___x_2047_, 1);
v___x_2048_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2042_);
return v___x_2048_;
}
else
{
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg___boxed(lean_object* v_decl_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2049_, v_a_2050_, v_a_2051_);
lean_dec(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec_ref(v_decl_2049_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object* v_decl_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2054_, v_a_2056_, v_a_2059_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object* v_decl_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(v_decl_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec_ref(v_a_2067_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
lean_dec_ref(v_decl_2064_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object* v_fvarId_2074_, lean_object* v_fvarId_x27_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v___x_2082_; lean_object* v_subst_2083_; lean_object* v_used_2084_; lean_object* v_binderRenaming_2085_; lean_object* v_funDeclInfoMap_2086_; uint8_t v_simplified_2087_; lean_object* v_visited_2088_; lean_object* v_inline_2089_; lean_object* v_inlineLocal_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2160_; 
v___x_2082_ = lean_st_ref_take(v_a_2076_);
v_subst_2083_ = lean_ctor_get(v___x_2082_, 0);
v_used_2084_ = lean_ctor_get(v___x_2082_, 1);
v_binderRenaming_2085_ = lean_ctor_get(v___x_2082_, 2);
v_funDeclInfoMap_2086_ = lean_ctor_get(v___x_2082_, 3);
v_simplified_2087_ = lean_ctor_get_uint8(v___x_2082_, sizeof(void*)*7);
v_visited_2088_ = lean_ctor_get(v___x_2082_, 4);
v_inline_2089_ = lean_ctor_get(v___x_2082_, 5);
v_inlineLocal_2090_ = lean_ctor_get(v___x_2082_, 6);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2092_ = v___x_2082_;
v_isShared_2093_ = v_isSharedCheck_2160_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_inlineLocal_2090_);
lean_inc(v_inline_2089_);
lean_inc(v_visited_2088_);
lean_inc(v_funDeclInfoMap_2086_);
lean_inc(v_binderRenaming_2085_);
lean_inc(v_used_2084_);
lean_inc(v_subst_2083_);
lean_dec(v___x_2082_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2160_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
lean_inc(v_fvarId_x27_2075_);
v___x_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2094_, 0, v_fvarId_x27_2075_);
lean_inc(v_fvarId_2074_);
v___x_2095_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_subst_2083_, v_fvarId_2074_, v___x_2094_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2095_);
v___x_2097_ = v___x_2092_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_used_2084_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_binderRenaming_2085_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_funDeclInfoMap_2086_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v_visited_2088_);
lean_ctor_set(v_reuseFailAlloc_2159_, 5, v_inline_2089_);
lean_ctor_set(v_reuseFailAlloc_2159_, 6, v_inlineLocal_2090_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, sizeof(void*)*7, v_simplified_2087_);
v___x_2097_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_st_ref_put(v_a_2076_, v___x_2097_);
v___x_2099_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_2074_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2150_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2150_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2150_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
uint8_t v___x_2104_; 
v___x_2104_ = l_Lean_Name_isInternal(v_a_2100_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; 
lean_del_object(v___x_2102_);
lean_inc(v_fvarId_x27_2075_);
v___x_2105_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_x27_2075_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2137_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2137_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2137_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
uint8_t v___x_2110_; 
v___x_2110_ = l_Lean_Name_isInternal(v_a_2106_);
lean_dec(v_a_2106_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_dec(v_a_2100_);
lean_dec(v_fvarId_x27_2075_);
v___x_2111_ = lean_box(0);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2111_);
v___x_2113_ = v___x_2108_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
else
{
lean_object* v___x_2115_; lean_object* v_subst_2116_; lean_object* v_used_2117_; lean_object* v_binderRenaming_2118_; lean_object* v_funDeclInfoMap_2119_; uint8_t v_simplified_2120_; lean_object* v_visited_2121_; lean_object* v_inline_2122_; lean_object* v_inlineLocal_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2136_; 
v___x_2115_ = lean_st_ref_take(v_a_2076_);
v_subst_2116_ = lean_ctor_get(v___x_2115_, 0);
v_used_2117_ = lean_ctor_get(v___x_2115_, 1);
v_binderRenaming_2118_ = lean_ctor_get(v___x_2115_, 2);
v_funDeclInfoMap_2119_ = lean_ctor_get(v___x_2115_, 3);
v_simplified_2120_ = lean_ctor_get_uint8(v___x_2115_, sizeof(void*)*7);
v_visited_2121_ = lean_ctor_get(v___x_2115_, 4);
v_inline_2122_ = lean_ctor_get(v___x_2115_, 5);
v_inlineLocal_2123_ = lean_ctor_get(v___x_2115_, 6);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2125_ = v___x_2115_;
v_isShared_2126_ = v_isSharedCheck_2136_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_inlineLocal_2123_);
lean_inc(v_inline_2122_);
lean_inc(v_visited_2121_);
lean_inc(v_funDeclInfoMap_2119_);
lean_inc(v_binderRenaming_2118_);
lean_inc(v_used_2117_);
lean_inc(v_subst_2116_);
lean_dec(v___x_2115_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2136_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_x27_2075_, v_a_2100_, v_binderRenaming_2118_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 2, v___x_2127_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_subst_2116_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_used_2117_);
lean_ctor_set(v_reuseFailAlloc_2135_, 2, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2135_, 3, v_funDeclInfoMap_2119_);
lean_ctor_set(v_reuseFailAlloc_2135_, 4, v_visited_2121_);
lean_ctor_set(v_reuseFailAlloc_2135_, 5, v_inline_2122_);
lean_ctor_set(v_reuseFailAlloc_2135_, 6, v_inlineLocal_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2135_, sizeof(void*)*7, v_simplified_2120_);
v___x_2129_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2130_ = lean_st_ref_put(v_a_2076_, v___x_2129_);
v___x_2131_ = lean_box(0);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2131_);
v___x_2133_ = v___x_2108_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec(v_a_2100_);
lean_dec(v_fvarId_x27_2075_);
v_a_2138_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2105_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2105_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_dec(v_a_2100_);
lean_dec(v_fvarId_x27_2075_);
v___x_2146_ = lean_box(0);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2146_);
v___x_2148_ = v___x_2102_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_fvarId_x27_2075_);
v_a_2151_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2099_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2099_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg___boxed(lean_object* v_fvarId_2161_, lean_object* v_fvarId_x27_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2161_, v_fvarId_x27_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object* v_fvarId_2170_, lean_object* v_fvarId_x27_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2170_, v_fvarId_x27_2171_, v_a_2173_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___boxed(lean_object* v_fvarId_2181_, lean_object* v_fvarId_x27_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst(v_fvarId_2181_, v_fvarId_x27_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
return v_res_2191_;
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
