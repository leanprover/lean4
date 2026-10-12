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
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_take(lean_object*);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0(lean_object* v_00_u03b1_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___y_2_);
return v___x_11_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v_res_12_;
v_res_12_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0(lean_box(0), v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed(lean_object* v_00_u03b1_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0(v_00_u03b1_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_23_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
lean_inc(v___y_34_);
lean_inc_ref(v___y_33_);
lean_inc(v___y_32_);
lean_inc_ref(v___y_31_);
lean_inc_ref(v___y_30_);
lean_inc(v___y_29_);
lean_inc_ref(v___y_28_);
v___x_36_ = lean_apply_8(v___y_26_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, lean_box(0));
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; lean_object* v___x_38_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_a_37_);
lean_dec_ref_known(v___x_36_, 1);
lean_inc(v___y_34_);
lean_inc_ref(v___y_33_);
lean_inc(v___y_32_);
lean_inc_ref(v___y_31_);
lean_inc_ref(v___y_30_);
lean_inc(v___y_29_);
lean_inc_ref(v___y_28_);
v___x_38_ = lean_apply_9(v___y_27_, v_a_37_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, lean_box(0));
return v___x_38_;
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
lean_dec_ref(v___y_27_);
v_a_39_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_36_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_36_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_26_ = stack[2].m_obj;
lean_object* v___y_27_ = stack[3].m_obj;
lean_object* v___y_28_ = stack[4].m_obj;
lean_object* v___y_29_ = stack[5].m_obj;
lean_object* v___y_30_ = stack[6].m_obj;
lean_object* v___y_31_ = stack[7].m_obj;
lean_object* v___y_32_ = stack[8].m_obj;
lean_object* v___y_33_ = stack[9].m_obj;
lean_object* v___y_34_ = stack[10].m_obj;
lean_object* v_res_47_;
v_res_47_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1(lean_box(0), lean_box(0), v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed(lean_object* v_00_u03b1_48_, lean_object* v_00_u03b2_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1(v_00_u03b1_48_, v_00_u03b2_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_60_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0(void){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_instMonadEIO___redArg();
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0, &l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0);
v___x_63_ = l_StateRefT_x27_instMonad___redArg(v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM(void){
_start:
{
lean_object* v___x_70_; lean_object* v_toApplicative_71_; lean_object* v_toFunctor_72_; lean_object* v_toSeq_73_; lean_object* v_toSeqLeft_74_; lean_object* v_toSeqRight_75_; lean_object* v___f_76_; lean_object* v___f_77_; lean_object* v___f_78_; lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_toApplicative_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_145_; 
v___x_70_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1, &l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1);
v_toApplicative_71_ = lean_ctor_get(v___x_70_, 0);
v_toFunctor_72_ = lean_ctor_get(v_toApplicative_71_, 0);
v_toSeq_73_ = lean_ctor_get(v_toApplicative_71_, 2);
v_toSeqLeft_74_ = lean_ctor_get(v_toApplicative_71_, 3);
v_toSeqRight_75_ = lean_ctor_get(v_toApplicative_71_, 4);
v___f_76_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2));
v___f_77_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3));
lean_inc_ref_n(v_toFunctor_72_, 2);
v___f_78_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_78_, 0, v_toFunctor_72_);
v___f_79_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_79_, 0, v_toFunctor_72_);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v___f_78_);
lean_ctor_set(v___x_80_, 1, v___f_79_);
lean_inc(v_toSeqRight_75_);
v___f_81_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_81_, 0, v_toSeqRight_75_);
lean_inc(v_toSeqLeft_74_);
v___f_82_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_82_, 0, v_toSeqLeft_74_);
lean_inc(v_toSeq_73_);
v___f_83_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_83_, 0, v_toSeq_73_);
v___x_84_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_84_, 0, v___x_80_);
lean_ctor_set(v___x_84_, 1, v___f_76_);
lean_ctor_set(v___x_84_, 2, v___f_83_);
lean_ctor_set(v___x_84_, 3, v___f_82_);
lean_ctor_set(v___x_84_, 4, v___f_81_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___f_77_);
v___x_86_ = l_StateRefT_x27_instMonad___redArg(v___x_85_);
v_toApplicative_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v___x_86_, 1);
lean_dec(v_unused_146_);
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_145_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_toApplicative_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_145_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v_toFunctor_91_; lean_object* v_toSeq_92_; lean_object* v_toSeqLeft_93_; lean_object* v_toSeqRight_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_143_; 
v_toFunctor_91_ = lean_ctor_get(v_toApplicative_87_, 0);
v_toSeq_92_ = lean_ctor_get(v_toApplicative_87_, 2);
v_toSeqLeft_93_ = lean_ctor_get(v_toApplicative_87_, 3);
v_toSeqRight_94_ = lean_ctor_get(v_toApplicative_87_, 4);
v_isSharedCheck_143_ = !lean_is_exclusive(v_toApplicative_87_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v_toApplicative_87_, 1);
lean_dec(v_unused_144_);
v___x_96_ = v_toApplicative_87_;
v_isShared_97_ = v_isSharedCheck_143_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_toSeqRight_94_);
lean_inc(v_toSeqLeft_93_);
lean_inc(v_toSeq_92_);
lean_inc(v_toFunctor_91_);
lean_dec(v_toApplicative_87_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_143_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___f_103_; lean_object* v___f_104_; lean_object* v___f_105_; lean_object* v___x_107_; 
v___f_98_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4));
v___f_99_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5));
lean_inc_ref(v_toFunctor_91_);
v___f_100_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_100_, 0, v_toFunctor_91_);
v___f_101_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_101_, 0, v_toFunctor_91_);
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v___f_100_);
lean_ctor_set(v___x_102_, 1, v___f_101_);
v___f_103_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_103_, 0, v_toSeqRight_94_);
v___f_104_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_104_, 0, v_toSeqLeft_93_);
v___f_105_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_105_, 0, v_toSeq_92_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 4, v___f_103_);
lean_ctor_set(v___x_96_, 3, v___f_104_);
lean_ctor_set(v___x_96_, 2, v___f_105_);
lean_ctor_set(v___x_96_, 1, v___f_98_);
lean_ctor_set(v___x_96_, 0, v___x_102_);
v___x_107_ = v___x_96_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___f_98_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v___f_105_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v___f_104_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v___f_103_);
v___x_107_ = v_reuseFailAlloc_142_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_109_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v___f_99_);
lean_ctor_set(v___x_89_, 0, v___x_107_);
v___x_109_ = v___x_89_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___f_99_);
v___x_109_ = v_reuseFailAlloc_141_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_toApplicative_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_139_; 
v___x_110_ = l_ReaderT_instMonad___redArg(v___x_109_);
v___x_111_ = l_StateRefT_x27_instMonad___redArg(v___x_110_);
v_toApplicative_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; 
v_unused_140_ = lean_ctor_get(v___x_111_, 1);
lean_dec(v_unused_140_);
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_139_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_toApplicative_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_139_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v_toFunctor_116_; lean_object* v_toSeq_117_; lean_object* v_toSeqLeft_118_; lean_object* v_toSeqRight_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_137_; 
v_toFunctor_116_ = lean_ctor_get(v_toApplicative_112_, 0);
v_toSeq_117_ = lean_ctor_get(v_toApplicative_112_, 2);
v_toSeqLeft_118_ = lean_ctor_get(v_toApplicative_112_, 3);
v_toSeqRight_119_ = lean_ctor_get(v_toApplicative_112_, 4);
v_isSharedCheck_137_ = !lean_is_exclusive(v_toApplicative_112_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; 
v_unused_138_ = lean_ctor_get(v_toApplicative_112_, 1);
lean_dec(v_unused_138_);
v___x_121_ = v_toApplicative_112_;
v_isShared_122_ = v_isSharedCheck_137_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_toSeqRight_119_);
lean_inc(v_toSeqLeft_118_);
lean_inc(v_toSeq_117_);
lean_inc(v_toFunctor_116_);
lean_dec(v_toApplicative_112_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_137_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___f_123_; lean_object* v___f_124_; lean_object* v___f_125_; lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v___f_128_; lean_object* v___f_129_; lean_object* v___f_130_; lean_object* v___x_132_; 
v___f_123_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6));
v___f_124_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7));
lean_inc_ref(v_toFunctor_116_);
v___f_125_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_125_, 0, v_toFunctor_116_);
v___f_126_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_126_, 0, v_toFunctor_116_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___f_125_);
lean_ctor_set(v___x_127_, 1, v___f_126_);
v___f_128_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_128_, 0, v_toSeqRight_119_);
v___f_129_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_129_, 0, v_toSeqLeft_118_);
v___f_130_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_130_, 0, v_toSeq_117_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 4, v___f_128_);
lean_ctor_set(v___x_121_, 3, v___f_129_);
lean_ctor_set(v___x_121_, 2, v___f_130_);
lean_ctor_set(v___x_121_, 1, v___f_123_);
lean_ctor_set(v___x_121_, 0, v___x_127_);
v___x_132_ = v___x_121_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v___f_123_);
lean_ctor_set(v_reuseFailAlloc_136_, 2, v___f_130_);
lean_ctor_set(v_reuseFailAlloc_136_, 3, v___f_129_);
lean_ctor_set(v_reuseFailAlloc_136_, 4, v___f_128_);
v___x_132_ = v_reuseFailAlloc_136_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_134_; 
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v___f_124_);
lean_ctor_set(v___x_114_, 0, v___x_132_);
v___x_134_ = v___x_114_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___f_124_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
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
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0(lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; lean_object* v_subst_156_; lean_object* v___x_157_; 
v___x_155_ = lean_st_ref_get(v___y_148_);
v_subst_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc_ref(v_subst_156_);
lean_dec(v___x_155_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v_subst_156_);
return v___x_157_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_147_ = stack[0].m_obj;
lean_object* v___y_148_ = stack[1].m_obj;
lean_object* v___y_149_ = stack[2].m_obj;
lean_object* v___y_150_ = stack[3].m_obj;
lean_object* v___y_151_ = stack[4].m_obj;
lean_object* v___y_152_ = stack[5].m_obj;
lean_object* v___y_153_ = stack[6].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0(v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0___boxed(lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0(v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_167_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0(lean_object* v_f_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; lean_object* v_subst_180_; lean_object* v_used_181_; lean_object* v_binderRenaming_182_; lean_object* v_funDeclInfoMap_183_; uint8_t v_simplified_184_; lean_object* v_visited_185_; lean_object* v_inline_186_; lean_object* v_inlineLocal_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_198_; 
v___x_179_ = lean_st_ref_take(v___y_172_);
v_subst_180_ = lean_ctor_get(v___x_179_, 0);
v_used_181_ = lean_ctor_get(v___x_179_, 1);
v_binderRenaming_182_ = lean_ctor_get(v___x_179_, 2);
v_funDeclInfoMap_183_ = lean_ctor_get(v___x_179_, 3);
v_simplified_184_ = lean_ctor_get_uint8(v___x_179_, sizeof(void*)*7);
v_visited_185_ = lean_ctor_get(v___x_179_, 4);
v_inline_186_ = lean_ctor_get(v___x_179_, 5);
v_inlineLocal_187_ = lean_ctor_get(v___x_179_, 6);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_198_ == 0)
{
v___x_189_ = v___x_179_;
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_inlineLocal_187_);
lean_inc(v_inline_186_);
lean_inc(v_visited_185_);
lean_inc(v_funDeclInfoMap_183_);
lean_inc(v_binderRenaming_182_);
lean_inc(v_used_181_);
lean_inc(v_subst_180_);
lean_dec(v___x_179_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_191_ = lean_box(0);
v___x_192_ = lean_apply_1(v_f_170_, v_subst_180_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_192_);
v___x_194_ = v___x_189_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_used_181_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_binderRenaming_182_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v_funDeclInfoMap_183_);
lean_ctor_set(v_reuseFailAlloc_197_, 4, v_visited_185_);
lean_ctor_set(v_reuseFailAlloc_197_, 5, v_inline_186_);
lean_ctor_set(v_reuseFailAlloc_197_, 6, v_inlineLocal_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_197_, sizeof(void*)*7, v_simplified_184_);
v___x_194_ = v_reuseFailAlloc_197_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_st_ref_put(v___y_172_, v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_191_);
return v___x_196_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_170_ = stack[0].m_obj;
lean_object* v___y_171_ = stack[1].m_obj;
lean_object* v___y_172_ = stack[2].m_obj;
lean_object* v___y_173_ = stack[3].m_obj;
lean_object* v___y_174_ = stack[4].m_obj;
lean_object* v___y_175_ = stack[5].m_obj;
lean_object* v___y_176_ = stack[6].m_obj;
lean_object* v___y_177_ = stack[7].m_obj;
lean_object* v_res_199_;
v_res_199_ = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0(v_f_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
stack->m_obj
 = v_res_199_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0___boxed(lean_object* v_f_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0(v_f_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_209_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object* v_a_212_){
_start:
{
lean_object* v___x_214_; lean_object* v_subst_215_; lean_object* v_used_216_; lean_object* v_binderRenaming_217_; lean_object* v_funDeclInfoMap_218_; lean_object* v_visited_219_; lean_object* v_inline_220_; lean_object* v_inlineLocal_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_232_; 
v___x_214_ = lean_st_ref_take(v_a_212_);
v_subst_215_ = lean_ctor_get(v___x_214_, 0);
v_used_216_ = lean_ctor_get(v___x_214_, 1);
v_binderRenaming_217_ = lean_ctor_get(v___x_214_, 2);
v_funDeclInfoMap_218_ = lean_ctor_get(v___x_214_, 3);
v_visited_219_ = lean_ctor_get(v___x_214_, 4);
v_inline_220_ = lean_ctor_get(v___x_214_, 5);
v_inlineLocal_221_ = lean_ctor_get(v___x_214_, 6);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_232_ == 0)
{
v___x_223_ = v___x_214_;
v_isShared_224_ = v_isSharedCheck_232_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_inlineLocal_221_);
lean_inc(v_inline_220_);
lean_inc(v_visited_219_);
lean_inc(v_funDeclInfoMap_218_);
lean_inc(v_binderRenaming_217_);
lean_inc(v_used_216_);
lean_inc(v_subst_215_);
lean_dec(v___x_214_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_232_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; uint8_t v___x_226_; lean_object* v___x_228_; 
v___x_225_ = lean_box(0);
v___x_226_ = 1;
if (v_isShared_224_ == 0)
{
v___x_228_ = v___x_223_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_subst_215_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_used_216_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_binderRenaming_217_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_funDeclInfoMap_218_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_visited_219_);
lean_ctor_set(v_reuseFailAlloc_231_, 5, v_inline_220_);
lean_ctor_set(v_reuseFailAlloc_231_, 6, v_inlineLocal_221_);
v___x_228_ = v_reuseFailAlloc_231_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*7, v___x_226_);
v___x_229_ = lean_st_ref_put(v_a_212_, v___x_228_);
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_225_);
return v___x_230_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_markSimplified___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_212_ = stack[0].m_obj;
lean_object* v_res_233_;
v_res_233_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_212_);
stack->m_obj
 = v_res_233_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg___boxed(lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_234_);
lean_dec(v_a_234_);
return v_res_236_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified(lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_238_);
return v___x_245_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_markSimplified_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_237_ = stack[0].m_obj;
lean_object* v_a_238_ = stack[1].m_obj;
lean_object* v_a_239_ = stack[2].m_obj;
lean_object* v_a_240_ = stack[3].m_obj;
lean_object* v_a_241_ = stack[4].m_obj;
lean_object* v_a_242_ = stack[5].m_obj;
lean_object* v_a_243_ = stack[6].m_obj;
lean_object* v_res_246_;
v_res_246_ = l_Lean_Compiler_LCNF_Simp_markSimplified(v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___boxed(lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Compiler_LCNF_Simp_markSimplified(v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
return v_res_255_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg(lean_object* v_a_256_){
_start:
{
lean_object* v___x_258_; lean_object* v_subst_259_; lean_object* v_used_260_; lean_object* v_binderRenaming_261_; lean_object* v_funDeclInfoMap_262_; uint8_t v_simplified_263_; lean_object* v_visited_264_; lean_object* v_inline_265_; lean_object* v_inlineLocal_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_278_; 
v___x_258_ = lean_st_ref_take(v_a_256_);
v_subst_259_ = lean_ctor_get(v___x_258_, 0);
v_used_260_ = lean_ctor_get(v___x_258_, 1);
v_binderRenaming_261_ = lean_ctor_get(v___x_258_, 2);
v_funDeclInfoMap_262_ = lean_ctor_get(v___x_258_, 3);
v_simplified_263_ = lean_ctor_get_uint8(v___x_258_, sizeof(void*)*7);
v_visited_264_ = lean_ctor_get(v___x_258_, 4);
v_inline_265_ = lean_ctor_get(v___x_258_, 5);
v_inlineLocal_266_ = lean_ctor_get(v___x_258_, 6);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_278_ == 0)
{
v___x_268_ = v___x_258_;
v_isShared_269_ = v_isSharedCheck_278_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_inlineLocal_266_);
lean_inc(v_inline_265_);
lean_inc(v_visited_264_);
lean_inc(v_funDeclInfoMap_262_);
lean_inc(v_binderRenaming_261_);
lean_inc(v_used_260_);
lean_inc(v_subst_259_);
lean_dec(v___x_258_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_278_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_270_ = lean_box(0);
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_add(v_visited_264_, v___x_271_);
lean_dec(v_visited_264_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 4, v___x_272_);
v___x_274_ = v___x_268_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_subst_259_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_used_260_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_binderRenaming_261_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_funDeclInfoMap_262_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_277_, 5, v_inline_265_);
lean_ctor_set(v_reuseFailAlloc_277_, 6, v_inlineLocal_266_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*7, v_simplified_263_);
v___x_274_ = v_reuseFailAlloc_277_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_st_ref_put(v_a_256_, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_270_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_incVisited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_256_ = stack[0].m_obj;
lean_object* v_res_279_;
v_res_279_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_256_);
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___redArg___boxed(lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_280_);
lean_dec(v_a_280_);
return v_res_282_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited(lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_284_);
return v___x_291_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_incVisited_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_283_ = stack[0].m_obj;
lean_object* v_a_284_ = stack[1].m_obj;
lean_object* v_a_285_ = stack[2].m_obj;
lean_object* v_a_286_ = stack[3].m_obj;
lean_object* v_a_287_ = stack[4].m_obj;
lean_object* v_a_288_ = stack[5].m_obj;
lean_object* v_a_289_ = stack[6].m_obj;
lean_object* v_res_292_;
v_res_292_ = l_Lean_Compiler_LCNF_Simp_incVisited(v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___boxed(lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Compiler_LCNF_Simp_incVisited(v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
return v_res_301_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incInline___redArg(lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; lean_object* v_subst_305_; lean_object* v_used_306_; lean_object* v_binderRenaming_307_; lean_object* v_funDeclInfoMap_308_; uint8_t v_simplified_309_; lean_object* v_visited_310_; lean_object* v_inline_311_; lean_object* v_inlineLocal_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_324_; 
v___x_304_ = lean_st_ref_take(v_a_302_);
v_subst_305_ = lean_ctor_get(v___x_304_, 0);
v_used_306_ = lean_ctor_get(v___x_304_, 1);
v_binderRenaming_307_ = lean_ctor_get(v___x_304_, 2);
v_funDeclInfoMap_308_ = lean_ctor_get(v___x_304_, 3);
v_simplified_309_ = lean_ctor_get_uint8(v___x_304_, sizeof(void*)*7);
v_visited_310_ = lean_ctor_get(v___x_304_, 4);
v_inline_311_ = lean_ctor_get(v___x_304_, 5);
v_inlineLocal_312_ = lean_ctor_get(v___x_304_, 6);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_324_ == 0)
{
v___x_314_ = v___x_304_;
v_isShared_315_ = v_isSharedCheck_324_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_inlineLocal_312_);
lean_inc(v_inline_311_);
lean_inc(v_visited_310_);
lean_inc(v_funDeclInfoMap_308_);
lean_inc(v_binderRenaming_307_);
lean_inc(v_used_306_);
lean_inc(v_subst_305_);
lean_dec(v___x_304_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_324_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_316_ = lean_box(0);
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_add(v_inline_311_, v___x_317_);
lean_dec(v_inline_311_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 5, v___x_318_);
v___x_320_ = v___x_314_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_subst_305_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_used_306_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v_binderRenaming_307_);
lean_ctor_set(v_reuseFailAlloc_323_, 3, v_funDeclInfoMap_308_);
lean_ctor_set(v_reuseFailAlloc_323_, 4, v_visited_310_);
lean_ctor_set(v_reuseFailAlloc_323_, 5, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_323_, 6, v_inlineLocal_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_323_, sizeof(void*)*7, v_simplified_309_);
v___x_320_ = v_reuseFailAlloc_323_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_st_ref_put(v_a_302_, v___x_320_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_316_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_incInline___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_302_ = stack[0].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Lean_Compiler_LCNF_Simp_incInline___redArg(v_a_302_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___redArg___boxed(lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Compiler_LCNF_Simp_incInline___redArg(v_a_326_);
lean_dec(v_a_326_);
return v_res_328_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incInline(lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Compiler_LCNF_Simp_incInline___redArg(v_a_330_);
return v___x_337_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_incInline_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_329_ = stack[0].m_obj;
lean_object* v_a_330_ = stack[1].m_obj;
lean_object* v_a_331_ = stack[2].m_obj;
lean_object* v_a_332_ = stack[3].m_obj;
lean_object* v_a_333_ = stack[4].m_obj;
lean_object* v_a_334_ = stack[5].m_obj;
lean_object* v_a_335_ = stack[6].m_obj;
lean_object* v_res_338_;
v_res_338_ = l_Lean_Compiler_LCNF_Simp_incInline(v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
stack->m_obj
 = v_res_338_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInline___boxed(lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Compiler_LCNF_Simp_incInline(v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
return v_res_347_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(lean_object* v_a_348_){
_start:
{
lean_object* v___x_350_; lean_object* v_subst_351_; lean_object* v_used_352_; lean_object* v_binderRenaming_353_; lean_object* v_funDeclInfoMap_354_; uint8_t v_simplified_355_; lean_object* v_visited_356_; lean_object* v_inline_357_; lean_object* v_inlineLocal_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_370_; 
v___x_350_ = lean_st_ref_take(v_a_348_);
v_subst_351_ = lean_ctor_get(v___x_350_, 0);
v_used_352_ = lean_ctor_get(v___x_350_, 1);
v_binderRenaming_353_ = lean_ctor_get(v___x_350_, 2);
v_funDeclInfoMap_354_ = lean_ctor_get(v___x_350_, 3);
v_simplified_355_ = lean_ctor_get_uint8(v___x_350_, sizeof(void*)*7);
v_visited_356_ = lean_ctor_get(v___x_350_, 4);
v_inline_357_ = lean_ctor_get(v___x_350_, 5);
v_inlineLocal_358_ = lean_ctor_get(v___x_350_, 6);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_370_ == 0)
{
v___x_360_ = v___x_350_;
v_isShared_361_ = v_isSharedCheck_370_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_inlineLocal_358_);
lean_inc(v_inline_357_);
lean_inc(v_visited_356_);
lean_inc(v_funDeclInfoMap_354_);
lean_inc(v_binderRenaming_353_);
lean_inc(v_used_352_);
lean_inc(v_subst_351_);
lean_dec(v___x_350_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_370_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_362_ = lean_box(0);
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = lean_nat_add(v_inlineLocal_358_, v___x_363_);
lean_dec(v_inlineLocal_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 6, v___x_364_);
v___x_366_ = v___x_360_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_subst_351_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_used_352_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_binderRenaming_353_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_funDeclInfoMap_354_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v_visited_356_);
lean_ctor_set(v_reuseFailAlloc_369_, 5, v_inline_357_);
lean_ctor_set(v_reuseFailAlloc_369_, 6, v___x_364_);
lean_ctor_set_uint8(v_reuseFailAlloc_369_, sizeof(void*)*7, v_simplified_355_);
v___x_366_ = v_reuseFailAlloc_369_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_st_ref_put(v_a_348_, v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_362_);
return v___x_368_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_348_ = stack[0].m_obj;
lean_object* v_res_371_;
v_res_371_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(v_a_348_);
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg___boxed(lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(v_a_372_);
lean_dec(v_a_372_);
return v_res_374_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal(lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(v_a_376_);
return v___x_383_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_incInlineLocal_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_375_ = stack[0].m_obj;
lean_object* v_a_376_ = stack[1].m_obj;
lean_object* v_a_377_ = stack[2].m_obj;
lean_object* v_a_378_ = stack[3].m_obj;
lean_object* v_a_379_ = stack[4].m_obj;
lean_object* v_a_380_ = stack[5].m_obj;
lean_object* v_a_381_ = stack[6].m_obj;
lean_object* v_res_384_;
v_res_384_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal(v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
stack->m_obj
 = v_res_384_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_incInlineLocal___boxed(lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal(v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
return v_res_393_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(lean_object* v_fvarId_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; lean_object* v_subst_398_; lean_object* v_used_399_; lean_object* v_binderRenaming_400_; lean_object* v_funDeclInfoMap_401_; uint8_t v_simplified_402_; lean_object* v_visited_403_; lean_object* v_inline_404_; lean_object* v_inlineLocal_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_416_; 
v___x_397_ = lean_st_ref_take(v_a_395_);
v_subst_398_ = lean_ctor_get(v___x_397_, 0);
v_used_399_ = lean_ctor_get(v___x_397_, 1);
v_binderRenaming_400_ = lean_ctor_get(v___x_397_, 2);
v_funDeclInfoMap_401_ = lean_ctor_get(v___x_397_, 3);
v_simplified_402_ = lean_ctor_get_uint8(v___x_397_, sizeof(void*)*7);
v_visited_403_ = lean_ctor_get(v___x_397_, 4);
v_inline_404_ = lean_ctor_get(v___x_397_, 5);
v_inlineLocal_405_ = lean_ctor_get(v___x_397_, 6);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_416_ == 0)
{
v___x_407_ = v___x_397_;
v_isShared_408_ = v_isSharedCheck_416_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_inlineLocal_405_);
lean_inc(v_inline_404_);
lean_inc(v_visited_403_);
lean_inc(v_funDeclInfoMap_401_);
lean_inc(v_binderRenaming_400_);
lean_inc(v_used_399_);
lean_inc(v_subst_398_);
lean_dec(v___x_397_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_416_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_409_ = lean_box(0);
v___x_410_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(v_funDeclInfoMap_401_, v_fvarId_394_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 3, v___x_410_);
v___x_412_ = v___x_407_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_subst_398_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_used_399_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_binderRenaming_400_);
lean_ctor_set(v_reuseFailAlloc_415_, 3, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_415_, 4, v_visited_403_);
lean_ctor_set(v_reuseFailAlloc_415_, 5, v_inline_404_);
lean_ctor_set(v_reuseFailAlloc_415_, 6, v_inlineLocal_405_);
lean_ctor_set_uint8(v_reuseFailAlloc_415_, sizeof(void*)*7, v_simplified_402_);
v___x_412_ = v_reuseFailAlloc_415_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_st_ref_put(v_a_395_, v___x_412_);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_409_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_addMustInline___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_394_ = stack[0].m_obj;
lean_object* v_a_395_ = stack[1].m_obj;
lean_object* v_res_417_;
v_res_417_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_394_, v_a_395_);
stack->m_obj
 = v_res_417_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline___redArg___boxed(lean_object* v_fvarId_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_418_, v_a_419_);
lean_dec(v_a_419_);
return v_res_421_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_addMustInline(lean_object* v_fvarId_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_422_, v_a_424_);
return v___x_431_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_addMustInline_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_422_ = stack[0].m_obj;
lean_object* v_a_423_ = stack[1].m_obj;
lean_object* v_a_424_ = stack[2].m_obj;
lean_object* v_a_425_ = stack[3].m_obj;
lean_object* v_a_426_ = stack[4].m_obj;
lean_object* v_a_427_ = stack[5].m_obj;
lean_object* v_a_428_ = stack[6].m_obj;
lean_object* v_a_429_ = stack[7].m_obj;
lean_object* v_res_432_;
v_res_432_ = l_Lean_Compiler_LCNF_Simp_addMustInline(v_fvarId_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
stack->m_obj
 = v_res_432_;
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
lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(lean_object* v_fvarId_443_, lean_object* v_a_444_){
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
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_458_ = lean_box(0);
v___x_459_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v_funDeclInfoMap_450_, v_fvarId_443_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 3, v___x_459_);
v___x_461_ = v___x_456_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_subst_447_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_used_448_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_binderRenaming_449_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v_visited_452_);
lean_ctor_set(v_reuseFailAlloc_464_, 5, v_inline_453_);
lean_ctor_set(v_reuseFailAlloc_464_, 6, v_inlineLocal_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*7, v_simplified_451_);
v___x_461_ = v_reuseFailAlloc_464_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_st_ref_put(v_a_444_, v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_458_);
return v___x_463_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_443_ = stack[0].m_obj;
lean_object* v_a_444_ = stack[1].m_obj;
lean_object* v_res_466_;
v_res_466_ = l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(v_fvarId_443_, v_a_444_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg___boxed(lean_object* v_fvarId_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(v_fvarId_467_, v_a_468_);
lean_dec(v_a_468_);
return v_res_470_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc(lean_object* v_fvarId_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(v_fvarId_471_, v_a_473_);
return v___x_480_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_addFunOcc_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_471_ = stack[0].m_obj;
lean_object* v_a_472_ = stack[1].m_obj;
lean_object* v_a_473_ = stack[2].m_obj;
lean_object* v_a_474_ = stack[3].m_obj;
lean_object* v_a_475_ = stack[4].m_obj;
lean_object* v_a_476_ = stack[5].m_obj;
lean_object* v_a_477_ = stack[6].m_obj;
lean_object* v_a_478_ = stack[7].m_obj;
lean_object* v_res_481_;
v_res_481_ = l_Lean_Compiler_LCNF_Simp_addFunOcc(v_fvarId_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
stack->m_obj
 = v_res_481_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunOcc___boxed(lean_object* v_fvarId_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Compiler_LCNF_Simp_addFunOcc(v_fvarId_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
return v_res_491_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(lean_object* v_fvarId_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; lean_object* v_subst_496_; lean_object* v_used_497_; lean_object* v_binderRenaming_498_; lean_object* v_funDeclInfoMap_499_; uint8_t v_simplified_500_; lean_object* v_visited_501_; lean_object* v_inline_502_; lean_object* v_inlineLocal_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_514_; 
v___x_495_ = lean_st_ref_take(v_a_493_);
v_subst_496_ = lean_ctor_get(v___x_495_, 0);
v_used_497_ = lean_ctor_get(v___x_495_, 1);
v_binderRenaming_498_ = lean_ctor_get(v___x_495_, 2);
v_funDeclInfoMap_499_ = lean_ctor_get(v___x_495_, 3);
v_simplified_500_ = lean_ctor_get_uint8(v___x_495_, sizeof(void*)*7);
v_visited_501_ = lean_ctor_get(v___x_495_, 4);
v_inline_502_ = lean_ctor_get(v___x_495_, 5);
v_inlineLocal_503_ = lean_ctor_get(v___x_495_, 6);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_514_ == 0)
{
v___x_505_ = v___x_495_;
v_isShared_506_ = v_isSharedCheck_514_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_inlineLocal_503_);
lean_inc(v_inline_502_);
lean_inc(v_visited_501_);
lean_inc(v_funDeclInfoMap_499_);
lean_inc(v_binderRenaming_498_);
lean_inc(v_used_497_);
lean_inc(v_subst_496_);
lean_dec(v___x_495_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_514_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_507_ = lean_box(0);
v___x_508_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(v_funDeclInfoMap_499_, v_fvarId_492_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 3, v___x_508_);
v___x_510_ = v___x_505_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_subst_496_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_used_497_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_binderRenaming_498_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_513_, 4, v_visited_501_);
lean_ctor_set(v_reuseFailAlloc_513_, 5, v_inline_502_);
lean_ctor_set(v_reuseFailAlloc_513_, 6, v_inlineLocal_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_513_, sizeof(void*)*7, v_simplified_500_);
v___x_510_ = v_reuseFailAlloc_513_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_st_ref_put(v_a_493_, v___x_510_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_507_);
return v___x_512_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_492_ = stack[0].m_obj;
lean_object* v_a_493_ = stack[1].m_obj;
lean_object* v_res_515_;
v_res_515_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(v_fvarId_492_, v_a_493_);
stack->m_obj
 = v_res_515_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg___boxed(lean_object* v_fvarId_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(v_fvarId_516_, v_a_517_);
lean_dec(v_a_517_);
return v_res_519_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc(lean_object* v_fvarId_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(v_fvarId_520_, v_a_522_);
return v___x_529_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_addFunHoOcc_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_520_ = stack[0].m_obj;
lean_object* v_a_521_ = stack[1].m_obj;
lean_object* v_a_522_ = stack[2].m_obj;
lean_object* v_a_523_ = stack[3].m_obj;
lean_object* v_a_524_ = stack[4].m_obj;
lean_object* v_a_525_ = stack[5].m_obj;
lean_object* v_a_526_ = stack[6].m_obj;
lean_object* v_a_527_ = stack[7].m_obj;
lean_object* v_res_530_;
v_res_530_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc(v_fvarId_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFunHoOcc___boxed(lean_object* v_fvarId_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc(v_fvarId_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
return v_res_540_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_box(0);
v___x_542_ = lean_unsigned_to_nat(16u);
v___x_543_ = lean_mk_array(v___x_542_, v___x_541_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0);
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___x_544_);
return v___x_546_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object* v_code_547_, uint8_t v_mustInline_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_555_; lean_object* v_subst_556_; lean_object* v_used_557_; lean_object* v_binderRenaming_558_; lean_object* v_funDeclInfoMap_559_; uint8_t v_simplified_560_; lean_object* v_visited_561_; lean_object* v_inline_562_; lean_object* v_inlineLocal_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_607_; 
v___x_555_ = lean_st_ref_take(v_a_549_);
v_subst_556_ = lean_ctor_get(v___x_555_, 0);
v_used_557_ = lean_ctor_get(v___x_555_, 1);
v_binderRenaming_558_ = lean_ctor_get(v___x_555_, 2);
v_funDeclInfoMap_559_ = lean_ctor_get(v___x_555_, 3);
v_simplified_560_ = lean_ctor_get_uint8(v___x_555_, sizeof(void*)*7);
v_visited_561_ = lean_ctor_get(v___x_555_, 4);
v_inline_562_ = lean_ctor_get(v___x_555_, 5);
v_inlineLocal_563_ = lean_ctor_get(v___x_555_, 6);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_607_ == 0)
{
v___x_565_ = v___x_555_;
v_isShared_566_ = v_isSharedCheck_607_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_inlineLocal_563_);
lean_inc(v_inline_562_);
lean_inc(v_visited_561_);
lean_inc(v_funDeclInfoMap_559_);
lean_inc(v_binderRenaming_558_);
lean_inc(v_used_557_);
lean_inc(v_subst_556_);
lean_dec(v___x_555_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_607_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 3, v___x_567_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_subst_556_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_used_557_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_binderRenaming_558_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_606_, 4, v_visited_561_);
lean_ctor_set(v_reuseFailAlloc_606_, 5, v_inline_562_);
lean_ctor_set(v_reuseFailAlloc_606_, 6, v_inlineLocal_563_);
lean_ctor_set_uint8(v_reuseFailAlloc_606_, sizeof(void*)*7, v_simplified_560_);
v___x_569_ = v_reuseFailAlloc_606_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_st_ref_put(v_a_549_, v___x_569_);
v___x_571_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(v_funDeclInfoMap_559_, v_code_547_, v_mustInline_548_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_597_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_597_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_597_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_597_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v_subst_577_; lean_object* v_used_578_; lean_object* v_binderRenaming_579_; uint8_t v_simplified_580_; lean_object* v_visited_581_; lean_object* v_inline_582_; lean_object* v_inlineLocal_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_595_; 
v___x_576_ = lean_st_ref_take(v_a_549_);
v_subst_577_ = lean_ctor_get(v___x_576_, 0);
v_used_578_ = lean_ctor_get(v___x_576_, 1);
v_binderRenaming_579_ = lean_ctor_get(v___x_576_, 2);
v_simplified_580_ = lean_ctor_get_uint8(v___x_576_, sizeof(void*)*7);
v_visited_581_ = lean_ctor_get(v___x_576_, 4);
v_inline_582_ = lean_ctor_get(v___x_576_, 5);
v_inlineLocal_583_ = lean_ctor_get(v___x_576_, 6);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v___x_576_, 3);
lean_dec(v_unused_596_);
v___x_585_ = v___x_576_;
v_isShared_586_ = v_isSharedCheck_595_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_inlineLocal_583_);
lean_inc(v_inline_582_);
lean_inc(v_visited_581_);
lean_inc(v_binderRenaming_579_);
lean_inc(v_used_578_);
lean_inc(v_subst_577_);
lean_dec(v___x_576_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_595_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_box(0);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 3, v_a_572_);
v___x_589_ = v___x_585_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_subst_577_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_used_578_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_binderRenaming_579_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_a_572_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v_visited_581_);
lean_ctor_set(v_reuseFailAlloc_594_, 5, v_inline_582_);
lean_ctor_set(v_reuseFailAlloc_594_, 6, v_inlineLocal_583_);
lean_ctor_set_uint8(v_reuseFailAlloc_594_, sizeof(void*)*7, v_simplified_580_);
v___x_589_ = v_reuseFailAlloc_594_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_st_ref_put(v_a_549_, v___x_589_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_587_);
v___x_592_ = v___x_574_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_a_598_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_571_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_571_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_547_ = stack[0].m_obj;
uint8_t v_mustInline_548_ = stack[1].m_num;
lean_object* v_a_549_ = stack[2].m_obj;
lean_object* v_a_550_ = stack[3].m_obj;
lean_object* v_a_551_ = stack[4].m_obj;
lean_object* v_a_552_ = stack[5].m_obj;
lean_object* v_a_553_ = stack[6].m_obj;
lean_object* v_res_608_;
v_res_608_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_547_, v_mustInline_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
stack->m_obj
 = v_res_608_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___boxed(lean_object* v_code_609_, lean_object* v_mustInline_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
uint8_t v_mustInline_boxed_617_; lean_object* v_res_618_; 
v_mustInline_boxed_617_ = lean_unbox(v_mustInline_610_);
v_res_618_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_609_, v_mustInline_boxed_617_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
return v_res_618_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object* v_code_619_, uint8_t v_mustInline_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_code_619_, v_mustInline_620_, v_a_622_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
return v___x_629_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_619_ = stack[0].m_obj;
uint8_t v_mustInline_620_ = stack[1].m_num;
lean_object* v_a_621_ = stack[2].m_obj;
lean_object* v_a_622_ = stack[3].m_obj;
lean_object* v_a_623_ = stack[4].m_obj;
lean_object* v_a_624_ = stack[5].m_obj;
lean_object* v_a_625_ = stack[6].m_obj;
lean_object* v_a_626_ = stack[7].m_obj;
lean_object* v_a_627_ = stack[8].m_obj;
lean_object* v_res_630_;
v_res_630_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(v_code_619_, v_mustInline_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
stack->m_obj
 = v_res_630_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___boxed(lean_object* v_code_631_, lean_object* v_mustInline_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
uint8_t v_mustInline_boxed_641_; lean_object* v_res_642_; 
v_mustInline_boxed_641_ = lean_unbox(v_mustInline_632_);
v_res_642_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(v_code_631_, v_mustInline_boxed_641_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
return v_res_642_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_643_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_646_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_647_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
lean_ctor_set(v___x_649_, 2, v___x_648_);
lean_ctor_set(v___x_649_, 3, v___x_648_);
lean_ctor_set(v___x_649_, 4, v___x_647_);
lean_ctor_set(v___x_649_, 5, v___x_647_);
lean_ctor_set(v___x_649_, 6, v___x_647_);
lean_ctor_set(v___x_649_, 7, v___x_647_);
lean_ctor_set(v___x_649_, 8, v___x_647_);
lean_ctor_set(v___x_649_, 9, v___x_647_);
lean_ctor_set(v___x_649_, 10, v___x_647_);
lean_ctor_set(v___x_649_, 11, v___x_646_);
return v___x_649_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_ref_656_; lean_object* v___x_657_; lean_object* v_env_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_ref_656_ = lean_ctor_get(v___y_653_, 2);
v___x_657_ = lean_st_ref_get(v___y_654_);
v_env_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc_ref(v_env_658_);
lean_dec(v___x_657_);
v___x_659_ = lean_st_ref_get(v___y_652_);
v___x_660_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_651_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_683_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_683_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_683_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_683_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_lctx_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_681_; 
v_lctx_665_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v___x_659_, 1);
lean_dec(v_unused_682_);
v___x_667_ = v___x_659_;
v_isShared_668_ = v_isSharedCheck_681_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_lctx_665_);
lean_dec(v___x_659_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_681_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_669_ = lean_unbox(v_a_661_);
lean_dec(v_a_661_);
v___x_670_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_665_, v___x_669_);
lean_dec_ref(v_lctx_665_);
v___x_671_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_653_);
v___x_672_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2);
v___x_673_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_673_, 0, v_env_658_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
lean_ctor_set(v___x_673_, 2, v___x_670_);
lean_ctor_set(v___x_673_, 3, v___x_671_);
if (v_isShared_668_ == 0)
{
lean_ctor_set_tag(v___x_667_, 3);
lean_ctor_set(v___x_667_, 1, v_msg_650_);
lean_ctor_set(v___x_667_, 0, v___x_673_);
v___x_675_ = v___x_667_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_msg_650_);
v___x_675_ = v_reuseFailAlloc_680_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
lean_inc(v_ref_656_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_ref_656_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 1);
lean_ctor_set(v___x_663_, 0, v___x_676_);
v___x_678_ = v___x_663_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec(v___x_659_);
lean_dec_ref(v_env_658_);
lean_dec_ref(v_msg_650_);
v_a_684_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_660_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_660_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_650_ = stack[0].m_obj;
lean_object* v___y_651_ = stack[1].m_obj;
lean_object* v___y_652_ = stack[2].m_obj;
lean_object* v___y_653_ = stack[3].m_obj;
lean_object* v___y_654_ = stack[4].m_obj;
lean_object* v_res_692_;
v_res_692_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v_msg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
stack->m_obj
 = v_res_692_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___boxed(lean_object* v_msg_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v_msg_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_699_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0(lean_object* v_00_u03b1_700_, lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v_msg_701_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
return v___x_710_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_701_ = stack[1].m_obj;
lean_object* v___y_702_ = stack[2].m_obj;
lean_object* v___y_703_ = stack[3].m_obj;
lean_object* v___y_704_ = stack[4].m_obj;
lean_object* v___y_705_ = stack[5].m_obj;
lean_object* v___y_706_ = stack[6].m_obj;
lean_object* v___y_707_ = stack[7].m_obj;
lean_object* v___y_708_ = stack[8].m_obj;
lean_object* v_res_711_;
v_res_711_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0(lean_box(0), v_msg_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
stack->m_obj
 = v_res_711_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___boxed(lean_object* v_00_u03b1_712_, lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0(v_00_u03b1_712_, v_msg_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_722_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_723_; double v___x_724_; 
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_float_of_nat(v___x_723_);
return v___x_724_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(lean_object* v_cls_728_, lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_ref_735_; lean_object* v___x_736_; lean_object* v_env_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_ref_735_ = lean_ctor_get(v___y_732_, 2);
v___x_736_ = lean_st_ref_get(v___y_733_);
v_env_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc_ref(v_env_737_);
lean_dec(v___x_736_);
v___x_738_ = lean_st_ref_get(v___y_731_);
v___x_739_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_730_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_799_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_799_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_799_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_799_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_lctx_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_797_; 
v_lctx_744_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v___x_738_, 1);
lean_dec(v_unused_798_);
v___x_746_ = v___x_738_;
v_isShared_747_ = v_isSharedCheck_797_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_lctx_744_);
lean_dec(v___x_738_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_797_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_748_ = lean_unbox(v_a_740_);
lean_dec(v_a_740_);
v___x_749_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_744_, v___x_748_);
lean_dec_ref(v_lctx_744_);
v___x_750_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_732_);
v___x_751_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2);
v___x_752_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_752_, 0, v_env_737_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
lean_ctor_set(v___x_752_, 2, v___x_749_);
lean_ctor_set(v___x_752_, 3, v___x_750_);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 3);
lean_ctor_set(v___x_746_, 1, v_msg_729_);
lean_ctor_set(v___x_746_, 0, v___x_752_);
v___x_754_ = v___x_746_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_msg_729_);
v___x_754_ = v_reuseFailAlloc_796_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v_traceState_756_; lean_object* v_env_757_; lean_object* v_nextMacroScope_758_; lean_object* v_ngen_759_; lean_object* v_auxDeclNGen_760_; lean_object* v_cache_761_; lean_object* v_recordedDeps_762_; lean_object* v_messages_763_; lean_object* v_infoState_764_; lean_object* v_snapshotTasks_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_795_; 
v___x_755_ = lean_st_ref_take(v___y_733_);
v_traceState_756_ = lean_ctor_get(v___x_755_, 4);
v_env_757_ = lean_ctor_get(v___x_755_, 0);
v_nextMacroScope_758_ = lean_ctor_get(v___x_755_, 1);
v_ngen_759_ = lean_ctor_get(v___x_755_, 2);
v_auxDeclNGen_760_ = lean_ctor_get(v___x_755_, 3);
v_cache_761_ = lean_ctor_get(v___x_755_, 5);
v_recordedDeps_762_ = lean_ctor_get(v___x_755_, 6);
v_messages_763_ = lean_ctor_get(v___x_755_, 7);
v_infoState_764_ = lean_ctor_get(v___x_755_, 8);
v_snapshotTasks_765_ = lean_ctor_get(v___x_755_, 9);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_795_ == 0)
{
v___x_767_ = v___x_755_;
v_isShared_768_ = v_isSharedCheck_795_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_snapshotTasks_765_);
lean_inc(v_infoState_764_);
lean_inc(v_messages_763_);
lean_inc(v_recordedDeps_762_);
lean_inc(v_cache_761_);
lean_inc(v_traceState_756_);
lean_inc(v_auxDeclNGen_760_);
lean_inc(v_ngen_759_);
lean_inc(v_nextMacroScope_758_);
lean_inc(v_env_757_);
lean_dec(v___x_755_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_795_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
uint64_t v_tid_769_; lean_object* v_traces_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_794_; 
v_tid_769_ = lean_ctor_get_uint64(v_traceState_756_, sizeof(void*)*1);
v_traces_770_ = lean_ctor_get(v_traceState_756_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_traceState_756_);
if (v_isSharedCheck_794_ == 0)
{
v___x_772_ = v_traceState_756_;
v_isShared_773_ = v_isSharedCheck_794_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_traces_770_);
lean_dec(v_traceState_756_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_794_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_775_; double v___x_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_774_ = lean_box(0);
v___x_775_ = lean_box(0);
v___x_776_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0);
v___x_777_ = 0;
v___x_778_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1));
v___x_779_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_779_, 0, v_cls_728_);
lean_ctor_set(v___x_779_, 1, v___x_775_);
lean_ctor_set(v___x_779_, 2, v___x_778_);
lean_ctor_set_float(v___x_779_, sizeof(void*)*3, v___x_776_);
lean_ctor_set_float(v___x_779_, sizeof(void*)*3 + 8, v___x_776_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*3 + 16, v___x_777_);
v___x_780_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__2));
v___x_781_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_754_);
lean_ctor_set(v___x_781_, 2, v___x_780_);
lean_inc(v_ref_735_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_ref_735_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Lean_PersistentArray_push___redArg(v_traces_770_, v___x_782_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_783_);
v___x_785_ = v___x_772_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_783_);
lean_ctor_set_uint64(v_reuseFailAlloc_793_, sizeof(void*)*1, v_tid_769_);
v___x_785_ = v_reuseFailAlloc_793_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_787_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 4, v___x_785_);
v___x_787_ = v___x_767_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_env_757_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_nextMacroScope_758_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_ngen_759_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v_auxDeclNGen_760_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_792_, 5, v_cache_761_);
lean_ctor_set(v_reuseFailAlloc_792_, 6, v_recordedDeps_762_);
lean_ctor_set(v_reuseFailAlloc_792_, 7, v_messages_763_);
lean_ctor_set(v_reuseFailAlloc_792_, 8, v_infoState_764_);
lean_ctor_set(v_reuseFailAlloc_792_, 9, v_snapshotTasks_765_);
v___x_787_ = v_reuseFailAlloc_792_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_st_ref_put(v___y_733_, v___x_787_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_774_);
v___x_790_ = v___x_742_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_774_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
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
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v___x_738_);
lean_dec_ref(v_env_737_);
lean_dec_ref(v_msg_729_);
lean_dec(v_cls_728_);
v_a_800_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_739_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_739_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_728_ = stack[0].m_obj;
lean_object* v_msg_729_ = stack[1].m_obj;
lean_object* v___y_730_ = stack[2].m_obj;
lean_object* v___y_731_ = stack[3].m_obj;
lean_object* v___y_732_ = stack[4].m_obj;
lean_object* v___y_733_ = stack[5].m_obj;
lean_object* v_res_808_;
v_res_808_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_728_, v_msg_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
stack->m_obj
 = v_res_808_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___boxed(lean_object* v_cls_809_, lean_object* v_msg_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_809_, v_msg_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
return v_res_816_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(lean_object* v_cls_817_, lean_object* v_msg_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_817_, v_msg_818_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
return v___x_827_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_817_ = stack[0].m_obj;
lean_object* v_msg_818_ = stack[1].m_obj;
lean_object* v___y_819_ = stack[2].m_obj;
lean_object* v___y_820_ = stack[3].m_obj;
lean_object* v___y_821_ = stack[4].m_obj;
lean_object* v___y_822_ = stack[5].m_obj;
lean_object* v___y_823_ = stack[6].m_obj;
lean_object* v___y_824_ = stack[7].m_obj;
lean_object* v___y_825_ = stack[8].m_obj;
lean_object* v_res_828_;
v_res_828_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(v_cls_817_, v_msg_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
stack->m_obj
 = v_res_828_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___boxed(lean_object* v_cls_829_, lean_object* v_msg_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(v_cls_829_, v_msg_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(lean_object* v_keys_840_, lean_object* v_vals_841_, lean_object* v_i_842_, lean_object* v_k_843_){
_start:
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_array_get_size(v_keys_840_);
v___x_845_ = lean_nat_dec_lt(v_i_842_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
lean_dec(v_i_842_);
v___x_846_ = lean_box(0);
return v___x_846_;
}
else
{
lean_object* v_k_x27_847_; uint8_t v___x_848_; 
v_k_x27_847_ = lean_array_fget_borrowed(v_keys_840_, v_i_842_);
v___x_848_ = lean_name_eq(v_k_843_, v_k_x27_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_add(v_i_842_, v___x_849_);
lean_dec(v_i_842_);
v_i_842_ = v___x_850_;
goto _start;
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_array_fget_borrowed(v_vals_841_, v_i_842_);
lean_dec(v_i_842_);
lean_inc(v___x_852_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_keys_854_, lean_object* v_vals_855_, lean_object* v_i_856_, lean_object* v_k_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(v_keys_854_, v_vals_855_, v_i_856_, v_k_857_);
lean_dec(v_k_857_);
lean_dec_ref(v_vals_855_);
lean_dec_ref(v_keys_854_);
return v_res_858_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(lean_object* v_x_859_, size_t v_x_860_, lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v_es_862_; lean_object* v___x_863_; size_t v___x_864_; size_t v___x_865_; lean_object* v_j_866_; lean_object* v___x_867_; 
v_es_862_ = lean_ctor_get(v_x_859_, 0);
v___x_863_ = lean_box(2);
v___x_864_ = ((size_t)31ULL);
v___x_865_ = lean_usize_land(v_x_860_, v___x_864_);
v_j_866_ = lean_usize_to_nat(v___x_865_);
v___x_867_ = lean_array_get_borrowed(v___x_863_, v_es_862_, v_j_866_);
lean_dec(v_j_866_);
switch(lean_obj_tag(v___x_867_))
{
case 0:
{
lean_object* v_key_868_; lean_object* v_val_869_; uint8_t v___x_870_; 
v_key_868_ = lean_ctor_get(v___x_867_, 0);
v_val_869_ = lean_ctor_get(v___x_867_, 1);
v___x_870_ = lean_name_eq(v_x_861_, v_key_868_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
v___x_871_ = lean_box(0);
return v___x_871_;
}
else
{
lean_object* v___x_872_; 
lean_inc(v_val_869_);
v___x_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_872_, 0, v_val_869_);
return v___x_872_;
}
}
case 1:
{
lean_object* v_node_873_; size_t v___x_874_; size_t v___x_875_; 
v_node_873_ = lean_ctor_get(v___x_867_, 0);
v___x_874_ = ((size_t)5ULL);
v___x_875_ = lean_usize_shift_right(v_x_860_, v___x_874_);
v_x_859_ = v_node_873_;
v_x_860_ = v___x_875_;
goto _start;
}
default: 
{
lean_object* v___x_877_; 
v___x_877_ = lean_box(0);
return v___x_877_;
}
}
}
else
{
lean_object* v_ks_878_; lean_object* v_vs_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_ks_878_ = lean_ctor_get(v_x_859_, 0);
v_vs_879_ = lean_ctor_get(v_x_859_, 1);
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(v_ks_878_, v_vs_879_, v___x_880_, v_x_861_);
return v___x_881_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_859_ = stack[0].m_obj;
size_t v_x_860_ = stack[1].m_num;
lean_object* v_x_861_ = stack[2].m_obj;
lean_object* v_res_882_;
v_res_882_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_859_, v_x_860_, v_x_861_);
stack->m_obj
 = v_res_882_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___boxed(lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
size_t v_x_7238__boxed_886_; lean_object* v_res_887_; 
v_x_7238__boxed_886_ = lean_unbox_usize(v_x_884_);
lean_dec(v_x_884_);
v_res_887_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_883_, v_x_7238__boxed_886_, v_x_885_);
lean_dec(v_x_885_);
lean_dec_ref(v_x_883_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
uint64_t v___y_891_; 
if (lean_obj_tag(v_x_889_) == 0)
{
uint64_t v___x_894_; 
v___x_894_ = 1723ULL;
v___y_891_ = v___x_894_;
goto v___jp_890_;
}
else
{
uint64_t v_hash_895_; 
v_hash_895_ = lean_ctor_get_uint64(v_x_889_, sizeof(void*)*2);
v___y_891_ = v_hash_895_;
goto v___jp_890_;
}
v___jp_890_:
{
size_t v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_uint64_to_usize(v___y_891_);
v___x_893_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_888_, v___x_892_, v_x_889_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___boxed(lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_x_896_, v_x_897_);
lean_dec(v_x_897_);
lean_dec_ref(v_x_896_);
return v_res_898_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__0));
v___x_901_ = l_Lean_stringToMessageData(v___x_900_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__2));
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__4));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12(void){
_start:
{
lean_object* v_cls_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_cls_918_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9));
v___x_919_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__11));
v___x_920_ = l_Lean_Name_append(v___x_919_, v_cls_918_);
return v___x_920_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t v_recursive_921_, lean_object* v_declName_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___y_932_; uint8_t v_inlineIfReduce_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v_toCold_1055_; lean_object* v_options_1056_; uint8_t v_hasTrace_1057_; 
v_toCold_1055_ = lean_ctor_get(v_a_928_, 0);
v_options_1056_ = lean_ctor_get(v_toCold_1055_, 2);
v_hasTrace_1057_ = lean_ctor_get_uint8(v_options_1056_, sizeof(void*)*1);
if (v_hasTrace_1057_ == 0)
{
v___y_1044_ = v_a_923_;
v___y_1045_ = v_a_924_;
v___y_1046_ = v_a_925_;
v___y_1047_ = v_a_926_;
v___y_1048_ = v_a_927_;
v___y_1049_ = v_a_928_;
v___y_1050_ = v_a_929_;
goto v___jp_1043_;
}
else
{
lean_object* v_inheritedTraceOptions_1058_; lean_object* v_cls_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_inheritedTraceOptions_1058_ = lean_ctor_get(v_toCold_1055_, 11);
v_cls_1059_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9));
v___x_1060_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12);
v___x_1061_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1058_, v_options_1056_, v___x_1060_);
if (v___x_1061_ == 0)
{
v___y_1044_ = v_a_923_;
v___y_1045_ = v_a_924_;
v___y_1046_ = v_a_925_;
v___y_1047_ = v_a_926_;
v___y_1048_ = v_a_927_;
v___y_1049_ = v_a_928_;
v___y_1050_ = v_a_929_;
goto v___jp_1043_;
}
else
{
uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = 0;
lean_inc(v_declName_922_);
v___x_1063_ = l_Lean_MessageData_ofConstName(v_declName_922_, v___x_1062_);
v___x_1064_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_1059_, v___x_1063_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_dec_ref_known(v___x_1064_, 1);
v___y_1044_ = v_a_923_;
v___y_1045_ = v_a_924_;
v___y_1046_ = v_a_925_;
v___y_1047_ = v_a_926_;
v___y_1048_ = v_a_927_;
v___y_1049_ = v_a_928_;
v___y_1050_ = v_a_929_;
goto v___jp_1043_;
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec(v_declName_922_);
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
v___jp_931_:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_937_);
if (lean_obj_tag(v___x_941_) == 0)
{
if (v_recursive_921_ == 0)
{
lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_declName_922_);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v___x_941_, 0);
lean_dec(v_unused_949_);
v___x_943_ = v___x_941_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_dec(v___x_941_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___y_932_);
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___y_932_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
if (v_inlineIfReduce_933_ == 0)
{
lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_declName_922_);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v___x_941_, 0);
lean_dec(v_unused_957_);
v___x_951_ = v___x_941_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_dec(v___x_941_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___y_932_);
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___y_932_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_999_; 
v_a_958_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_999_ == 0)
{
v___x_960_ = v___x_941_;
v_isShared_961_ = v_isSharedCheck_999_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_941_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_999_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v_maxRecInlineIfReduce_962_; uint8_t v___x_963_; 
v_maxRecInlineIfReduce_962_ = lean_ctor_get(v_a_958_, 2);
lean_inc(v_maxRecInlineIfReduce_962_);
lean_dec(v_a_958_);
v___x_963_ = lean_nat_dec_lt(v_maxRecInlineIfReduce_962_, v___y_932_);
lean_dec(v_maxRecInlineIfReduce_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_965_; 
lean_dec(v_declName_922_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___y_932_);
v___x_965_ = v___x_960_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___y_932_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
lean_object* v___x_967_; 
lean_del_object(v___x_960_);
lean_dec(v___y_932_);
v___x_967_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_937_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v_maxRecInlineIfReduce_969_; lean_object* v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v_maxRecInlineIfReduce_969_ = lean_ctor_get(v_a_968_, 2);
lean_inc(v_maxRecInlineIfReduce_969_);
lean_dec(v_a_968_);
v___x_970_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1);
v___x_971_ = 0;
v___x_972_ = l_Lean_MessageData_ofConstName(v_declName_922_, v___x_971_);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_970_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_Nat_reprFast(v_maxRecInlineIfReduce_969_);
v___x_977_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
v___x_978_ = l_Lean_MessageData_ofFormat(v___x_977_);
v___x_979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_975_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_981_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_declName_922_);
v_a_991_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_967_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_967_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
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
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v___y_932_);
lean_dec(v_declName_922_);
v_a_1000_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_941_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_941_);
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
v___jp_1008_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = lean_nat_add(v___y_1016_, v___x_1017_);
lean_dec(v___y_1016_);
v___x_1019_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_1012_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; uint8_t v___x_1021_; lean_object* v___x_1022_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = lean_unbox(v_a_1020_);
lean_dec(v_a_1020_);
lean_inc(v_declName_922_);
v___x_1022_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_922_, v___x_1021_, v___y_1010_, v___y_1013_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
if (lean_obj_tag(v_a_1023_) == 1)
{
lean_object* v_val_1024_; uint8_t v___x_1025_; 
v_val_1024_ = lean_ctor_get(v_a_1023_, 0);
lean_inc(v_val_1024_);
lean_dec_ref_known(v_a_1023_, 1);
v___x_1025_ = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(v_val_1024_);
lean_dec(v_val_1024_);
v___y_932_ = v___x_1018_;
v_inlineIfReduce_933_ = v___x_1025_;
v___y_934_ = v___y_1009_;
v___y_935_ = v___y_1011_;
v___y_936_ = v___y_1015_;
v___y_937_ = v___y_1012_;
v___y_938_ = v___y_1014_;
v___y_939_ = v___y_1010_;
v___y_940_ = v___y_1013_;
goto v___jp_931_;
}
else
{
uint8_t v___x_1026_; 
lean_dec(v_a_1023_);
v___x_1026_ = 0;
v___y_932_ = v___x_1018_;
v_inlineIfReduce_933_ = v___x_1026_;
v___y_934_ = v___y_1009_;
v___y_935_ = v___y_1011_;
v___y_936_ = v___y_1015_;
v___y_937_ = v___y_1012_;
v___y_938_ = v___y_1014_;
v___y_939_ = v___y_1010_;
v___y_940_ = v___y_1013_;
goto v___jp_931_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v___x_1018_);
lean_dec(v_declName_922_);
v_a_1027_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1022_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1022_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v___x_1018_);
lean_dec(v_declName_922_);
v_a_1035_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1019_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1019_);
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
lean_object* v_inlineStackOccs_1051_; lean_object* v___x_1052_; 
v_inlineStackOccs_1051_ = lean_ctor_get(v___y_1044_, 3);
v___x_1052_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_inlineStackOccs_1051_, v_declName_922_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_unsigned_to_nat(0u);
v___y_1009_ = v___y_1044_;
v___y_1010_ = v___y_1049_;
v___y_1011_ = v___y_1045_;
v___y_1012_ = v___y_1047_;
v___y_1013_ = v___y_1050_;
v___y_1014_ = v___y_1048_;
v___y_1015_ = v___y_1046_;
v___y_1016_ = v___x_1053_;
goto v___jp_1008_;
}
else
{
lean_object* v_val_1054_; 
v_val_1054_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_val_1054_);
lean_dec_ref_known(v___x_1052_, 1);
v___y_1009_ = v___y_1044_;
v___y_1010_ = v___y_1049_;
v___y_1011_ = v___y_1045_;
v___y_1012_ = v___y_1047_;
v___y_1013_ = v___y_1050_;
v___y_1014_ = v___y_1048_;
v___y_1015_ = v___y_1046_;
v___y_1016_ = v_val_1054_;
goto v___jp_1008_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_0interp(lean_interpreter_value* stack)
{
uint8_t v_recursive_921_ = stack[0].m_num;
lean_object* v_declName_922_ = stack[1].m_obj;
lean_object* v_a_923_ = stack[2].m_obj;
lean_object* v_a_924_ = stack[3].m_obj;
lean_object* v_a_925_ = stack[4].m_obj;
lean_object* v_a_926_ = stack[5].m_obj;
lean_object* v_a_927_ = stack[6].m_obj;
lean_object* v_a_928_ = stack[7].m_obj;
lean_object* v_a_929_ = stack[8].m_obj;
lean_object* v_res_1073_;
v_res_1073_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_921_, v_declName_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
stack->m_obj
 = v_res_1073_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___boxed(lean_object* v_recursive_1074_, lean_object* v_declName_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
uint8_t v_recursive_boxed_1084_; lean_object* v_res_1085_; 
v_recursive_boxed_1084_ = lean_unbox(v_recursive_1074_);
v_res_1085_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_boxed_1084_, v_declName_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1(lean_object* v_00_u03b2_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_x_1087_, v_x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___boxed(lean_object* v_00_u03b2_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1(v_00_u03b2_1090_, v_x_1091_, v_x_1092_);
lean_dec(v_x_1092_);
lean_dec_ref(v_x_1091_);
return v_res_1093_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(lean_object* v_00_u03b2_1094_, lean_object* v_x_1095_, size_t v_x_1096_, lean_object* v_x_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_1095_, v_x_1096_, v_x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1095_ = stack[1].m_obj;
size_t v_x_1096_ = stack[2].m_num;
lean_object* v_x_1097_ = stack[3].m_obj;
lean_object* v_res_1099_;
v_res_1099_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(lean_box(0), v_x_1095_, v_x_1096_, v_x_1097_);
stack->m_obj
 = v_res_1099_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
size_t v_x_7845__boxed_1104_; lean_object* v_res_1105_; 
v_x_7845__boxed_1104_ = lean_unbox_usize(v_x_1102_);
lean_dec(v_x_1102_);
v_res_1105_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(v_00_u03b2_1100_, v_x_1101_, v_x_7845__boxed_1104_, v_x_1103_);
lean_dec(v_x_1103_);
lean_dec_ref(v_x_1101_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1106_, lean_object* v_keys_1107_, lean_object* v_vals_1108_, lean_object* v_heq_1109_, lean_object* v_i_1110_, lean_object* v_k_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(v_keys_1107_, v_vals_1108_, v_i_1110_, v_k_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1113_, lean_object* v_keys_1114_, lean_object* v_vals_1115_, lean_object* v_heq_1116_, lean_object* v_i_1117_, lean_object* v_k_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3(v_00_u03b2_1113_, v_keys_1114_, v_vals_1115_, v_heq_1116_, v_i_1117_, v_k_1118_);
lean_dec(v_k_1118_);
lean_dec_ref(v_vals_1115_);
lean_dec_ref(v_keys_1114_);
return v_res_1119_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg(lean_object* v_value_1122_, uint8_t v_recursive_1123_, lean_object* v_x_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
if (lean_obj_tag(v_value_1122_) == 3)
{
lean_object* v_declName_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v_declName_1133_ = lean_ctor_get(v_value_1122_, 0);
lean_inc_n(v_declName_1133_, 2);
lean_dec_ref_known(v_value_1122_, 3);
v___x_1134_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0));
v___x_1135_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1));
v___x_1136_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1123_, v_declName_1133_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v_declName_1138_; lean_object* v_config_1139_; lean_object* v_inlineStack_1140_; lean_object* v_inlineStackOccs_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v_declName_1138_ = lean_ctor_get(v_a_1125_, 0);
v_config_1139_ = lean_ctor_get(v_a_1125_, 1);
v_inlineStack_1140_ = lean_ctor_get(v_a_1125_, 2);
v_inlineStackOccs_1141_ = lean_ctor_get(v_a_1125_, 3);
lean_inc(v_inlineStack_1140_);
lean_inc(v_declName_1133_);
v___x_1142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_declName_1133_);
lean_ctor_set(v___x_1142_, 1, v_inlineStack_1140_);
lean_inc_ref(v_inlineStackOccs_1141_);
v___x_1143_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1134_, v___x_1135_, v_inlineStackOccs_1141_, v_declName_1133_, v_a_1137_);
lean_inc_ref(v_config_1139_);
lean_inc(v_declName_1138_);
v___x_1144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1144_, 0, v_declName_1138_);
lean_ctor_set(v___x_1144_, 1, v_config_1139_);
lean_ctor_set(v___x_1144_, 2, v___x_1142_);
lean_ctor_set(v___x_1144_, 3, v___x_1143_);
lean_inc(v_a_1131_);
lean_inc_ref(v_a_1130_);
lean_inc(v_a_1129_);
lean_inc_ref(v_a_1128_);
lean_inc_ref(v_a_1127_);
lean_inc(v_a_1126_);
v___x_1145_ = lean_apply_8(v_x_1124_, v___x_1144_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, lean_box(0));
return v___x_1145_;
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_declName_1133_);
lean_dec_ref(v_x_1124_);
v_a_1146_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1136_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1136_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
else
{
lean_object* v___x_1154_; 
lean_dec(v_value_1122_);
lean_inc(v_a_1131_);
lean_inc_ref(v_a_1130_);
lean_inc(v_a_1129_);
lean_inc_ref(v_a_1128_);
lean_inc_ref(v_a_1127_);
lean_inc(v_a_1126_);
lean_inc_ref(v_a_1125_);
v___x_1154_ = lean_apply_8(v_x_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, lean_box(0));
return v___x_1154_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_withInlining___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_1122_ = stack[0].m_obj;
uint8_t v_recursive_1123_ = stack[1].m_num;
lean_object* v_x_1124_ = stack[2].m_obj;
lean_object* v_a_1125_ = stack[3].m_obj;
lean_object* v_a_1126_ = stack[4].m_obj;
lean_object* v_a_1127_ = stack[5].m_obj;
lean_object* v_a_1128_ = stack[6].m_obj;
lean_object* v_a_1129_ = stack[7].m_obj;
lean_object* v_a_1130_ = stack[8].m_obj;
lean_object* v_a_1131_ = stack[9].m_obj;
lean_object* v_res_1155_;
v_res_1155_ = l_Lean_Compiler_LCNF_Simp_withInlining___redArg(v_value_1122_, v_recursive_1123_, v_x_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
stack->m_obj
 = v_res_1155_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___redArg___boxed(lean_object* v_value_1156_, lean_object* v_recursive_1157_, lean_object* v_x_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
uint8_t v_recursive_boxed_1167_; lean_object* v_res_1168_; 
v_recursive_boxed_1167_ = lean_unbox(v_recursive_1157_);
v_res_1168_ = l_Lean_Compiler_LCNF_Simp_withInlining___redArg(v_value_1156_, v_recursive_boxed_1167_, v_x_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
return v_res_1168_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining(lean_object* v_00_u03b1_1169_, lean_object* v_value_1170_, uint8_t v_recursive_1171_, lean_object* v_x_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
if (lean_obj_tag(v_value_1170_) == 3)
{
lean_object* v_declName_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_declName_1181_ = lean_ctor_get(v_value_1170_, 0);
lean_inc_n(v_declName_1181_, 2);
lean_dec_ref_known(v_value_1170_, 3);
v___x_1182_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0));
v___x_1183_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1));
v___x_1184_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_1171_, v_declName_1181_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v_declName_1186_; lean_object* v_config_1187_; lean_object* v_inlineStack_1188_; lean_object* v_inlineStackOccs_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v_declName_1186_ = lean_ctor_get(v_a_1173_, 0);
v_config_1187_ = lean_ctor_get(v_a_1173_, 1);
v_inlineStack_1188_ = lean_ctor_get(v_a_1173_, 2);
v_inlineStackOccs_1189_ = lean_ctor_get(v_a_1173_, 3);
lean_inc(v_inlineStack_1188_);
lean_inc(v_declName_1181_);
v___x_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1190_, 0, v_declName_1181_);
lean_ctor_set(v___x_1190_, 1, v_inlineStack_1188_);
lean_inc_ref(v_inlineStackOccs_1189_);
v___x_1191_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1182_, v___x_1183_, v_inlineStackOccs_1189_, v_declName_1181_, v_a_1185_);
lean_inc_ref(v_config_1187_);
lean_inc(v_declName_1186_);
v___x_1192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1192_, 0, v_declName_1186_);
lean_ctor_set(v___x_1192_, 1, v_config_1187_);
lean_ctor_set(v___x_1192_, 2, v___x_1190_);
lean_ctor_set(v___x_1192_, 3, v___x_1191_);
lean_inc(v_a_1179_);
lean_inc_ref(v_a_1178_);
lean_inc(v_a_1177_);
lean_inc_ref(v_a_1176_);
lean_inc_ref(v_a_1175_);
lean_inc(v_a_1174_);
v___x_1193_ = lean_apply_8(v_x_1172_, v___x_1192_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, lean_box(0));
return v___x_1193_;
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v_declName_1181_);
lean_dec_ref(v_x_1172_);
v_a_1194_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1184_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1184_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v___x_1202_; 
lean_dec(v_value_1170_);
lean_inc(v_a_1179_);
lean_inc_ref(v_a_1178_);
lean_inc(v_a_1177_);
lean_inc_ref(v_a_1176_);
lean_inc_ref(v_a_1175_);
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
v___x_1202_ = lean_apply_8(v_x_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, lean_box(0));
return v___x_1202_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_withInlining_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_1170_ = stack[1].m_obj;
uint8_t v_recursive_1171_ = stack[2].m_num;
lean_object* v_x_1172_ = stack[3].m_obj;
lean_object* v_a_1173_ = stack[4].m_obj;
lean_object* v_a_1174_ = stack[5].m_obj;
lean_object* v_a_1175_ = stack[6].m_obj;
lean_object* v_a_1176_ = stack[7].m_obj;
lean_object* v_a_1177_ = stack[8].m_obj;
lean_object* v_a_1178_ = stack[9].m_obj;
lean_object* v_a_1179_ = stack[10].m_obj;
lean_object* v_res_1203_;
v_res_1203_ = l_Lean_Compiler_LCNF_Simp_withInlining(lean_box(0), v_value_1170_, v_recursive_1171_, v_x_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
stack->m_obj
 = v_res_1203_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withInlining___boxed(lean_object* v_00_u03b1_1204_, lean_object* v_value_1205_, lean_object* v_recursive_1206_, lean_object* v_x_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
uint8_t v_recursive_boxed_1216_; lean_object* v_res_1217_; 
v_recursive_boxed_1216_ = lean_unbox(v_recursive_1206_);
v_res_1217_ = l_Lean_Compiler_LCNF_Simp_withInlining(v_00_u03b1_1204_, v_value_1205_, v_recursive_boxed_1216_, v_x_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
return v_res_1217_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__0));
v___x_1220_ = l_Lean_stringToMessageData(v___x_1219_);
return v___x_1220_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__3));
v___x_1225_ = l_Lean_MessageData_ofFormat(v___x_1224_);
return v___x_1225_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(lean_object* v_as_x27_1226_, lean_object* v_b_1227_){
_start:
{
if (lean_obj_tag(v_as_x27_1226_) == 0)
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v_b_1227_);
return v___x_1229_;
}
else
{
lean_object* v_snd_1230_; lean_object* v_head_1231_; lean_object* v_tail_1232_; lean_object* v_fst_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1274_; 
v_snd_1230_ = lean_ctor_get(v_b_1227_, 1);
lean_inc(v_snd_1230_);
v_head_1231_ = lean_ctor_get(v_as_x27_1226_, 0);
v_tail_1232_ = lean_ctor_get(v_as_x27_1226_, 1);
v_fst_1233_ = lean_ctor_get(v_b_1227_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_b_1227_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v_b_1227_, 1);
lean_dec(v_unused_1275_);
v___x_1235_ = v_b_1227_;
v_isShared_1236_ = v_isSharedCheck_1274_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_fst_1233_);
lean_dec(v_b_1227_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1274_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_fst_1237_; lean_object* v_snd_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1273_; 
v_fst_1237_ = lean_ctor_get(v_snd_1230_, 0);
v_snd_1238_ = lean_ctor_get(v_snd_1230_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_snd_1230_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1240_ = v_snd_1230_;
v_isShared_1241_ = v_isSharedCheck_1273_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_snd_1238_);
lean_inc(v_fst_1237_);
lean_dec(v_snd_1230_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1273_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
uint8_t v___x_1242_; 
v___x_1242_ = lean_name_eq(v_fst_1237_, v_head_1231_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
lean_dec(v_snd_1238_);
lean_dec(v_fst_1237_);
v___x_1243_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1);
lean_inc_n(v_head_1231_, 2);
v___x_1244_ = l_Lean_MessageData_ofConstName(v_head_1231_, v___x_1242_);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v___x_1243_);
v___x_1246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_fst_1233_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_box(v___x_1242_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 1, v___x_1247_);
lean_ctor_set(v___x_1240_, 0, v_head_1231_);
v___x_1249_ = v___x_1240_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_head_1231_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1251_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___x_1249_);
lean_ctor_set(v___x_1235_, 0, v___x_1246_);
v___x_1251_ = v___x_1235_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
v_as_x27_1226_ = v_tail_1232_;
v_b_1227_ = v___x_1251_;
goto _start;
}
}
}
else
{
uint8_t v___x_1255_; 
v___x_1255_ = lean_unbox(v_snd_1238_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
lean_dec(v_snd_1238_);
v___x_1256_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_fst_1233_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_box(v___x_1242_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 1, v___x_1258_);
v___x_1260_ = v___x_1240_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_fst_1237_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1262_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___x_1260_);
lean_ctor_set(v___x_1235_, 0, v___x_1257_);
v___x_1262_ = v___x_1235_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
v_as_x27_1226_ = v_tail_1232_;
v_b_1227_ = v___x_1262_;
goto _start;
}
}
}
else
{
lean_object* v___x_1267_; 
if (v_isShared_1241_ == 0)
{
v___x_1267_ = v___x_1240_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_fst_1237_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_snd_1238_);
v___x_1267_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1269_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___x_1267_);
v___x_1269_ = v___x_1235_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_fst_1233_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
v_as_x27_1226_ = v_tail_1232_;
v_b_1227_ = v___x_1269_;
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
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1226_ = stack[0].m_obj;
lean_object* v_b_1227_ = stack[1].m_obj;
lean_object* v_res_1276_;
v_res_1276_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_1226_, v_b_1227_);
stack->m_obj
 = v_res_1276_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___boxed(lean_object* v_as_x27_1277_, lean_object* v_b_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_1277_, v_b_1278_);
lean_dec(v_as_x27_1277_);
return v_res_1280_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = l_Lean_maxRecDepthErrorMessage;
v___x_1282_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0);
v___x_1284_ = l_Lean_MessageData_ofFormat(v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__2));
v___x_1287_ = l_Lean_stringToMessageData(v___x_1286_);
return v___x_1287_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_inlineStack_1296_; 
v_inlineStack_1296_ = lean_ctor_get(v_a_1288_, 2);
if (lean_obj_tag(v_inlineStack_1296_) == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1);
v___x_1298_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_1297_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
return v___x_1298_;
}
else
{
lean_object* v_head_1299_; lean_object* v_tail_1300_; uint8_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v_a_1309_; lean_object* v_fst_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1319_; 
v_head_1299_ = lean_ctor_get(v_inlineStack_1296_, 0);
v_tail_1300_ = lean_ctor_get(v_inlineStack_1296_, 1);
v___x_1301_ = 0;
lean_inc_n(v_head_1299_, 2);
v___x_1302_ = l_Lean_MessageData_ofConstName(v_head_1299_, v___x_1301_);
v___x_1303_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1);
v___x_1304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_box(v___x_1301_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v_head_1299_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1304_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_tail_1300_, v___x_1307_);
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref(v___x_1308_);
v_fst_1310_ = lean_ctor_get(v_a_1309_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_a_1309_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v_a_1309_, 1);
lean_dec(v_unused_1320_);
v___x_1312_ = v_a_1309_;
v_isShared_1313_ = v_isSharedCheck_1319_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_fst_1310_);
lean_dec(v_a_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1319_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3, &l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3);
if (v_isShared_1313_ == 0)
{
lean_ctor_set_tag(v___x_1312_, 7);
lean_ctor_set(v___x_1312_, 1, v_fst_1310_);
lean_ctor_set(v___x_1312_, 0, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_fst_1310_);
v___x_1316_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_1316_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
return v___x_1317_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1288_ = stack[0].m_obj;
lean_object* v_a_1289_ = stack[1].m_obj;
lean_object* v_a_1290_ = stack[2].m_obj;
lean_object* v_a_1291_ = stack[3].m_obj;
lean_object* v_a_1292_ = stack[4].m_obj;
lean_object* v_a_1293_ = stack[5].m_obj;
lean_object* v_a_1294_ = stack[6].m_obj;
lean_object* v_res_1321_;
v_res_1321_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
stack->m_obj
 = v_res_1321_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___boxed(lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
return v_res_1330_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object* v_00_u03b1_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1332_ = stack[1].m_obj;
lean_object* v_a_1333_ = stack[2].m_obj;
lean_object* v_a_1334_ = stack[3].m_obj;
lean_object* v_a_1335_ = stack[4].m_obj;
lean_object* v_a_1336_ = stack[5].m_obj;
lean_object* v_a_1337_ = stack[6].m_obj;
lean_object* v_a_1338_ = stack[7].m_obj;
lean_object* v_res_1341_;
v_res_1341_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
stack->m_obj
 = v_res_1341_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___boxed(lean_object* v_00_u03b1_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(v_00_u03b1_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec_ref(v_a_1345_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
return v_res_1351_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(lean_object* v_as_1352_, lean_object* v_as_x27_1353_, lean_object* v_b_1354_, lean_object* v_a_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_1353_, v_b_1354_);
return v___x_1364_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1352_ = stack[0].m_obj;
lean_object* v_as_x27_1353_ = stack[1].m_obj;
lean_object* v_b_1354_ = stack[2].m_obj;
lean_object* v___y_1356_ = stack[4].m_obj;
lean_object* v___y_1357_ = stack[5].m_obj;
lean_object* v___y_1358_ = stack[6].m_obj;
lean_object* v___y_1359_ = stack[7].m_obj;
lean_object* v___y_1360_ = stack[8].m_obj;
lean_object* v___y_1361_ = stack[9].m_obj;
lean_object* v___y_1362_ = stack[10].m_obj;
lean_object* v_res_1365_;
v_res_1365_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(v_as_1352_, v_as_x27_1353_, v_b_1354_, lean_box(0), v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
stack->m_obj
 = v_res_1365_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___boxed(lean_object* v_as_1366_, lean_object* v_as_x27_1367_, lean_object* v_b_1368_, lean_object* v_a_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(v_as_1366_, v_as_x27_1367_, v_b_1368_, v_a_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v_as_x27_1367_);
lean_dec(v_as_1366_);
return v_res_1378_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(lean_object* v_x_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_toCold_1388_; lean_object* v_currRecDepth_1389_; lean_object* v_ref_1390_; uint16_t v_optionFlags_1391_; uint8_t v_suppressElabErrors_1392_; uint8_t v_isRecordingDeps_1393_; lean_object* v_maxRecDepth_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v_toCold_1388_ = lean_ctor_get(v_a_1385_, 0);
v_currRecDepth_1389_ = lean_ctor_get(v_a_1385_, 1);
v_ref_1390_ = lean_ctor_get(v_a_1385_, 2);
v_optionFlags_1391_ = lean_ctor_get_uint16(v_a_1385_, sizeof(void*)*3);
v_suppressElabErrors_1392_ = lean_ctor_get_uint8(v_a_1385_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1393_ = lean_ctor_get_uint8(v_a_1385_, sizeof(void*)*3 + 3);
v_maxRecDepth_1399_ = lean_ctor_get(v_toCold_1388_, 3);
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = lean_nat_dec_eq(v_maxRecDepth_1399_, v___x_1400_);
if (v___x_1401_ == 0)
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_nat_dec_eq(v_currRecDepth_1389_, v_maxRecDepth_1399_);
if (v___x_1402_ == 0)
{
goto v___jp_1394_;
}
else
{
lean_object* v___x_1403_; 
lean_dec_ref(v_x_1379_);
v___x_1403_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
return v___x_1403_;
}
}
else
{
goto v___jp_1394_;
}
v___jp_1394_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = lean_nat_add(v_currRecDepth_1389_, v___x_1395_);
lean_inc(v_ref_1390_);
lean_inc_ref(v_toCold_1388_);
v___x_1397_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1397_, 0, v_toCold_1388_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
lean_ctor_set(v___x_1397_, 2, v_ref_1390_);
lean_ctor_set_uint16(v___x_1397_, sizeof(void*)*3, v_optionFlags_1391_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*3 + 2, v_suppressElabErrors_1392_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*3 + 3, v_isRecordingDeps_1393_);
lean_inc(v_a_1386_);
lean_inc(v_a_1384_);
lean_inc_ref(v_a_1383_);
lean_inc_ref(v_a_1382_);
lean_inc(v_a_1381_);
lean_inc_ref(v_a_1380_);
v___x_1398_ = lean_apply_8(v_x_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v___x_1397_, v_a_1386_, lean_box(0));
return v___x_1398_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1379_ = stack[0].m_obj;
lean_object* v_a_1380_ = stack[1].m_obj;
lean_object* v_a_1381_ = stack[2].m_obj;
lean_object* v_a_1382_ = stack[3].m_obj;
lean_object* v_a_1383_ = stack[4].m_obj;
lean_object* v_a_1384_ = stack[5].m_obj;
lean_object* v_a_1385_ = stack[6].m_obj;
lean_object* v_a_1386_ = stack[7].m_obj;
lean_object* v_res_1404_;
v_res_1404_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(v_x_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
stack->m_obj
 = v_res_1404_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg___boxed(lean_object* v_x_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(v_x_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
return v_res_1414_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth(lean_object* v_00_u03b1_1415_, lean_object* v_x_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_toCold_1425_; lean_object* v_currRecDepth_1426_; lean_object* v_ref_1427_; uint16_t v_optionFlags_1428_; uint8_t v_suppressElabErrors_1429_; uint8_t v_isRecordingDeps_1430_; lean_object* v_maxRecDepth_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v_toCold_1425_ = lean_ctor_get(v_a_1422_, 0);
v_currRecDepth_1426_ = lean_ctor_get(v_a_1422_, 1);
v_ref_1427_ = lean_ctor_get(v_a_1422_, 2);
v_optionFlags_1428_ = lean_ctor_get_uint16(v_a_1422_, sizeof(void*)*3);
v_suppressElabErrors_1429_ = lean_ctor_get_uint8(v_a_1422_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1430_ = lean_ctor_get_uint8(v_a_1422_, sizeof(void*)*3 + 3);
v_maxRecDepth_1436_ = lean_ctor_get(v_toCold_1425_, 3);
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = lean_nat_dec_eq(v_maxRecDepth_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
uint8_t v___x_1439_; 
v___x_1439_ = lean_nat_dec_eq(v_currRecDepth_1426_, v_maxRecDepth_1436_);
if (v___x_1439_ == 0)
{
goto v___jp_1431_;
}
else
{
lean_object* v___x_1440_; 
lean_dec_ref(v_x_1416_);
v___x_1440_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
return v___x_1440_;
}
}
else
{
goto v___jp_1431_;
}
v___jp_1431_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1432_ = lean_unsigned_to_nat(1u);
v___x_1433_ = lean_nat_add(v_currRecDepth_1426_, v___x_1432_);
lean_inc(v_ref_1427_);
lean_inc_ref(v_toCold_1425_);
v___x_1434_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1434_, 0, v_toCold_1425_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
lean_ctor_set(v___x_1434_, 2, v_ref_1427_);
lean_ctor_set_uint16(v___x_1434_, sizeof(void*)*3, v_optionFlags_1428_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*3 + 2, v_suppressElabErrors_1429_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*3 + 3, v_isRecordingDeps_1430_);
lean_inc(v_a_1423_);
lean_inc(v_a_1421_);
lean_inc_ref(v_a_1420_);
lean_inc_ref(v_a_1419_);
lean_inc(v_a_1418_);
lean_inc_ref(v_a_1417_);
v___x_1435_ = lean_apply_8(v_x_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v___x_1434_, v_a_1423_, lean_box(0));
return v___x_1435_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_withIncRecDepth_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1416_ = stack[1].m_obj;
lean_object* v_a_1417_ = stack[2].m_obj;
lean_object* v_a_1418_ = stack[3].m_obj;
lean_object* v_a_1419_ = stack[4].m_obj;
lean_object* v_a_1420_ = stack[5].m_obj;
lean_object* v_a_1421_ = stack[6].m_obj;
lean_object* v_a_1422_ = stack[7].m_obj;
lean_object* v_a_1423_ = stack[8].m_obj;
lean_object* v_res_1441_;
v_res_1441_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth(lean_box(0), v_x_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
stack->m_obj
 = v_res_1441_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth___boxed(lean_object* v_00_u03b1_1442_, lean_object* v_x_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth(v_00_u03b1_1442_, v_x_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
return v_res_1452_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(lean_object* v_a_1453_, lean_object* v_fvarId_1454_, lean_object* v___x_1455_, lean_object* v_a_x3f_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v_subst_1459_; lean_object* v_used_1460_; lean_object* v_binderRenaming_1461_; lean_object* v_funDeclInfoMap_1462_; uint8_t v_simplified_1463_; lean_object* v_visited_1464_; lean_object* v_inline_1465_; lean_object* v_inlineLocal_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1477_; 
v___x_1458_ = lean_st_ref_take(v_a_1453_);
v_subst_1459_ = lean_ctor_get(v___x_1458_, 0);
v_used_1460_ = lean_ctor_get(v___x_1458_, 1);
v_binderRenaming_1461_ = lean_ctor_get(v___x_1458_, 2);
v_funDeclInfoMap_1462_ = lean_ctor_get(v___x_1458_, 3);
v_simplified_1463_ = lean_ctor_get_uint8(v___x_1458_, sizeof(void*)*7);
v_visited_1464_ = lean_ctor_get(v___x_1458_, 4);
v_inline_1465_ = lean_ctor_get(v___x_1458_, 5);
v_inlineLocal_1466_ = lean_ctor_get(v___x_1458_, 6);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1468_ = v___x_1458_;
v_isShared_1469_ = v_isSharedCheck_1477_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_inlineLocal_1466_);
lean_inc(v_inline_1465_);
lean_inc(v_visited_1464_);
lean_inc(v_funDeclInfoMap_1462_);
lean_inc(v_binderRenaming_1461_);
lean_inc(v_used_1460_);
lean_inc(v_subst_1459_);
lean_dec(v___x_1458_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1477_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1470_ = lean_box(0);
v___x_1471_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(v_funDeclInfoMap_1462_, v_fvarId_1454_, v___x_1455_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 3, v___x_1471_);
v___x_1473_ = v___x_1468_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_subst_1459_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_used_1460_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_binderRenaming_1461_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1476_, 4, v_visited_1464_);
lean_ctor_set(v_reuseFailAlloc_1476_, 5, v_inline_1465_);
lean_ctor_set(v_reuseFailAlloc_1476_, 6, v_inlineLocal_1466_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*7, v_simplified_1463_);
v___x_1473_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_st_ref_put(v_a_1453_, v___x_1473_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1470_);
return v___x_1475_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1453_ = stack[0].m_obj;
lean_object* v_fvarId_1454_ = stack[1].m_obj;
lean_object* v___x_1455_ = stack[2].m_obj;
lean_object* v_a_x3f_1456_ = stack[3].m_obj;
lean_object* v_res_1478_;
v_res_1478_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1453_, v_fvarId_1454_, v___x_1455_, v_a_x3f_1456_);
stack->m_obj
 = v_res_1478_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0___boxed(lean_object* v_a_1479_, lean_object* v_fvarId_1480_, lean_object* v___x_1481_, lean_object* v_a_x3f_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1479_, v_fvarId_1480_, v___x_1481_, v_a_x3f_1482_);
lean_dec(v_a_x3f_1482_);
lean_dec(v_a_1479_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(lean_object* v_a_1485_, lean_object* v_x_1486_){
_start:
{
if (lean_obj_tag(v_x_1486_) == 0)
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_box(0);
return v___x_1487_;
}
else
{
lean_object* v_key_1488_; lean_object* v_value_1489_; lean_object* v_tail_1490_; uint8_t v___x_1491_; 
v_key_1488_ = lean_ctor_get(v_x_1486_, 0);
v_value_1489_ = lean_ctor_get(v_x_1486_, 1);
v_tail_1490_ = lean_ctor_get(v_x_1486_, 2);
v___x_1491_ = l_Lean_instBEqFVarId_beq(v_key_1488_, v_a_1485_);
if (v___x_1491_ == 0)
{
v_x_1486_ = v_tail_1490_;
goto _start;
}
else
{
lean_object* v___x_1493_; 
lean_inc(v_value_1489_);
v___x_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_value_1489_);
return v___x_1493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg___boxed(lean_object* v_a_1494_, lean_object* v_x_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1494_, v_x_1495_);
lean_dec(v_x_1495_);
lean_dec(v_a_1494_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(lean_object* v_m_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_buckets_1499_; lean_object* v___x_1500_; uint64_t v___x_1501_; uint64_t v___x_1502_; uint64_t v___x_1503_; uint64_t v_fold_1504_; uint64_t v___x_1505_; uint64_t v___x_1506_; uint64_t v___x_1507_; size_t v___x_1508_; size_t v___x_1509_; size_t v___x_1510_; size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_buckets_1499_ = lean_ctor_get(v_m_1497_, 1);
v___x_1500_ = lean_array_get_size(v_buckets_1499_);
v___x_1501_ = l_Lean_instHashableFVarId_hash(v_a_1498_);
v___x_1502_ = 32ULL;
v___x_1503_ = lean_uint64_shift_right(v___x_1501_, v___x_1502_);
v_fold_1504_ = lean_uint64_xor(v___x_1501_, v___x_1503_);
v___x_1505_ = 16ULL;
v___x_1506_ = lean_uint64_shift_right(v_fold_1504_, v___x_1505_);
v___x_1507_ = lean_uint64_xor(v_fold_1504_, v___x_1506_);
v___x_1508_ = lean_uint64_to_usize(v___x_1507_);
v___x_1509_ = lean_usize_of_nat(v___x_1500_);
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_sub(v___x_1509_, v___x_1510_);
v___x_1512_ = lean_usize_land(v___x_1508_, v___x_1511_);
v___x_1513_ = lean_array_uget_borrowed(v_buckets_1499_, v___x_1512_);
v___x_1514_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1498_, v___x_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg___boxed(lean_object* v_m_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_1515_, v_a_1516_);
lean_dec(v_a_1516_);
lean_dec_ref(v_m_1515_);
return v_res_1517_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(lean_object* v_fvarId_1518_, lean_object* v_x_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v_funDeclInfoMap_1529_; lean_object* v___x_1530_; lean_object* v_a_1532_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1528_ = lean_st_ref_get(v_a_1521_);
v_funDeclInfoMap_1529_ = lean_ctor_get(v___x_1528_, 3);
lean_inc_ref(v_funDeclInfoMap_1529_);
lean_dec(v___x_1528_);
v___x_1530_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_1529_, v_fvarId_1518_);
lean_dec_ref(v_funDeclInfoMap_1529_);
lean_inc(v_fvarId_1518_);
v___x_1543_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_1518_, v_a_1521_);
lean_dec_ref(v___x_1543_);
lean_inc(v_a_1526_);
lean_inc_ref(v_a_1525_);
lean_inc(v_a_1524_);
lean_inc_ref(v_a_1523_);
lean_inc_ref(v_a_1522_);
lean_inc(v_a_1521_);
lean_inc_ref(v_a_1520_);
v___x_1544_ = lean_apply_8(v_x_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, lean_box(0));
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1561_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1561_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1561_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
lean_inc(v_a_1545_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 1);
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
v___x_1551_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1521_, v_fvarId_1518_, v___x_1530_, v___x_1550_);
lean_dec_ref(v___x_1550_);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v___x_1551_, 0);
lean_dec(v_unused_1559_);
v___x_1553_ = v___x_1551_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v___x_1551_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v_a_1545_);
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1545_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
else
{
lean_object* v_a_1562_; 
v_a_1562_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1544_, 1);
v_a_1532_ = v_a_1562_;
goto v___jp_1531_;
}
v___jp_1531_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
v___x_1533_ = lean_box(0);
v___x_1534_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(v_a_1521_, v_fvarId_1518_, v___x_1530_, v___x_1533_);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; 
v_unused_1542_ = lean_ctor_get(v___x_1534_, 0);
lean_dec(v_unused_1542_);
v___x_1536_ = v___x_1534_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_dec(v___x_1534_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set_tag(v___x_1536_, 1);
lean_ctor_set(v___x_1536_, 0, v_a_1532_);
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1532_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1518_ = stack[0].m_obj;
lean_object* v_x_1519_ = stack[1].m_obj;
lean_object* v_a_1520_ = stack[2].m_obj;
lean_object* v_a_1521_ = stack[3].m_obj;
lean_object* v_a_1522_ = stack[4].m_obj;
lean_object* v_a_1523_ = stack[5].m_obj;
lean_object* v_a_1524_ = stack[6].m_obj;
lean_object* v_a_1525_ = stack[7].m_obj;
lean_object* v_a_1526_ = stack[8].m_obj;
lean_object* v_res_1563_;
v_res_1563_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1518_, v_x_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
stack->m_obj
 = v_res_1563_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___boxed(lean_object* v_fvarId_1564_, lean_object* v_x_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1564_, v_x_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
return v_res_1574_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_object* v_00_u03b1_1575_, lean_object* v_fvarId_1576_, lean_object* v_x_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(v_fvarId_1576_, v_x_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_withAddMustInline_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1576_ = stack[1].m_obj;
lean_object* v_x_1577_ = stack[2].m_obj;
lean_object* v_a_1578_ = stack[3].m_obj;
lean_object* v_a_1579_ = stack[4].m_obj;
lean_object* v_a_1580_ = stack[5].m_obj;
lean_object* v_a_1581_ = stack[6].m_obj;
lean_object* v_a_1582_ = stack[7].m_obj;
lean_object* v_a_1583_ = stack[8].m_obj;
lean_object* v_a_1584_ = stack[9].m_obj;
lean_object* v_res_1587_;
v_res_1587_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline(lean_box(0), v_fvarId_1576_, v_x_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
stack->m_obj
 = v_res_1587_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withAddMustInline___boxed(lean_object* v_00_u03b1_1588_, lean_object* v_fvarId_1589_, lean_object* v_x_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline(v_00_u03b1_1588_, v_fvarId_1589_, v_x_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(lean_object* v_00_u03b2_1600_, lean_object* v_m_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_1601_, v_a_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___boxed(lean_object* v_00_u03b2_1604_, lean_object* v_m_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(v_00_u03b2_1604_, v_m_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_m_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(lean_object* v_00_u03b2_1608_, lean_object* v_a_1609_, lean_object* v_x_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_1609_, v_x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1612_, lean_object* v_a_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(v_00_u03b2_1612_, v_a_1613_, v_x_1614_);
lean_dec(v_x_1614_);
lean_dec(v_a_1613_);
return v_res_1615_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object* v_fvarId_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v___x_1627_; lean_object* v_funDeclInfoMap_1628_; lean_object* v___x_1629_; 
v___x_1627_ = lean_st_ref_get(v_a_1617_);
v_funDeclInfoMap_1628_ = lean_ctor_get(v___x_1627_, 3);
lean_inc_ref(v_funDeclInfoMap_1628_);
lean_dec(v___x_1627_);
v___x_1629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_1628_, v_fvarId_1616_);
lean_dec_ref(v_funDeclInfoMap_1628_);
if (lean_obj_tag(v___x_1629_) == 1)
{
lean_object* v_val_1630_; uint8_t v___x_1631_; 
v_val_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_val_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = lean_unbox(v_val_1630_);
lean_dec(v_val_1630_);
switch(v___x_1631_)
{
case 0:
{
goto v___jp_1623_;
}
case 2:
{
goto v___jp_1623_;
}
default: 
{
goto v___jp_1619_;
}
}
}
else
{
lean_dec(v___x_1629_);
goto v___jp_1619_;
}
v___jp_1619_:
{
uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1620_ = 0;
v___x_1621_ = lean_box(v___x_1620_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
v___jp_1623_:
{
uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = 1;
v___x_1625_ = lean_box(v___x_1624_);
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
return v___x_1626_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1616_ = stack[0].m_obj;
lean_object* v_a_1617_ = stack[1].m_obj;
lean_object* v_res_1632_;
v_res_1632_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1616_, v_a_1617_);
stack->m_obj
 = v_res_1632_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg___boxed(lean_object* v_fvarId_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1633_, v_a_1634_);
lean_dec(v_a_1634_);
lean_dec(v_fvarId_1633_);
return v_res_1636_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object* v_fvarId_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1637_, v_a_1639_);
return v___x_1646_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1637_ = stack[0].m_obj;
lean_object* v_a_1638_ = stack[1].m_obj;
lean_object* v_a_1639_ = stack[2].m_obj;
lean_object* v_a_1640_ = stack[3].m_obj;
lean_object* v_a_1641_ = stack[4].m_obj;
lean_object* v_a_1642_ = stack[5].m_obj;
lean_object* v_a_1643_ = stack[6].m_obj;
lean_object* v_a_1644_ = stack[7].m_obj;
lean_object* v_res_1647_;
v_res_1647_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(v_fvarId_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
stack->m_obj
 = v_res_1647_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(lean_object* v_fvarId_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(v_fvarId_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_fvarId_1648_);
return v_res_1657_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg(lean_object* v_code_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_1659_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1673_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1673_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1673_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_smallThreshold_1666_; uint8_t v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v_smallThreshold_1666_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_smallThreshold_1666_);
lean_dec(v_a_1662_);
v___x_1667_ = 0;
v___x_1668_ = l_Lean_Compiler_LCNF_Code_sizeLe(v___x_1667_, v_code_1658_, v_smallThreshold_1666_);
lean_dec(v_smallThreshold_1666_);
v___x_1669_ = lean_box(v___x_1668_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1669_);
v___x_1671_ = v___x_1664_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v_a_1674_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1661_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1661_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_isSmall___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_1658_ = stack[0].m_obj;
lean_object* v_a_1659_ = stack[1].m_obj;
lean_object* v_res_1682_;
v_res_1682_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1658_, v_a_1659_);
stack->m_obj
 = v_res_1682_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___redArg___boxed(lean_object* v_code_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1683_, v_a_1684_);
lean_dec_ref(v_a_1684_);
lean_dec_ref(v_code_1683_);
return v_res_1686_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_isSmall(lean_object* v_code_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1687_, v_a_1691_);
return v___x_1696_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_isSmall_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_1687_ = stack[0].m_obj;
lean_object* v_a_1688_ = stack[1].m_obj;
lean_object* v_a_1689_ = stack[2].m_obj;
lean_object* v_a_1690_ = stack[3].m_obj;
lean_object* v_a_1691_ = stack[4].m_obj;
lean_object* v_a_1692_ = stack[5].m_obj;
lean_object* v_a_1693_ = stack[6].m_obj;
lean_object* v_a_1694_ = stack[7].m_obj;
lean_object* v_res_1697_;
v_res_1697_ = l_Lean_Compiler_LCNF_Simp_isSmall(v_code_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
stack->m_obj
 = v_res_1697_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isSmall___boxed(lean_object* v_code_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Compiler_LCNF_Simp_isSmall(v_code_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec_ref(v_code_1698_);
return v_res_1707_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(lean_object* v_decl_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_fvarId_1712_; lean_object* v_value_1713_; lean_object* v___x_1714_; lean_object* v_a_1715_; uint8_t v___x_1716_; 
v_fvarId_1712_ = lean_ctor_get(v_decl_1708_, 0);
v_value_1713_ = lean_ctor_get(v_decl_1708_, 4);
v___x_1714_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_1712_, v_a_1709_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v___x_1716_ = lean_unbox(v_a_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec_ref(v___x_1714_);
v___x_1717_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_value_1713_, v_a_1710_);
return v___x_1717_;
}
else
{
return v___x_1714_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1708_ = stack[0].m_obj;
lean_object* v_a_1709_ = stack[1].m_obj;
lean_object* v_a_1710_ = stack[2].m_obj;
lean_object* v_res_1718_;
v_res_1718_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1708_, v_a_1709_, v_a_1710_);
stack->m_obj
 = v_res_1718_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg___boxed(lean_object* v_decl_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1719_, v_a_1720_, v_a_1721_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec_ref(v_decl_1719_);
return v_res_1723_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object* v_decl_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_1724_, v_a_1726_, v_a_1728_);
return v___x_1733_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_shouldInlineLocal_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1724_ = stack[0].m_obj;
lean_object* v_a_1725_ = stack[1].m_obj;
lean_object* v_a_1726_ = stack[2].m_obj;
lean_object* v_a_1727_ = stack[3].m_obj;
lean_object* v_a_1728_ = stack[4].m_obj;
lean_object* v_a_1729_ = stack[5].m_obj;
lean_object* v_a_1730_ = stack[6].m_obj;
lean_object* v_a_1731_ = stack[7].m_obj;
lean_object* v_res_1734_;
v_res_1734_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(v_decl_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
stack->m_obj
 = v_res_1734_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(lean_object* v_decl_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(v_decl_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec_ref(v_decl_1735_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(lean_object* v_a_1745_, lean_object* v_b_1746_, lean_object* v_x_1747_){
_start:
{
if (lean_obj_tag(v_x_1747_) == 0)
{
lean_dec(v_b_1746_);
lean_dec(v_a_1745_);
return v_x_1747_;
}
else
{
lean_object* v_key_1748_; lean_object* v_value_1749_; lean_object* v_tail_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1762_; 
v_key_1748_ = lean_ctor_get(v_x_1747_, 0);
v_value_1749_ = lean_ctor_get(v_x_1747_, 1);
v_tail_1750_ = lean_ctor_get(v_x_1747_, 2);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_x_1747_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1752_ = v_x_1747_;
v_isShared_1753_ = v_isSharedCheck_1762_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_tail_1750_);
lean_inc(v_value_1749_);
lean_inc(v_key_1748_);
lean_dec(v_x_1747_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1762_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
uint8_t v___x_1754_; 
v___x_1754_ = l_Lean_instBEqFVarId_beq(v_key_1748_, v_a_1745_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1755_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_1745_, v_b_1746_, v_tail_1750_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 2, v___x_1755_);
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_key_1748_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_value_1749_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
else
{
lean_object* v___x_1760_; 
lean_dec(v_value_1749_);
lean_dec(v_key_1748_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 1, v_b_1746_);
lean_ctor_set(v___x_1752_, 0, v_a_1745_);
v___x_1760_ = v___x_1752_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1745_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_b_1746_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_tail_1750_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(lean_object* v_a_1763_, lean_object* v_x_1764_){
_start:
{
if (lean_obj_tag(v_x_1764_) == 0)
{
uint8_t v___x_1765_; 
v___x_1765_ = 0;
return v___x_1765_;
}
else
{
lean_object* v_key_1766_; lean_object* v_tail_1767_; uint8_t v___x_1768_; 
v_key_1766_ = lean_ctor_get(v_x_1764_, 0);
v_tail_1767_ = lean_ctor_get(v_x_1764_, 2);
v___x_1768_ = l_Lean_instBEqFVarId_beq(v_key_1766_, v_a_1763_);
if (v___x_1768_ == 0)
{
v_x_1764_ = v_tail_1767_;
goto _start;
}
else
{
return v___x_1768_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1763_ = stack[0].m_obj;
lean_object* v_x_1764_ = stack[1].m_obj;
uint8_t v_res_1770_;
v_res_1770_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1763_, v_x_1764_);
stack->m_num = v_res_1770_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg___boxed(lean_object* v_a_1771_, lean_object* v_x_1772_){
_start:
{
uint8_t v_res_1773_; lean_object* v_r_1774_; 
v_res_1773_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1771_, v_x_1772_);
lean_dec(v_x_1772_);
lean_dec(v_a_1771_);
v_r_1774_ = lean_box(v_res_1773_);
return v_r_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_1775_, lean_object* v_x_1776_){
_start:
{
if (lean_obj_tag(v_x_1776_) == 0)
{
return v_x_1775_;
}
else
{
lean_object* v_key_1777_; lean_object* v_value_1778_; lean_object* v_tail_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1802_; 
v_key_1777_ = lean_ctor_get(v_x_1776_, 0);
v_value_1778_ = lean_ctor_get(v_x_1776_, 1);
v_tail_1779_ = lean_ctor_get(v_x_1776_, 2);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_x_1776_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1781_ = v_x_1776_;
v_isShared_1782_ = v_isSharedCheck_1802_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_tail_1779_);
lean_inc(v_value_1778_);
lean_inc(v_key_1777_);
lean_dec(v_x_1776_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1802_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; uint64_t v___x_1784_; uint64_t v___x_1785_; uint64_t v___x_1786_; uint64_t v_fold_1787_; uint64_t v___x_1788_; uint64_t v___x_1789_; uint64_t v___x_1790_; size_t v___x_1791_; size_t v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; size_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1783_ = lean_array_get_size(v_x_1775_);
v___x_1784_ = l_Lean_instHashableFVarId_hash(v_key_1777_);
v___x_1785_ = 32ULL;
v___x_1786_ = lean_uint64_shift_right(v___x_1784_, v___x_1785_);
v_fold_1787_ = lean_uint64_xor(v___x_1784_, v___x_1786_);
v___x_1788_ = 16ULL;
v___x_1789_ = lean_uint64_shift_right(v_fold_1787_, v___x_1788_);
v___x_1790_ = lean_uint64_xor(v_fold_1787_, v___x_1789_);
v___x_1791_ = lean_uint64_to_usize(v___x_1790_);
v___x_1792_ = lean_usize_of_nat(v___x_1783_);
v___x_1793_ = ((size_t)1ULL);
v___x_1794_ = lean_usize_sub(v___x_1792_, v___x_1793_);
v___x_1795_ = lean_usize_land(v___x_1791_, v___x_1794_);
v___x_1796_ = lean_array_uget_borrowed(v_x_1775_, v___x_1795_);
lean_inc(v___x_1796_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 2, v___x_1796_);
v___x_1798_ = v___x_1781_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_key_1777_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_value_1778_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_array_uset(v_x_1775_, v___x_1795_, v___x_1798_);
v_x_1775_ = v___x_1799_;
v_x_1776_ = v_tail_1779_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1803_, lean_object* v_source_1804_, lean_object* v_target_1805_){
_start:
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = lean_array_get_size(v_source_1804_);
v___x_1807_ = lean_nat_dec_lt(v_i_1803_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_dec_ref(v_source_1804_);
lean_dec(v_i_1803_);
return v_target_1805_;
}
else
{
lean_object* v_es_1808_; lean_object* v___x_1809_; lean_object* v_source_1810_; lean_object* v_target_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_es_1808_ = lean_array_fget(v_source_1804_, v_i_1803_);
v___x_1809_ = lean_box(0);
v_source_1810_ = lean_array_fset(v_source_1804_, v_i_1803_, v___x_1809_);
v_target_1811_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(v_target_1805_, v_es_1808_);
v___x_1812_ = lean_unsigned_to_nat(1u);
v___x_1813_ = lean_nat_add(v_i_1803_, v___x_1812_);
lean_dec(v_i_1803_);
v_i_1803_ = v___x_1813_;
v_source_1804_ = v_source_1810_;
v_target_1805_ = v_target_1811_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(lean_object* v_data_1815_){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v_nbuckets_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1816_ = lean_array_get_size(v_data_1815_);
v___x_1817_ = lean_unsigned_to_nat(2u);
v_nbuckets_1818_ = lean_nat_mul(v___x_1816_, v___x_1817_);
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = lean_box(0);
v___x_1821_ = lean_mk_array(v_nbuckets_1818_, v___x_1820_);
v___x_1822_ = lean_array_propagate_mark(v_data_1815_, v___x_1821_);
v___x_1823_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(v___x_1819_, v_data_1815_, v___x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(lean_object* v_m_1824_, lean_object* v_a_1825_, lean_object* v_b_1826_){
_start:
{
lean_object* v_size_1827_; lean_object* v_buckets_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1871_; 
v_size_1827_ = lean_ctor_get(v_m_1824_, 0);
v_buckets_1828_ = lean_ctor_get(v_m_1824_, 1);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_m_1824_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1830_ = v_m_1824_;
v_isShared_1831_ = v_isSharedCheck_1871_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_buckets_1828_);
lean_inc(v_size_1827_);
lean_dec(v_m_1824_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1871_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; uint64_t v___x_1833_; uint64_t v___x_1834_; uint64_t v___x_1835_; uint64_t v_fold_1836_; uint64_t v___x_1837_; uint64_t v___x_1838_; uint64_t v___x_1839_; size_t v___x_1840_; size_t v___x_1841_; size_t v___x_1842_; size_t v___x_1843_; size_t v___x_1844_; lean_object* v_bkt_1845_; uint8_t v___x_1846_; 
v___x_1832_ = lean_array_get_size(v_buckets_1828_);
v___x_1833_ = l_Lean_instHashableFVarId_hash(v_a_1825_);
v___x_1834_ = 32ULL;
v___x_1835_ = lean_uint64_shift_right(v___x_1833_, v___x_1834_);
v_fold_1836_ = lean_uint64_xor(v___x_1833_, v___x_1835_);
v___x_1837_ = 16ULL;
v___x_1838_ = lean_uint64_shift_right(v_fold_1836_, v___x_1837_);
v___x_1839_ = lean_uint64_xor(v_fold_1836_, v___x_1838_);
v___x_1840_ = lean_uint64_to_usize(v___x_1839_);
v___x_1841_ = lean_usize_of_nat(v___x_1832_);
v___x_1842_ = ((size_t)1ULL);
v___x_1843_ = lean_usize_sub(v___x_1841_, v___x_1842_);
v___x_1844_ = lean_usize_land(v___x_1840_, v___x_1843_);
v_bkt_1845_ = lean_array_uget_borrowed(v_buckets_1828_, v___x_1844_);
v___x_1846_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_1825_, v_bkt_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v_size_x27_1848_; lean_object* v___x_1849_; lean_object* v_buckets_x27_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1847_ = lean_unsigned_to_nat(1u);
v_size_x27_1848_ = lean_nat_add(v_size_1827_, v___x_1847_);
lean_dec(v_size_1827_);
lean_inc(v_bkt_1845_);
v___x_1849_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1849_, 0, v_a_1825_);
lean_ctor_set(v___x_1849_, 1, v_b_1826_);
lean_ctor_set(v___x_1849_, 2, v_bkt_1845_);
v_buckets_x27_1850_ = lean_array_uset(v_buckets_1828_, v___x_1844_, v___x_1849_);
v___x_1851_ = lean_unsigned_to_nat(4u);
v___x_1852_ = lean_nat_mul(v_size_x27_1848_, v___x_1851_);
v___x_1853_ = lean_unsigned_to_nat(3u);
v___x_1854_ = lean_nat_div(v___x_1852_, v___x_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_array_get_size(v_buckets_x27_1850_);
v___x_1856_ = lean_nat_dec_le(v___x_1854_, v___x_1855_);
lean_dec(v___x_1854_);
if (v___x_1856_ == 0)
{
lean_object* v_val_1857_; lean_object* v___x_1859_; 
v_val_1857_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(v_buckets_x27_1850_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v_val_1857_);
lean_ctor_set(v___x_1830_, 0, v_size_x27_1848_);
v___x_1859_ = v___x_1830_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_size_x27_1848_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_val_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
else
{
lean_object* v___x_1862_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v_buckets_x27_1850_);
lean_ctor_set(v___x_1830_, 0, v_size_x27_1848_);
v___x_1862_ = v___x_1830_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_size_x27_1848_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_buckets_x27_1850_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
else
{
lean_object* v___x_1864_; lean_object* v_buckets_x27_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
lean_inc(v_bkt_1845_);
v___x_1864_ = lean_box(0);
v_buckets_x27_1865_ = lean_array_uset(v_buckets_1828_, v___x_1844_, v___x_1864_);
v___x_1866_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_1825_, v_b_1826_, v_bkt_1845_);
v___x_1867_ = lean_array_uset(v_buckets_x27_1865_, v___x_1844_, v___x_1866_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v___x_1867_);
v___x_1869_ = v___x_1830_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_size_1827_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(lean_object* v_as_1872_, size_t v_sz_1873_, size_t v_i_1874_, lean_object* v_b_1875_){
_start:
{
uint8_t v___x_1877_; 
v___x_1877_ = lean_usize_dec_lt(v_i_1874_, v_sz_1873_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_b_1875_);
return v___x_1878_;
}
else
{
lean_object* v_snd_1879_; lean_object* v_fst_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1914_; 
v_snd_1879_ = lean_ctor_get(v_b_1875_, 1);
v_fst_1880_ = lean_ctor_get(v_b_1875_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_b_1875_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1882_ = v_b_1875_;
v_isShared_1883_ = v_isSharedCheck_1914_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_snd_1879_);
lean_inc(v_fst_1880_);
lean_dec(v_b_1875_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1914_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v_array_1884_; lean_object* v_start_1885_; lean_object* v_stop_1886_; uint8_t v___x_1887_; 
v_array_1884_ = lean_ctor_get(v_snd_1879_, 0);
v_start_1885_ = lean_ctor_get(v_snd_1879_, 1);
v_stop_1886_ = lean_ctor_get(v_snd_1879_, 2);
v___x_1887_ = lean_nat_dec_lt(v_start_1885_, v_stop_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1889_; 
if (v_isShared_1883_ == 0)
{
v___x_1889_ = v___x_1882_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_fst_1880_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_snd_1879_);
v___x_1889_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
}
else
{
lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1910_; 
lean_inc(v_stop_1886_);
lean_inc(v_start_1885_);
lean_inc_ref(v_array_1884_);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_snd_1879_);
if (v_isSharedCheck_1910_ == 0)
{
lean_object* v_unused_1911_; lean_object* v_unused_1912_; lean_object* v_unused_1913_; 
v_unused_1911_ = lean_ctor_get(v_snd_1879_, 2);
lean_dec(v_unused_1911_);
v_unused_1912_ = lean_ctor_get(v_snd_1879_, 1);
lean_dec(v_unused_1912_);
v_unused_1913_ = lean_ctor_get(v_snd_1879_, 0);
lean_dec(v_unused_1913_);
v___x_1893_ = v_snd_1879_;
v_isShared_1894_ = v_isSharedCheck_1910_;
goto v_resetjp_1892_;
}
else
{
lean_dec(v_snd_1879_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1910_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_a_1895_; lean_object* v_fvarId_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v_a_1895_ = lean_array_uget_borrowed(v_as_1872_, v_i_1874_);
v_fvarId_1896_ = lean_ctor_get(v_a_1895_, 0);
v___x_1897_ = lean_array_fget(v_array_1884_, v_start_1885_);
v___x_1898_ = lean_unsigned_to_nat(1u);
v___x_1899_ = lean_nat_add(v_start_1885_, v___x_1898_);
lean_dec(v_start_1885_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 1, v___x_1899_);
v___x_1901_ = v___x_1893_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_array_1884_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v_stop_1886_);
v___x_1901_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
lean_inc(v_fvarId_1896_);
v___x_1902_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_fst_1880_, v_fvarId_1896_, v___x_1897_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 1, v___x_1901_);
lean_ctor_set(v___x_1882_, 0, v___x_1902_);
v___x_1904_ = v___x_1882_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1902_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v___x_1901_);
v___x_1904_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
size_t v___x_1905_; size_t v___x_1906_; 
v___x_1905_ = ((size_t)1ULL);
v___x_1906_ = lean_usize_add(v_i_1874_, v___x_1905_);
v_i_1874_ = v___x_1906_;
v_b_1875_ = v___x_1904_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1872_ = stack[0].m_obj;
size_t v_sz_1873_ = stack[1].m_num;
size_t v_i_1874_ = stack[2].m_num;
lean_object* v_b_1875_ = stack[3].m_obj;
lean_object* v_res_1915_;
v_res_1915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_1872_, v_sz_1873_, v_i_1874_, v_b_1875_);
stack->m_obj
 = v_res_1915_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg___boxed(lean_object* v_as_1916_, lean_object* v_sz_1917_, lean_object* v_i_1918_, lean_object* v_b_1919_, lean_object* v___y_1920_){
_start:
{
size_t v_sz_boxed_1921_; size_t v_i_boxed_1922_; lean_object* v_res_1923_; 
v_sz_boxed_1921_ = lean_unbox_usize(v_sz_1917_);
lean_dec(v_sz_1917_);
v_i_boxed_1922_ = lean_unbox_usize(v_i_1918_);
lean_dec(v_i_1918_);
v_res_1923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_1916_, v_sz_boxed_1921_, v_i_boxed_1922_, v_b_1919_);
lean_dec_ref(v_as_1916_);
return v_res_1923_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object* v_params_1924_, lean_object* v_code_1925_, lean_object* v_args_1926_, uint8_t v_mustInline_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v___x_1936_; lean_object* v_subst_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; size_t v_sz_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1936_ = lean_unsigned_to_nat(0u);
v_subst_1937_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1, &l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1);
v___x_1938_ = lean_array_get_size(v_args_1926_);
v___x_1939_ = l_Array_toSubarray___redArg(v_args_1926_, v___x_1936_, v___x_1938_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v_subst_1937_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v_sz_1941_ = lean_array_size(v_params_1924_);
v___x_1942_ = ((size_t)0ULL);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_params_1924_, v_sz_1941_, v___x_1942_, v___x_1940_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v_fst_1945_; uint8_t v___x_1946_; uint8_t v___x_1947_; lean_object* v___x_1948_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v_fst_1945_ = lean_ctor_get(v_a_1944_, 0);
lean_inc(v_fst_1945_);
lean_dec(v_a_1944_);
v___x_1946_ = 0;
v___x_1947_ = 0;
v___x_1948_ = l_Lean_Compiler_LCNF_Code_internalize(v___x_1946_, v_code_1925_, v_fst_1945_, v___x_1947_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc_n(v_a_1949_, 2);
lean_dec_ref_known(v___x_1948_, 1);
v___x_1950_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(v_a_1949_, v_mustInline_1927_, v_a_1929_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; 
v_unused_1958_ = lean_ctor_get(v___x_1950_, 0);
lean_dec(v_unused_1958_);
v___x_1952_ = v___x_1950_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_dec(v___x_1950_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v_a_1949_);
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1949_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v_a_1949_);
v_a_1959_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1950_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1950_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
return v___x_1948_;
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec_ref(v_code_1925_);
v_a_1967_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1943_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1943_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_betaReduce_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_1924_ = stack[0].m_obj;
lean_object* v_code_1925_ = stack[1].m_obj;
lean_object* v_args_1926_ = stack[2].m_obj;
uint8_t v_mustInline_1927_ = stack[3].m_num;
lean_object* v_a_1928_ = stack[4].m_obj;
lean_object* v_a_1929_ = stack[5].m_obj;
lean_object* v_a_1930_ = stack[6].m_obj;
lean_object* v_a_1931_ = stack[7].m_obj;
lean_object* v_a_1932_ = stack[8].m_obj;
lean_object* v_a_1933_ = stack[9].m_obj;
lean_object* v_a_1934_ = stack[10].m_obj;
lean_object* v_res_1975_;
v_res_1975_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1924_, v_code_1925_, v_args_1926_, v_mustInline_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
stack->m_obj
 = v_res_1975_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(lean_object* v_params_1976_, lean_object* v_code_1977_, lean_object* v_args_1978_, lean_object* v_mustInline_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
uint8_t v_mustInline_boxed_1988_; lean_object* v_res_1989_; 
v_mustInline_boxed_1988_ = lean_unbox(v_mustInline_1979_);
v_res_1989_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v_params_1976_, v_code_1977_, v_args_1978_, v_mustInline_boxed_1988_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec_ref(v_params_1976_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0(lean_object* v_00_u03b2_1990_, lean_object* v_m_1991_, lean_object* v_a_1992_, lean_object* v_b_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_m_1991_, v_a_1992_, v_b_1993_);
return v___x_1994_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(lean_object* v_as_1995_, size_t v_sz_1996_, size_t v_i_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_1995_, v_sz_1996_, v_i_1997_, v_b_1998_);
return v___x_2007_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1995_ = stack[0].m_obj;
size_t v_sz_1996_ = stack[1].m_num;
size_t v_i_1997_ = stack[2].m_num;
lean_object* v_b_1998_ = stack[3].m_obj;
lean_object* v___y_1999_ = stack[4].m_obj;
lean_object* v___y_2000_ = stack[5].m_obj;
lean_object* v___y_2001_ = stack[6].m_obj;
lean_object* v___y_2002_ = stack[7].m_obj;
lean_object* v___y_2003_ = stack[8].m_obj;
lean_object* v___y_2004_ = stack[9].m_obj;
lean_object* v___y_2005_ = stack[10].m_obj;
lean_object* v_res_2008_;
v_res_2008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(v_as_1995_, v_sz_1996_, v_i_1997_, v_b_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
stack->m_obj
 = v_res_2008_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___boxed(lean_object* v_as_2009_, lean_object* v_sz_2010_, lean_object* v_i_2011_, lean_object* v_b_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
size_t v_sz_boxed_2021_; size_t v_i_boxed_2022_; lean_object* v_res_2023_; 
v_sz_boxed_2021_ = lean_unbox_usize(v_sz_2010_);
lean_dec(v_sz_2010_);
v_i_boxed_2022_ = lean_unbox_usize(v_i_2011_);
lean_dec(v_i_2011_);
v_res_2023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(v_as_2009_, v_sz_boxed_2021_, v_i_boxed_2022_, v_b_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec_ref(v_as_2009_);
return v_res_2023_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(lean_object* v_00_u03b2_2024_, lean_object* v_a_2025_, lean_object* v_x_2026_){
_start:
{
uint8_t v___x_2027_; 
v___x_2027_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_2025_, v_x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2025_ = stack[1].m_obj;
lean_object* v_x_2026_ = stack[2].m_obj;
uint8_t v_res_2028_;
v_res_2028_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(lean_box(0), v_a_2025_, v_x_2026_);
stack->m_num = v_res_2028_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2029_, lean_object* v_a_2030_, lean_object* v_x_2031_){
_start:
{
uint8_t v_res_2032_; lean_object* v_r_2033_; 
v_res_2032_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(v_00_u03b2_2029_, v_a_2030_, v_x_2031_);
lean_dec(v_x_2031_);
lean_dec(v_a_2030_);
v_r_2033_ = lean_box(v_res_2032_);
return v_r_2033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1(lean_object* v_00_u03b2_2034_, lean_object* v_data_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(v_data_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2(lean_object* v_00_u03b2_2037_, lean_object* v_a_2038_, lean_object* v_b_2039_, lean_object* v_x_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_2038_, v_b_2039_, v_x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2042_, lean_object* v_i_2043_, lean_object* v_source_2044_, lean_object* v_target_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(v_i_2043_, v_source_2044_, v_target_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2048_, v_x_2049_);
return v___x_2050_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(lean_object* v_decl_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
uint8_t v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = 0;
v___x_2056_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2055_, v_decl_2051_, v_a_2053_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v___x_2057_; 
lean_dec_ref_known(v___x_2056_, 1);
v___x_2057_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2052_);
return v___x_2057_;
}
else
{
return v___x_2056_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2051_ = stack[0].m_obj;
lean_object* v_a_2052_ = stack[1].m_obj;
lean_object* v_a_2053_ = stack[2].m_obj;
lean_object* v_res_2058_;
v_res_2058_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2051_, v_a_2052_, v_a_2053_);
stack->m_obj
 = v_res_2058_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg___boxed(lean_object* v_decl_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2059_, v_a_2060_, v_a_2061_);
lean_dec(v_a_2061_);
lean_dec(v_a_2060_);
lean_dec_ref(v_decl_2059_);
return v_res_2063_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object* v_decl_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_2064_, v_a_2066_, v_a_2069_);
return v___x_2073_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_eraseLetDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2064_ = stack[0].m_obj;
lean_object* v_a_2065_ = stack[1].m_obj;
lean_object* v_a_2066_ = stack[2].m_obj;
lean_object* v_a_2067_ = stack[3].m_obj;
lean_object* v_a_2068_ = stack[4].m_obj;
lean_object* v_a_2069_ = stack[5].m_obj;
lean_object* v_a_2070_ = stack[6].m_obj;
lean_object* v_a_2071_ = stack[7].m_obj;
lean_object* v_res_2074_;
v_res_2074_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(v_decl_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
stack->m_obj
 = v_res_2074_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(lean_object* v_decl_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(v_decl_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_decl_2075_);
return v_res_2084_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(lean_object* v_decl_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
uint8_t v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = 0;
v___x_2090_ = 1;
v___x_2091_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_2089_, v_decl_2085_, v___x_2090_, v_a_2087_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v___x_2092_; 
lean_dec_ref_known(v___x_2091_, 1);
v___x_2092_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2086_);
return v___x_2092_;
}
else
{
return v___x_2091_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2085_ = stack[0].m_obj;
lean_object* v_a_2086_ = stack[1].m_obj;
lean_object* v_a_2087_ = stack[2].m_obj;
lean_object* v_res_2093_;
v_res_2093_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2085_, v_a_2086_, v_a_2087_);
stack->m_obj
 = v_res_2093_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg___boxed(lean_object* v_decl_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2094_, v_a_2095_, v_a_2096_);
lean_dec(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_decl_2094_);
return v_res_2098_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object* v_decl_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_2099_, v_a_2101_, v_a_2104_);
return v___x_2108_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_eraseFunDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2099_ = stack[0].m_obj;
lean_object* v_a_2100_ = stack[1].m_obj;
lean_object* v_a_2101_ = stack[2].m_obj;
lean_object* v_a_2102_ = stack[3].m_obj;
lean_object* v_a_2103_ = stack[4].m_obj;
lean_object* v_a_2104_ = stack[5].m_obj;
lean_object* v_a_2105_ = stack[6].m_obj;
lean_object* v_a_2106_ = stack[7].m_obj;
lean_object* v_res_2109_;
v_res_2109_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(v_decl_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
stack->m_obj
 = v_res_2109_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(lean_object* v_decl_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(v_decl_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
lean_dec_ref(v_a_2111_);
lean_dec_ref(v_decl_2110_);
return v_res_2119_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object* v_fvarId_2120_, lean_object* v_fvarId_x27_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v_subst_2129_; lean_object* v_used_2130_; lean_object* v_binderRenaming_2131_; lean_object* v_funDeclInfoMap_2132_; uint8_t v_simplified_2133_; lean_object* v_visited_2134_; lean_object* v_inline_2135_; lean_object* v_inlineLocal_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2206_; 
v___x_2128_ = lean_st_ref_take(v_a_2122_);
v_subst_2129_ = lean_ctor_get(v___x_2128_, 0);
v_used_2130_ = lean_ctor_get(v___x_2128_, 1);
v_binderRenaming_2131_ = lean_ctor_get(v___x_2128_, 2);
v_funDeclInfoMap_2132_ = lean_ctor_get(v___x_2128_, 3);
v_simplified_2133_ = lean_ctor_get_uint8(v___x_2128_, sizeof(void*)*7);
v_visited_2134_ = lean_ctor_get(v___x_2128_, 4);
v_inline_2135_ = lean_ctor_get(v___x_2128_, 5);
v_inlineLocal_2136_ = lean_ctor_get(v___x_2128_, 6);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2138_ = v___x_2128_;
v_isShared_2139_ = v_isSharedCheck_2206_;
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
v_isShared_2139_ = v_isSharedCheck_2206_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
lean_inc(v_fvarId_x27_2121_);
v___x_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2140_, 0, v_fvarId_x27_2121_);
lean_inc(v_fvarId_2120_);
v___x_2141_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_subst_2129_, v_fvarId_2120_, v___x_2140_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2141_);
v___x_2143_ = v___x_2138_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_used_2130_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_binderRenaming_2131_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_funDeclInfoMap_2132_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v_visited_2134_);
lean_ctor_set(v_reuseFailAlloc_2205_, 5, v_inline_2135_);
lean_ctor_set(v_reuseFailAlloc_2205_, 6, v_inlineLocal_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*7, v_simplified_2133_);
v___x_2143_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_st_ref_put(v_a_2122_, v___x_2143_);
v___x_2145_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_2120_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2196_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2196_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2196_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
uint8_t v___x_2150_; 
v___x_2150_ = l_Lean_Name_isInternal(v_a_2146_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
lean_del_object(v___x_2148_);
lean_inc(v_fvarId_x27_2121_);
v___x_2151_ = l_Lean_Compiler_LCNF_getBinderName(v_fvarId_x27_2121_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2183_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2154_ = v___x_2151_;
v_isShared_2155_ = v_isSharedCheck_2183_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2151_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2183_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
uint8_t v___x_2156_; 
v___x_2156_ = l_Lean_Name_isInternal(v_a_2152_);
lean_dec(v_a_2152_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
lean_dec(v_a_2146_);
lean_dec(v_fvarId_x27_2121_);
v___x_2157_ = lean_box(0);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2157_);
v___x_2159_ = v___x_2154_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
else
{
lean_object* v___x_2161_; lean_object* v_subst_2162_; lean_object* v_used_2163_; lean_object* v_binderRenaming_2164_; lean_object* v_funDeclInfoMap_2165_; uint8_t v_simplified_2166_; lean_object* v_visited_2167_; lean_object* v_inline_2168_; lean_object* v_inlineLocal_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2182_; 
v___x_2161_ = lean_st_ref_take(v_a_2122_);
v_subst_2162_ = lean_ctor_get(v___x_2161_, 0);
v_used_2163_ = lean_ctor_get(v___x_2161_, 1);
v_binderRenaming_2164_ = lean_ctor_get(v___x_2161_, 2);
v_funDeclInfoMap_2165_ = lean_ctor_get(v___x_2161_, 3);
v_simplified_2166_ = lean_ctor_get_uint8(v___x_2161_, sizeof(void*)*7);
v_visited_2167_ = lean_ctor_get(v___x_2161_, 4);
v_inline_2168_ = lean_ctor_get(v___x_2161_, 5);
v_inlineLocal_2169_ = lean_ctor_get(v___x_2161_, 6);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2171_ = v___x_2161_;
v_isShared_2172_ = v_isSharedCheck_2182_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_inlineLocal_2169_);
lean_inc(v_inline_2168_);
lean_inc(v_visited_2167_);
lean_inc(v_funDeclInfoMap_2165_);
lean_inc(v_binderRenaming_2164_);
lean_inc(v_used_2163_);
lean_inc(v_subst_2162_);
lean_dec(v___x_2161_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2182_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2173_ = lean_box(0);
v___x_2174_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_x27_2121_, v_a_2146_, v_binderRenaming_2164_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 2, v___x_2174_);
v___x_2176_ = v___x_2171_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_subst_2162_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_used_2163_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_funDeclInfoMap_2165_);
lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_visited_2167_);
lean_ctor_set(v_reuseFailAlloc_2181_, 5, v_inline_2168_);
lean_ctor_set(v_reuseFailAlloc_2181_, 6, v_inlineLocal_2169_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, sizeof(void*)*7, v_simplified_2166_);
v___x_2176_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2177_ = lean_st_ref_put(v_a_2122_, v___x_2176_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2173_);
v___x_2179_ = v___x_2154_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2173_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_a_2146_);
lean_dec(v_fvarId_x27_2121_);
v_a_2184_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2151_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2151_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2194_; 
lean_dec(v_a_2146_);
lean_dec(v_fvarId_x27_2121_);
v___x_2192_ = lean_box(0);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2192_);
v___x_2194_ = v___x_2148_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v_fvarId_x27_2121_);
v_a_2197_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2145_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2145_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
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
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2120_ = stack[0].m_obj;
lean_object* v_fvarId_x27_2121_ = stack[1].m_obj;
lean_object* v_a_2122_ = stack[2].m_obj;
lean_object* v_a_2123_ = stack[3].m_obj;
lean_object* v_a_2124_ = stack[4].m_obj;
lean_object* v_a_2125_ = stack[5].m_obj;
lean_object* v_a_2126_ = stack[6].m_obj;
lean_object* v_res_2207_;
v_res_2207_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2120_, v_fvarId_x27_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
stack->m_obj
 = v_res_2207_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg___boxed(lean_object* v_fvarId_2208_, lean_object* v_fvarId_x27_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2208_, v_fvarId_x27_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
return v_res_2216_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object* v_fvarId_2217_, lean_object* v_fvarId_x27_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_2217_, v_fvarId_x27_2218_, v_a_2220_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
return v___x_2227_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_addFVarSubst_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2217_ = stack[0].m_obj;
lean_object* v_fvarId_x27_2218_ = stack[1].m_obj;
lean_object* v_a_2219_ = stack[2].m_obj;
lean_object* v_a_2220_ = stack[3].m_obj;
lean_object* v_a_2221_ = stack[4].m_obj;
lean_object* v_a_2222_ = stack[5].m_obj;
lean_object* v_a_2223_ = stack[6].m_obj;
lean_object* v_a_2224_ = stack[7].m_obj;
lean_object* v_a_2225_ = stack[8].m_obj;
lean_object* v_res_2228_;
v_res_2228_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst(v_fvarId_2217_, v_fvarId_x27_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
stack->m_obj
 = v_res_2228_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___boxed(lean_object* v_fvarId_2229_, lean_object* v_fvarId_x27_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst(v_fvarId_2229_, v_fvarId_x27_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
return v_res_2239_;
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
