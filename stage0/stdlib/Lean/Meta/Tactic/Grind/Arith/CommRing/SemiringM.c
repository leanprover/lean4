// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadSemiring import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr public import Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "`grind` internal error, invalid semiringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "`grind` internal error, invalid ringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4_value),LEAN_SCALAR_PTR_LITERAL(232, 146, 236, 221, 122, 127, 105, 70)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "expression in two different semirings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "failed to find instance"};
static const lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM.0.Lean.Grind.CommRing.Expr.denoteAsRingExpr.go"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(lean_object* v_semiringId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc(v_a_3_);
v___x_14_ = lean_apply_12(v_x_2_, v_semiringId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg___boxed(lean_object* v_semiringId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(v_semiringId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_a_18_);
lean_dec(v_a_17_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(lean_object* v_00_u03b1_29_, lean_object* v_semiringId_30_, lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
lean_inc(v_a_41_);
lean_inc_ref(v_a_40_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc(v_a_32_);
v___x_43_ = lean_apply_12(v_x_31_, v_semiringId_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___boxed(lean_object* v_00_u03b1_44_, lean_object* v_semiringId_45_, lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(v_00_u03b1_44_, v_semiringId_45_, v_x_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec(v_a_47_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
lean_inc(v_a_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_a_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg___boxed(lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(v_a_62_);
lean_dec(v_a_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
lean_inc(v_a_65_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v_a_65_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___boxed(lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec(v_a_79_);
lean_dec(v_a_78_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(lean_object* v_e_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_Sym_canon(v_e_91_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_106_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v___x_106_ = l_Lean_Meta_Sym_shareCommon(v_a_105_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
return v___x_106_;
}
else
{
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed(lean_object* v_e_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(v_e_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec(v___y_109_);
lean_dec(v___y_108_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(lean_object* v_e_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_121_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed(lean_object* v_e_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(v_e_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec(v___y_137_);
lean_dec(v___y_136_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(lean_object* v_msgData_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; lean_object* v_env_162_; lean_object* v___x_163_; lean_object* v_mctx_164_; lean_object* v_lctx_165_; lean_object* v_options_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_161_ = lean_st_ref_get(v___y_159_);
v_env_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc_ref(v_env_162_);
lean_dec(v___x_161_);
v___x_163_ = lean_st_ref_get(v___y_157_);
v_mctx_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc_ref(v_mctx_164_);
lean_dec(v___x_163_);
v_lctx_165_ = lean_ctor_get(v___y_156_, 2);
v_options_166_ = lean_ctor_get(v___y_158_, 2);
lean_inc_ref(v_options_166_);
lean_inc_ref(v_lctx_165_);
v___x_167_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_167_, 0, v_env_162_);
lean_ctor_set(v___x_167_, 1, v_mctx_164_);
lean_ctor_set(v___x_167_, 2, v_lctx_165_);
lean_ctor_set(v___x_167_, 3, v_options_166_);
v___x_168_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v_msgData_155_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0___boxed(lean_object* v_msgData_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msgData_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(lean_object* v_msg_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_ref_183_; lean_object* v___x_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
v_ref_183_ = lean_ctor_get(v___y_180_, 5);
v___x_184_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msg_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_193_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
lean_inc(v_ref_183_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_ref_183_);
lean_ctor_set(v___x_189_, 1, v_a_185_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 1);
lean_ctor_set(v___x_187_, 0, v___x_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg___boxed(lean_object* v_msg_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_200_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_205_, v_a_213_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_230_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_230_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_230_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_230_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_semirings_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_semirings_221_ = lean_ctor_get(v_a_217_, 3);
lean_inc_ref(v_semirings_221_);
lean_dec(v_a_217_);
v___x_222_ = lean_array_get_size(v_semirings_221_);
v___x_223_ = lean_nat_dec_lt(v_a_204_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec_ref(v_semirings_221_);
lean_del_object(v___x_219_);
v___x_224_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1);
v___x_225_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_224_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_array_fget(v_semirings_221_, v_a_204_);
lean_dec_ref(v_semirings_221_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_226_);
v___x_228_ = v___x_219_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
v_a_231_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_216_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_216_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed(lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec(v_a_240_);
lean_dec(v_a_239_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(lean_object* v_00_u03b1_252_, lean_object* v_msg_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_253_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___boxed(lean_object* v_00_u03b1_267_, lean_object* v_msg_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(v_00_u03b1_267_, v_msg_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec(v___y_270_);
lean_dec(v___y_269_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(lean_object* v_a_282_, lean_object* v_f_283_, lean_object* v_s_284_){
_start:
{
lean_object* v_rings_285_; lean_object* v_typeIdOf_286_; lean_object* v_exprToRingId_287_; lean_object* v_semirings_288_; lean_object* v_stypeIdOf_289_; lean_object* v_exprToSemiringId_290_; lean_object* v_ncRings_291_; lean_object* v_exprToNCRingId_292_; lean_object* v_nctypeIdOf_293_; lean_object* v_ncSemirings_294_; lean_object* v_exprToNCSemiringId_295_; lean_object* v_ncstypeIdOf_296_; lean_object* v_steps_297_; uint8_t v_reportedMaxDegreeIssue_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_rings_285_ = lean_ctor_get(v_s_284_, 0);
v_typeIdOf_286_ = lean_ctor_get(v_s_284_, 1);
v_exprToRingId_287_ = lean_ctor_get(v_s_284_, 2);
v_semirings_288_ = lean_ctor_get(v_s_284_, 3);
v_stypeIdOf_289_ = lean_ctor_get(v_s_284_, 4);
v_exprToSemiringId_290_ = lean_ctor_get(v_s_284_, 5);
v_ncRings_291_ = lean_ctor_get(v_s_284_, 6);
v_exprToNCRingId_292_ = lean_ctor_get(v_s_284_, 7);
v_nctypeIdOf_293_ = lean_ctor_get(v_s_284_, 8);
v_ncSemirings_294_ = lean_ctor_get(v_s_284_, 9);
v_exprToNCSemiringId_295_ = lean_ctor_get(v_s_284_, 10);
v_ncstypeIdOf_296_ = lean_ctor_get(v_s_284_, 11);
v_steps_297_ = lean_ctor_get(v_s_284_, 12);
v_reportedMaxDegreeIssue_298_ = lean_ctor_get_uint8(v_s_284_, sizeof(void*)*13);
v___x_299_ = lean_array_get_size(v_semirings_288_);
v___x_300_ = lean_nat_dec_lt(v_a_282_, v___x_299_);
if (v___x_300_ == 0)
{
lean_dec_ref(v_f_283_);
return v_s_284_;
}
else
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_312_; 
lean_inc(v_steps_297_);
lean_inc_ref(v_ncstypeIdOf_296_);
lean_inc_ref(v_exprToNCSemiringId_295_);
lean_inc_ref(v_ncSemirings_294_);
lean_inc_ref(v_nctypeIdOf_293_);
lean_inc_ref(v_exprToNCRingId_292_);
lean_inc_ref(v_ncRings_291_);
lean_inc_ref(v_exprToSemiringId_290_);
lean_inc_ref(v_stypeIdOf_289_);
lean_inc_ref(v_semirings_288_);
lean_inc_ref(v_exprToRingId_287_);
lean_inc_ref(v_typeIdOf_286_);
lean_inc_ref(v_rings_285_);
v_isSharedCheck_312_ = !lean_is_exclusive(v_s_284_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; lean_object* v_unused_319_; lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; lean_object* v_unused_324_; lean_object* v_unused_325_; 
v_unused_313_ = lean_ctor_get(v_s_284_, 12);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_s_284_, 11);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_s_284_, 10);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_s_284_, 9);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_s_284_, 8);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_s_284_, 7);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_s_284_, 6);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_s_284_, 5);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_s_284_, 4);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_s_284_, 3);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_s_284_, 2);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_s_284_, 1);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_s_284_, 0);
lean_dec(v_unused_325_);
v___x_302_ = v_s_284_;
v_isShared_303_ = v_isSharedCheck_312_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_s_284_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_312_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_v_304_; lean_object* v___x_305_; lean_object* v_xs_x27_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v_v_304_ = lean_array_fget(v_semirings_288_, v_a_282_);
v___x_305_ = lean_box(0);
v_xs_x27_306_ = lean_array_fset(v_semirings_288_, v_a_282_, v___x_305_);
v___x_307_ = lean_apply_1(v_f_283_, v_v_304_);
v___x_308_ = lean_array_fset(v_xs_x27_306_, v_a_282_, v___x_307_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 3, v___x_308_);
v___x_310_ = v___x_302_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_rings_285_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_typeIdOf_286_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_exprToRingId_287_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_stypeIdOf_289_);
lean_ctor_set(v_reuseFailAlloc_311_, 5, v_exprToSemiringId_290_);
lean_ctor_set(v_reuseFailAlloc_311_, 6, v_ncRings_291_);
lean_ctor_set(v_reuseFailAlloc_311_, 7, v_exprToNCRingId_292_);
lean_ctor_set(v_reuseFailAlloc_311_, 8, v_nctypeIdOf_293_);
lean_ctor_set(v_reuseFailAlloc_311_, 9, v_ncSemirings_294_);
lean_ctor_set(v_reuseFailAlloc_311_, 10, v_exprToNCSemiringId_295_);
lean_ctor_set(v_reuseFailAlloc_311_, 11, v_ncstypeIdOf_296_);
lean_ctor_set(v_reuseFailAlloc_311_, 12, v_steps_297_);
lean_ctor_set_uint8(v_reuseFailAlloc_311_, sizeof(void*)*13, v_reportedMaxDegreeIssue_298_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed(lean_object* v_a_326_, lean_object* v_f_327_, lean_object* v_s_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(v_a_326_, v_f_327_, v_s_328_);
lean_dec(v_a_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(lean_object* v_f_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___f_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
lean_inc(v_a_331_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_334_, 0, v_a_331_);
lean_closure_set(v___f_334_, 1, v_f_330_);
v___x_335_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_336_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_335_, v___f_334_, v_a_332_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___boxed(lean_object* v_f_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(v_f_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec(v_a_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(lean_object* v_f_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___f_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
lean_inc(v_a_343_);
v___f_355_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_355_, 0, v_a_343_);
lean_closure_set(v___f_355_, 1, v_f_342_);
v___x_356_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_357_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_356_, v___f_355_, v_a_344_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed(lean_object* v_f_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(v_f_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec(v_a_360_);
lean_dec(v_a_359_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0));
v___x_374_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed), 12, 0);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0));
v___x_379_ = l_Lean_stringToMessageData(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_381_, v_a_389_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_394_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v___x_392_, 1);
v___x_394_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_409_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_409_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_409_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_409_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_ringId_399_; lean_object* v_rings_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_ringId_399_ = lean_ctor_get(v_a_395_, 1);
lean_inc(v_ringId_399_);
lean_dec(v_a_395_);
v_rings_400_ = lean_ctor_get(v_a_393_, 0);
lean_inc_ref(v_rings_400_);
lean_dec(v_a_393_);
v___x_401_ = lean_array_get_size(v_rings_400_);
v___x_402_ = lean_nat_dec_lt(v_ringId_399_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref(v_rings_400_);
lean_dec(v_ringId_399_);
lean_del_object(v___x_397_);
v___x_403_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1);
v___x_404_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_403_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
return v___x_404_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_array_fget(v_rings_400_, v_ringId_399_);
lean_dec(v_ringId_399_);
lean_dec_ref(v_rings_400_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_405_);
v___x_407_ = v___x_397_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_a_393_);
v_a_410_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_394_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_394_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
v_a_418_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_392_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_392_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed(lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec(v_a_427_);
lean_dec(v_a_426_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(lean_object* v_ringId_439_, lean_object* v_f_440_, lean_object* v_s_441_){
_start:
{
lean_object* v_rings_442_; lean_object* v_typeIdOf_443_; lean_object* v_exprToRingId_444_; lean_object* v_semirings_445_; lean_object* v_stypeIdOf_446_; lean_object* v_exprToSemiringId_447_; lean_object* v_ncRings_448_; lean_object* v_exprToNCRingId_449_; lean_object* v_nctypeIdOf_450_; lean_object* v_ncSemirings_451_; lean_object* v_exprToNCSemiringId_452_; lean_object* v_ncstypeIdOf_453_; lean_object* v_steps_454_; uint8_t v_reportedMaxDegreeIssue_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v_rings_442_ = lean_ctor_get(v_s_441_, 0);
v_typeIdOf_443_ = lean_ctor_get(v_s_441_, 1);
v_exprToRingId_444_ = lean_ctor_get(v_s_441_, 2);
v_semirings_445_ = lean_ctor_get(v_s_441_, 3);
v_stypeIdOf_446_ = lean_ctor_get(v_s_441_, 4);
v_exprToSemiringId_447_ = lean_ctor_get(v_s_441_, 5);
v_ncRings_448_ = lean_ctor_get(v_s_441_, 6);
v_exprToNCRingId_449_ = lean_ctor_get(v_s_441_, 7);
v_nctypeIdOf_450_ = lean_ctor_get(v_s_441_, 8);
v_ncSemirings_451_ = lean_ctor_get(v_s_441_, 9);
v_exprToNCSemiringId_452_ = lean_ctor_get(v_s_441_, 10);
v_ncstypeIdOf_453_ = lean_ctor_get(v_s_441_, 11);
v_steps_454_ = lean_ctor_get(v_s_441_, 12);
v_reportedMaxDegreeIssue_455_ = lean_ctor_get_uint8(v_s_441_, sizeof(void*)*13);
v___x_456_ = lean_array_get_size(v_rings_442_);
v___x_457_ = lean_nat_dec_lt(v_ringId_439_, v___x_456_);
if (v___x_457_ == 0)
{
lean_dec_ref(v_f_440_);
return v_s_441_;
}
else
{
lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_469_; 
lean_inc(v_steps_454_);
lean_inc_ref(v_ncstypeIdOf_453_);
lean_inc_ref(v_exprToNCSemiringId_452_);
lean_inc_ref(v_ncSemirings_451_);
lean_inc_ref(v_nctypeIdOf_450_);
lean_inc_ref(v_exprToNCRingId_449_);
lean_inc_ref(v_ncRings_448_);
lean_inc_ref(v_exprToSemiringId_447_);
lean_inc_ref(v_stypeIdOf_446_);
lean_inc_ref(v_semirings_445_);
lean_inc_ref(v_exprToRingId_444_);
lean_inc_ref(v_typeIdOf_443_);
lean_inc_ref(v_rings_442_);
v_isSharedCheck_469_ = !lean_is_exclusive(v_s_441_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; lean_object* v_unused_479_; lean_object* v_unused_480_; lean_object* v_unused_481_; lean_object* v_unused_482_; 
v_unused_470_ = lean_ctor_get(v_s_441_, 12);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_s_441_, 11);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_s_441_, 10);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_s_441_, 9);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_s_441_, 8);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_s_441_, 7);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_s_441_, 6);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_s_441_, 5);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_s_441_, 4);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_s_441_, 3);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_s_441_, 2);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_s_441_, 1);
lean_dec(v_unused_481_);
v_unused_482_ = lean_ctor_get(v_s_441_, 0);
lean_dec(v_unused_482_);
v___x_459_ = v_s_441_;
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
else
{
lean_dec(v_s_441_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_v_461_; lean_object* v___x_462_; lean_object* v_xs_x27_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v_v_461_ = lean_array_fget(v_rings_442_, v_ringId_439_);
v___x_462_ = lean_box(0);
v_xs_x27_463_ = lean_array_fset(v_rings_442_, v_ringId_439_, v___x_462_);
v___x_464_ = lean_apply_1(v_f_440_, v_v_461_);
v___x_465_ = lean_array_fset(v_xs_x27_463_, v_ringId_439_, v___x_464_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_465_);
v___x_467_ = v___x_459_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_typeIdOf_443_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_exprToRingId_444_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_semirings_445_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_stypeIdOf_446_);
lean_ctor_set(v_reuseFailAlloc_468_, 5, v_exprToSemiringId_447_);
lean_ctor_set(v_reuseFailAlloc_468_, 6, v_ncRings_448_);
lean_ctor_set(v_reuseFailAlloc_468_, 7, v_exprToNCRingId_449_);
lean_ctor_set(v_reuseFailAlloc_468_, 8, v_nctypeIdOf_450_);
lean_ctor_set(v_reuseFailAlloc_468_, 9, v_ncSemirings_451_);
lean_ctor_set(v_reuseFailAlloc_468_, 10, v_exprToNCSemiringId_452_);
lean_ctor_set(v_reuseFailAlloc_468_, 11, v_ncstypeIdOf_453_);
lean_ctor_set(v_reuseFailAlloc_468_, 12, v_steps_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_468_, sizeof(void*)*13, v_reportedMaxDegreeIssue_455_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed(lean_object* v_ringId_483_, lean_object* v_f_484_, lean_object* v_s_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(v_ringId_483_, v_f_484_, v_s_485_);
lean_dec(v_ringId_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(lean_object* v_f_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v_ringId_502_; lean_object* v___f_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v_ringId_502_ = lean_ctor_get(v_a_501_, 1);
lean_inc(v_ringId_502_);
lean_dec(v_a_501_);
v___f_503_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed), 3, 2);
lean_closure_set(v___f_503_, 0, v_ringId_502_);
lean_closure_set(v___f_503_, 1, v_f_487_);
v___x_504_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_505_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_504_, v___f_503_, v_a_489_);
return v___x_505_;
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec_ref(v_f_487_);
v_a_506_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_500_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_500_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed(lean_object* v_f_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v_f_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec(v_a_516_);
lean_dec(v_a_515_);
return v_res_527_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0));
v___x_530_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed), 12, 0);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM(void){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_s_535_){
_start:
{
lean_object* v_rings_536_; lean_object* v_typeIdOf_537_; lean_object* v_exprToRingId_538_; lean_object* v_semirings_539_; lean_object* v_stypeIdOf_540_; lean_object* v_exprToSemiringId_541_; lean_object* v_ncRings_542_; lean_object* v_exprToNCRingId_543_; lean_object* v_nctypeIdOf_544_; lean_object* v_ncSemirings_545_; lean_object* v_exprToNCSemiringId_546_; lean_object* v_ncstypeIdOf_547_; lean_object* v_steps_548_; uint8_t v_reportedMaxDegreeIssue_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_rings_536_ = lean_ctor_get(v_s_535_, 0);
v_typeIdOf_537_ = lean_ctor_get(v_s_535_, 1);
v_exprToRingId_538_ = lean_ctor_get(v_s_535_, 2);
v_semirings_539_ = lean_ctor_get(v_s_535_, 3);
v_stypeIdOf_540_ = lean_ctor_get(v_s_535_, 4);
v_exprToSemiringId_541_ = lean_ctor_get(v_s_535_, 5);
v_ncRings_542_ = lean_ctor_get(v_s_535_, 6);
v_exprToNCRingId_543_ = lean_ctor_get(v_s_535_, 7);
v_nctypeIdOf_544_ = lean_ctor_get(v_s_535_, 8);
v_ncSemirings_545_ = lean_ctor_get(v_s_535_, 9);
v_exprToNCSemiringId_546_ = lean_ctor_get(v_s_535_, 10);
v_ncstypeIdOf_547_ = lean_ctor_get(v_s_535_, 11);
v_steps_548_ = lean_ctor_get(v_s_535_, 12);
v_reportedMaxDegreeIssue_549_ = lean_ctor_get_uint8(v_s_535_, sizeof(void*)*13);
v___x_550_ = lean_array_get_size(v_semirings_539_);
v___x_551_ = lean_nat_dec_lt(v_a_533_, v___x_550_);
if (v___x_551_ == 0)
{
lean_dec_ref(v_a_534_);
return v_s_535_;
}
else
{
lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_575_; 
lean_inc(v_steps_548_);
lean_inc_ref(v_ncstypeIdOf_547_);
lean_inc_ref(v_exprToNCSemiringId_546_);
lean_inc_ref(v_ncSemirings_545_);
lean_inc_ref(v_nctypeIdOf_544_);
lean_inc_ref(v_exprToNCRingId_543_);
lean_inc_ref(v_ncRings_542_);
lean_inc_ref(v_exprToSemiringId_541_);
lean_inc_ref(v_stypeIdOf_540_);
lean_inc_ref(v_semirings_539_);
lean_inc_ref(v_exprToRingId_538_);
lean_inc_ref(v_typeIdOf_537_);
lean_inc_ref(v_rings_536_);
v_isSharedCheck_575_ = !lean_is_exclusive(v_s_535_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; lean_object* v_unused_577_; lean_object* v_unused_578_; lean_object* v_unused_579_; lean_object* v_unused_580_; lean_object* v_unused_581_; lean_object* v_unused_582_; lean_object* v_unused_583_; lean_object* v_unused_584_; lean_object* v_unused_585_; lean_object* v_unused_586_; lean_object* v_unused_587_; lean_object* v_unused_588_; 
v_unused_576_ = lean_ctor_get(v_s_535_, 12);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_s_535_, 11);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_s_535_, 10);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_s_535_, 9);
lean_dec(v_unused_579_);
v_unused_580_ = lean_ctor_get(v_s_535_, 8);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_s_535_, 7);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_s_535_, 6);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_s_535_, 5);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_s_535_, 4);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_s_535_, 3);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_s_535_, 2);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_s_535_, 1);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_s_535_, 0);
lean_dec(v_unused_588_);
v___x_553_ = v_s_535_;
v_isShared_554_ = v_isSharedCheck_575_;
goto v_resetjp_552_;
}
else
{
lean_dec(v_s_535_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_575_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_v_555_; lean_object* v_toSemiring_556_; lean_object* v_ringId_557_; lean_object* v_commSemiringInst_558_; lean_object* v_addRightCancelInst_x3f_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_573_; 
v_v_555_ = lean_array_fget(v_semirings_539_, v_a_533_);
v_toSemiring_556_ = lean_ctor_get(v_v_555_, 0);
v_ringId_557_ = lean_ctor_get(v_v_555_, 1);
v_commSemiringInst_558_ = lean_ctor_get(v_v_555_, 2);
v_addRightCancelInst_x3f_559_ = lean_ctor_get(v_v_555_, 3);
v_isSharedCheck_573_ = !lean_is_exclusive(v_v_555_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_v_555_, 4);
lean_dec(v_unused_574_);
v___x_561_ = v_v_555_;
v_isShared_562_ = v_isSharedCheck_573_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_addRightCancelInst_x3f_559_);
lean_inc(v_commSemiringInst_558_);
lean_inc(v_ringId_557_);
lean_inc(v_toSemiring_556_);
lean_dec(v_v_555_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_573_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v_xs_x27_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_563_ = lean_box(0);
v_xs_x27_564_ = lean_array_fset(v_semirings_539_, v_a_533_, v___x_563_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v_a_534_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 4, v___x_565_);
v___x_567_ = v___x_561_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_toSemiring_556_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_ringId_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_commSemiringInst_558_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_addRightCancelInst_x3f_559_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v___x_565_);
v___x_567_ = v_reuseFailAlloc_572_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = lean_array_fset(v_xs_x27_564_, v_a_533_, v___x_567_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 3, v___x_568_);
v___x_570_ = v___x_553_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_rings_536_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_typeIdOf_537_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_exprToRingId_538_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v_stypeIdOf_540_);
lean_ctor_set(v_reuseFailAlloc_571_, 5, v_exprToSemiringId_541_);
lean_ctor_set(v_reuseFailAlloc_571_, 6, v_ncRings_542_);
lean_ctor_set(v_reuseFailAlloc_571_, 7, v_exprToNCRingId_543_);
lean_ctor_set(v_reuseFailAlloc_571_, 8, v_nctypeIdOf_544_);
lean_ctor_set(v_reuseFailAlloc_571_, 9, v_ncSemirings_545_);
lean_ctor_set(v_reuseFailAlloc_571_, 10, v_exprToNCSemiringId_546_);
lean_ctor_set(v_reuseFailAlloc_571_, 11, v_ncstypeIdOf_547_);
lean_ctor_set(v_reuseFailAlloc_571_, 12, v_steps_548_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, sizeof(void*)*13, v_reportedMaxDegreeIssue_549_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed(lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_s_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(v_a_589_, v_a_590_, v_s_591_);
lean_dec(v_a_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn(lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___y_617_; lean_object* v___x_638_; 
v___x_638_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_660_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_660_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_660_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_660_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_toQFn_x3f_643_; 
v_toQFn_x3f_643_ = lean_ctor_get(v_a_639_, 4);
if (lean_obj_tag(v_toQFn_x3f_643_) == 1)
{
lean_object* v_val_644_; lean_object* v___x_646_; 
lean_inc_ref(v_toQFn_x3f_643_);
lean_dec(v_a_639_);
v_val_644_ = lean_ctor_get(v_toQFn_x3f_643_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v_toQFn_x3f_643_, 1);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v_val_644_);
v___x_646_ = v___x_641_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_val_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
else
{
lean_object* v_toSemiring_648_; lean_object* v_type_649_; lean_object* v_u_650_; lean_object* v_semiringInst_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
lean_del_object(v___x_641_);
v_toSemiring_648_ = lean_ctor_get(v_a_639_, 0);
lean_inc_ref(v_toSemiring_648_);
lean_dec(v_a_639_);
v_type_649_ = lean_ctor_get(v_toSemiring_648_, 1);
lean_inc_ref(v_type_649_);
v_u_650_ = lean_ctor_get(v_toSemiring_648_, 2);
lean_inc(v_u_650_);
v_semiringInst_651_ = lean_ctor_get(v_toSemiring_648_, 3);
lean_inc_ref(v_semiringInst_651_);
lean_dec_ref(v_toSemiring_648_);
v___x_652_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5));
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_654_, 0, v_u_650_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_mkConst(v___x_652_, v___x_654_);
v___x_656_ = l_Lean_mkAppB(v___x_655_, v_type_649_, v_semiringInst_651_);
v___x_657_ = l_Lean_Meta_Sym_canon(v___x_656_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = l_Lean_Meta_Sym_shareCommon(v_a_658_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
v___y_617_ = v___x_659_;
goto v___jp_616_;
}
else
{
v___y_617_ = v___x_657_;
goto v___jp_616_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_a_661_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_638_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_638_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
v___jp_616_:
{
if (lean_obj_tag(v___y_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___f_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_a_618_ = lean_ctor_get(v___y_617_, 0);
lean_inc_n(v_a_618_, 2);
lean_dec_ref_known(v___y_617_, 1);
lean_inc(v_a_604_);
v___f_619_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed), 3, 2);
lean_closure_set(v___f_619_, 0, v_a_604_);
lean_closure_set(v___f_619_, 1, v_a_618_);
v___x_620_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_621_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_620_, v___f_619_, v_a_605_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v___x_621_, 0);
lean_dec(v_unused_629_);
v___x_623_ = v___x_621_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_dec(v___x_621_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_a_618_);
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_618_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v_a_618_);
v_a_630_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_621_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_621_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
return v___y_617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___boxed(lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec(v_a_670_);
lean_dec(v_a_669_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(lean_object* v_u_690_, lean_object* v_type_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v_add_702_; lean_object* v___x_703_; 
v___x_698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1));
v___x_699_ = lean_box(0);
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v_u_690_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
lean_inc_ref(v___x_700_);
v___x_701_ = l_Lean_mkConst(v___x_698_, v___x_700_);
lean_inc_ref(v_type_691_);
v_add_702_ = l_Lean_Expr_app___override(v___x_701_, v_type_691_);
v___x_703_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_add_702_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_717_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_717_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_717_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_717_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
if (lean_obj_tag(v_a_704_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_del_object(v___x_706_);
v_val_708_ = lean_ctor_get(v_a_704_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v_a_704_, 1);
v___x_709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3));
v___x_710_ = l_Lean_mkConst(v___x_709_, v___x_700_);
v___x_711_ = l_Lean_mkAppB(v___x_710_, v_type_691_, v_val_708_);
v___x_712_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_711_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_715_; 
lean_dec(v_a_704_);
lean_dec_ref_known(v___x_700_, 2);
lean_dec_ref(v_type_691_);
v___x_713_ = lean_box(0);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_713_);
v___x_715_ = v___x_706_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_700_, 2);
lean_dec_ref(v_type_691_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___boxed(lean_object* v_u_718_, lean_object* v_type_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_718_, v_type_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(lean_object* v_u_727_, lean_object* v_type_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_727_, v_type_728_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___boxed(lean_object* v_u_741_, lean_object* v_type_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(v_u_741_, v_type_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec(v_a_743_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_s_757_){
_start:
{
lean_object* v_rings_758_; lean_object* v_typeIdOf_759_; lean_object* v_exprToRingId_760_; lean_object* v_semirings_761_; lean_object* v_stypeIdOf_762_; lean_object* v_exprToSemiringId_763_; lean_object* v_ncRings_764_; lean_object* v_exprToNCRingId_765_; lean_object* v_nctypeIdOf_766_; lean_object* v_ncSemirings_767_; lean_object* v_exprToNCSemiringId_768_; lean_object* v_ncstypeIdOf_769_; lean_object* v_steps_770_; uint8_t v_reportedMaxDegreeIssue_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_rings_758_ = lean_ctor_get(v_s_757_, 0);
v_typeIdOf_759_ = lean_ctor_get(v_s_757_, 1);
v_exprToRingId_760_ = lean_ctor_get(v_s_757_, 2);
v_semirings_761_ = lean_ctor_get(v_s_757_, 3);
v_stypeIdOf_762_ = lean_ctor_get(v_s_757_, 4);
v_exprToSemiringId_763_ = lean_ctor_get(v_s_757_, 5);
v_ncRings_764_ = lean_ctor_get(v_s_757_, 6);
v_exprToNCRingId_765_ = lean_ctor_get(v_s_757_, 7);
v_nctypeIdOf_766_ = lean_ctor_get(v_s_757_, 8);
v_ncSemirings_767_ = lean_ctor_get(v_s_757_, 9);
v_exprToNCSemiringId_768_ = lean_ctor_get(v_s_757_, 10);
v_ncstypeIdOf_769_ = lean_ctor_get(v_s_757_, 11);
v_steps_770_ = lean_ctor_get(v_s_757_, 12);
v_reportedMaxDegreeIssue_771_ = lean_ctor_get_uint8(v_s_757_, sizeof(void*)*13);
v___x_772_ = lean_array_get_size(v_semirings_761_);
v___x_773_ = lean_nat_dec_lt(v_a_755_, v___x_772_);
if (v___x_773_ == 0)
{
lean_dec(v_a_756_);
return v_s_757_;
}
else
{
lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_797_; 
lean_inc(v_steps_770_);
lean_inc_ref(v_ncstypeIdOf_769_);
lean_inc_ref(v_exprToNCSemiringId_768_);
lean_inc_ref(v_ncSemirings_767_);
lean_inc_ref(v_nctypeIdOf_766_);
lean_inc_ref(v_exprToNCRingId_765_);
lean_inc_ref(v_ncRings_764_);
lean_inc_ref(v_exprToSemiringId_763_);
lean_inc_ref(v_stypeIdOf_762_);
lean_inc_ref(v_semirings_761_);
lean_inc_ref(v_exprToRingId_760_);
lean_inc_ref(v_typeIdOf_759_);
lean_inc_ref(v_rings_758_);
v_isSharedCheck_797_ = !lean_is_exclusive(v_s_757_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; lean_object* v_unused_799_; lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; lean_object* v_unused_804_; lean_object* v_unused_805_; lean_object* v_unused_806_; lean_object* v_unused_807_; lean_object* v_unused_808_; lean_object* v_unused_809_; lean_object* v_unused_810_; 
v_unused_798_ = lean_ctor_get(v_s_757_, 12);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_s_757_, 11);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_s_757_, 10);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_s_757_, 9);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_s_757_, 8);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_s_757_, 7);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_s_757_, 6);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_s_757_, 5);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_s_757_, 4);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_s_757_, 3);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_s_757_, 2);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_s_757_, 1);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_s_757_, 0);
lean_dec(v_unused_810_);
v___x_775_ = v_s_757_;
v_isShared_776_ = v_isSharedCheck_797_;
goto v_resetjp_774_;
}
else
{
lean_dec(v_s_757_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_797_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_v_777_; lean_object* v_toSemiring_778_; lean_object* v_ringId_779_; lean_object* v_commSemiringInst_780_; lean_object* v_toQFn_x3f_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_795_; 
v_v_777_ = lean_array_fget(v_semirings_761_, v_a_755_);
v_toSemiring_778_ = lean_ctor_get(v_v_777_, 0);
v_ringId_779_ = lean_ctor_get(v_v_777_, 1);
v_commSemiringInst_780_ = lean_ctor_get(v_v_777_, 2);
v_toQFn_x3f_781_ = lean_ctor_get(v_v_777_, 4);
v_isSharedCheck_795_ = !lean_is_exclusive(v_v_777_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_v_777_, 3);
lean_dec(v_unused_796_);
v___x_783_ = v_v_777_;
v_isShared_784_ = v_isSharedCheck_795_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_toQFn_x3f_781_);
lean_inc(v_commSemiringInst_780_);
lean_inc(v_ringId_779_);
lean_inc(v_toSemiring_778_);
lean_dec(v_v_777_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_795_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v_xs_x27_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_785_ = lean_box(0);
v_xs_x27_786_ = lean_array_fset(v_semirings_761_, v_a_755_, v___x_785_);
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v_a_756_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 3, v___x_787_);
v___x_789_ = v___x_783_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_toSemiring_778_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_ringId_779_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_commSemiringInst_780_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_toQFn_x3f_781_);
v___x_789_ = v_reuseFailAlloc_794_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = lean_array_fset(v_xs_x27_786_, v_a_755_, v___x_789_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 3, v___x_790_);
v___x_792_ = v___x_775_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_rings_758_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_typeIdOf_759_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_exprToRingId_760_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v_stypeIdOf_762_);
lean_ctor_set(v_reuseFailAlloc_793_, 5, v_exprToSemiringId_763_);
lean_ctor_set(v_reuseFailAlloc_793_, 6, v_ncRings_764_);
lean_ctor_set(v_reuseFailAlloc_793_, 7, v_exprToNCRingId_765_);
lean_ctor_set(v_reuseFailAlloc_793_, 8, v_nctypeIdOf_766_);
lean_ctor_set(v_reuseFailAlloc_793_, 9, v_ncSemirings_767_);
lean_ctor_set(v_reuseFailAlloc_793_, 10, v_exprToNCSemiringId_768_);
lean_ctor_set(v_reuseFailAlloc_793_, 11, v_ncstypeIdOf_769_);
lean_ctor_set(v_reuseFailAlloc_793_, 12, v_steps_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_793_, sizeof(void*)*13, v_reportedMaxDegreeIssue_771_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed(lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_s_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(v_a_811_, v_a_812_, v_s_813_);
lean_dec(v_a_811_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_861_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_861_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_861_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_861_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_addRightCancelInst_x3f_832_; 
v_addRightCancelInst_x3f_832_ = lean_ctor_get(v_a_828_, 3);
if (lean_obj_tag(v_addRightCancelInst_x3f_832_) == 1)
{
lean_object* v_val_833_; lean_object* v___x_835_; 
lean_inc_ref(v_addRightCancelInst_x3f_832_);
lean_dec(v_a_828_);
v_val_833_ = lean_ctor_get(v_addRightCancelInst_x3f_832_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v_addRightCancelInst_x3f_832_, 1);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v_val_833_);
v___x_835_ = v___x_830_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_val_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
lean_object* v_toSemiring_837_; lean_object* v_type_838_; lean_object* v_u_839_; lean_object* v___x_840_; 
lean_del_object(v___x_830_);
v_toSemiring_837_ = lean_ctor_get(v_a_828_, 0);
lean_inc_ref(v_toSemiring_837_);
lean_dec(v_a_828_);
v_type_838_ = lean_ctor_get(v_toSemiring_837_, 1);
lean_inc_ref(v_type_838_);
v_u_839_ = lean_ctor_get(v_toSemiring_837_, 2);
lean_inc(v_u_839_);
lean_dec_ref(v_toSemiring_837_);
v___x_840_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_839_, v_type_838_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___f_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc_n(v_a_841_, 2);
lean_dec_ref_known(v___x_840_, 1);
lean_inc(v_a_815_);
v___f_842_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_842_, 0, v_a_815_);
lean_closure_set(v___f_842_, 1, v_a_841_);
v___x_843_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_844_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_843_, v___f_842_, v_a_816_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v___x_844_, 0);
lean_dec(v_unused_852_);
v___x_846_ = v___x_844_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_dec(v___x_844_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v_a_841_);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_841_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec(v_a_841_);
v_a_853_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_844_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_844_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
else
{
return v___x_840_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v_a_862_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_827_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_827_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___boxed(lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec(v_a_871_);
lean_dec(v_a_870_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_883_, lean_object* v_s_884_){
_start:
{
lean_object* v_id_885_; lean_object* v_type_886_; lean_object* v_u_887_; lean_object* v_semiringInst_888_; lean_object* v_mulFn_x3f_889_; lean_object* v_powFn_x3f_890_; lean_object* v_natCastFn_x3f_891_; lean_object* v_denote_892_; lean_object* v_vars_893_; lean_object* v_varMap_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_902_; 
v_id_885_ = lean_ctor_get(v_s_884_, 0);
v_type_886_ = lean_ctor_get(v_s_884_, 1);
v_u_887_ = lean_ctor_get(v_s_884_, 2);
v_semiringInst_888_ = lean_ctor_get(v_s_884_, 3);
v_mulFn_x3f_889_ = lean_ctor_get(v_s_884_, 5);
v_powFn_x3f_890_ = lean_ctor_get(v_s_884_, 6);
v_natCastFn_x3f_891_ = lean_ctor_get(v_s_884_, 7);
v_denote_892_ = lean_ctor_get(v_s_884_, 8);
v_vars_893_ = lean_ctor_get(v_s_884_, 9);
v_varMap_894_ = lean_ctor_get(v_s_884_, 10);
v_isSharedCheck_902_ = !lean_is_exclusive(v_s_884_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v_s_884_, 4);
lean_dec(v_unused_903_);
v___x_896_ = v_s_884_;
v_isShared_897_ = v_isSharedCheck_902_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_varMap_894_);
lean_inc(v_vars_893_);
lean_inc(v_denote_892_);
lean_inc(v_natCastFn_x3f_891_);
lean_inc(v_powFn_x3f_890_);
lean_inc(v_mulFn_x3f_889_);
lean_inc(v_semiringInst_888_);
lean_inc(v_u_887_);
lean_inc(v_type_886_);
lean_inc(v_id_885_);
lean_dec(v_s_884_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_902_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v_addFn_883_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 4, v___x_898_);
v___x_900_ = v___x_896_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_id_885_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_type_886_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_u_887_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v_semiringInst_888_);
lean_ctor_set(v_reuseFailAlloc_901_, 4, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_901_, 5, v_mulFn_x3f_889_);
lean_ctor_set(v_reuseFailAlloc_901_, 6, v_powFn_x3f_890_);
lean_ctor_set(v_reuseFailAlloc_901_, 7, v_natCastFn_x3f_891_);
lean_ctor_set(v_reuseFailAlloc_901_, 8, v_denote_892_);
lean_ctor_set(v_reuseFailAlloc_901_, 9, v_vars_893_);
lean_ctor_set(v_reuseFailAlloc_901_, 10, v_varMap_894_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_904_, lean_object* v_addFn_905_, lean_object* v_____r_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = lean_apply_2(v_toPure_904_, lean_box(0), v_addFn_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_908_, lean_object* v_modifySemiring_909_, lean_object* v_toBind_910_, lean_object* v_addFn_911_){
_start:
{
lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_inc_ref(v_addFn_911_);
v___f_912_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_912_, 0, v_addFn_911_);
v___f_913_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_913_, 0, v_toPure_908_);
lean_closure_set(v___f_913_, 1, v_addFn_911_);
v___x_914_ = lean_apply_1(v_modifySemiring_909_, v___f_912_);
v___x_915_ = lean_apply_4(v_toBind_910_, lean_box(0), lean_box(0), v___x_914_, v___f_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3(lean_object* v_toPure_933_, lean_object* v_inst_934_, lean_object* v_inst_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_toBind_938_, lean_object* v___f_939_, lean_object* v_s_940_){
_start:
{
lean_object* v_addFn_x3f_941_; 
v_addFn_x3f_941_ = lean_ctor_get(v_s_940_, 4);
if (lean_obj_tag(v_addFn_x3f_941_) == 1)
{
lean_object* v_val_942_; lean_object* v___x_943_; 
lean_inc_ref(v_addFn_x3f_941_);
lean_dec_ref(v_s_940_);
lean_dec(v___f_939_);
lean_dec(v_toBind_938_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
lean_dec_ref(v_inst_935_);
lean_dec(v_inst_934_);
v_val_942_ = lean_ctor_get(v_addFn_x3f_941_, 0);
lean_inc(v_val_942_);
lean_dec_ref_known(v_addFn_x3f_941_, 1);
v___x_943_ = lean_apply_2(v_toPure_933_, lean_box(0), v_val_942_);
return v___x_943_;
}
else
{
lean_object* v_type_944_; lean_object* v_u_945_; lean_object* v_semiringInst_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_expectedInst_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_toPure_933_);
v_type_944_ = lean_ctor_get(v_s_940_, 1);
lean_inc_ref_n(v_type_944_, 3);
v_u_945_ = lean_ctor_get(v_s_940_, 2);
lean_inc_n(v_u_945_, 2);
v_semiringInst_946_ = lean_ctor_get(v_s_940_, 3);
lean_inc_ref(v_semiringInst_946_);
lean_dec_ref(v_s_940_);
v___x_947_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_948_ = lean_box(0);
v___x_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_949_, 0, v_u_945_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
lean_inc_ref(v___x_949_);
v___x_950_ = l_Lean_mkConst(v___x_947_, v___x_949_);
v___x_951_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_952_ = l_Lean_mkConst(v___x_951_, v___x_949_);
v___x_953_ = l_Lean_mkAppB(v___x_952_, v_type_944_, v_semiringInst_946_);
v_expectedInst_954_ = l_Lean_mkAppB(v___x_950_, v_type_944_, v___x_953_);
v___x_955_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_956_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_957_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_934_, v_inst_935_, v_inst_936_, v_inst_937_, v_type_944_, v_u_945_, v___x_955_, v___x_956_, v_expectedInst_954_);
v___x_958_ = lean_apply_4(v_toBind_938_, lean_box(0), lean_box(0), v___x_957_, v___f_939_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_inst_963_){
_start:
{
lean_object* v_toApplicative_964_; lean_object* v_toBind_965_; lean_object* v_getSemiring_966_; lean_object* v_modifySemiring_967_; lean_object* v_toPure_968_; lean_object* v___f_969_; lean_object* v___f_970_; lean_object* v___x_971_; 
v_toApplicative_964_ = lean_ctor_get(v_inst_961_, 0);
v_toBind_965_ = lean_ctor_get(v_inst_961_, 1);
lean_inc_n(v_toBind_965_, 3);
v_getSemiring_966_ = lean_ctor_get(v_inst_963_, 0);
lean_inc(v_getSemiring_966_);
v_modifySemiring_967_ = lean_ctor_get(v_inst_963_, 1);
lean_inc(v_modifySemiring_967_);
lean_dec_ref(v_inst_963_);
v_toPure_968_ = lean_ctor_get(v_toApplicative_964_, 1);
lean_inc_n(v_toPure_968_, 2);
v___f_969_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_969_, 0, v_toPure_968_);
lean_closure_set(v___f_969_, 1, v_modifySemiring_967_);
lean_closure_set(v___f_969_, 2, v_toBind_965_);
v___f_970_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_970_, 0, v_toPure_968_);
lean_closure_set(v___f_970_, 1, v_inst_959_);
lean_closure_set(v___f_970_, 2, v_inst_960_);
lean_closure_set(v___f_970_, 3, v_inst_961_);
lean_closure_set(v___f_970_, 4, v_inst_962_);
lean_closure_set(v___f_970_, 5, v_toBind_965_);
lean_closure_set(v___f_970_, 6, v___f_969_);
v___x_971_ = lean_apply_4(v_toBind_965_, lean_box(0), lean_box(0), v_getSemiring_966_, v___f_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27(lean_object* v_m_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_inst_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(v_inst_973_, v_inst_974_, v_inst_975_, v_inst_976_, v_inst_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_979_, lean_object* v_s_980_){
_start:
{
lean_object* v_id_981_; lean_object* v_type_982_; lean_object* v_u_983_; lean_object* v_semiringInst_984_; lean_object* v_addFn_x3f_985_; lean_object* v_powFn_x3f_986_; lean_object* v_natCastFn_x3f_987_; lean_object* v_denote_988_; lean_object* v_vars_989_; lean_object* v_varMap_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_998_; 
v_id_981_ = lean_ctor_get(v_s_980_, 0);
v_type_982_ = lean_ctor_get(v_s_980_, 1);
v_u_983_ = lean_ctor_get(v_s_980_, 2);
v_semiringInst_984_ = lean_ctor_get(v_s_980_, 3);
v_addFn_x3f_985_ = lean_ctor_get(v_s_980_, 4);
v_powFn_x3f_986_ = lean_ctor_get(v_s_980_, 6);
v_natCastFn_x3f_987_ = lean_ctor_get(v_s_980_, 7);
v_denote_988_ = lean_ctor_get(v_s_980_, 8);
v_vars_989_ = lean_ctor_get(v_s_980_, 9);
v_varMap_990_ = lean_ctor_get(v_s_980_, 10);
v_isSharedCheck_998_ = !lean_is_exclusive(v_s_980_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v_s_980_, 5);
lean_dec(v_unused_999_);
v___x_992_ = v_s_980_;
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_varMap_990_);
lean_inc(v_vars_989_);
lean_inc(v_denote_988_);
lean_inc(v_natCastFn_x3f_987_);
lean_inc(v_powFn_x3f_986_);
lean_inc(v_addFn_x3f_985_);
lean_inc(v_semiringInst_984_);
lean_inc(v_u_983_);
lean_inc(v_type_982_);
lean_inc(v_id_981_);
lean_dec(v_s_980_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v_mulFn_979_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 5, v___x_994_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_id_981_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_type_982_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_u_983_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_semiringInst_984_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v_addFn_x3f_985_);
lean_ctor_set(v_reuseFailAlloc_997_, 5, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_997_, 6, v_powFn_x3f_986_);
lean_ctor_set(v_reuseFailAlloc_997_, 7, v_natCastFn_x3f_987_);
lean_ctor_set(v_reuseFailAlloc_997_, 8, v_denote_988_);
lean_ctor_set(v_reuseFailAlloc_997_, 9, v_vars_989_);
lean_ctor_set(v_reuseFailAlloc_997_, 10, v_varMap_990_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_1000_, lean_object* v_mulFn_1001_, lean_object* v_____r_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_apply_2(v_toPure_1000_, lean_box(0), v_mulFn_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_1004_, lean_object* v_modifySemiring_1005_, lean_object* v_toBind_1006_, lean_object* v_mulFn_1007_){
_start:
{
lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_inc_ref(v_mulFn_1007_);
v___f_1008_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1008_, 0, v_mulFn_1007_);
v___f_1009_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1009_, 0, v_toPure_1004_);
lean_closure_set(v___f_1009_, 1, v_mulFn_1007_);
v___x_1010_ = lean_apply_1(v_modifySemiring_1005_, v___f_1008_);
v___x_1011_ = lean_apply_4(v_toBind_1006_, lean_box(0), lean_box(0), v___x_1010_, v___f_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3(lean_object* v_toPure_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_toBind_1033_, lean_object* v___f_1034_, lean_object* v_s_1035_){
_start:
{
lean_object* v_mulFn_x3f_1036_; 
v_mulFn_x3f_1036_ = lean_ctor_get(v_s_1035_, 5);
if (lean_obj_tag(v_mulFn_x3f_1036_) == 1)
{
lean_object* v_val_1037_; lean_object* v___x_1038_; 
lean_inc_ref(v_mulFn_x3f_1036_);
lean_dec_ref(v_s_1035_);
lean_dec(v___f_1034_);
lean_dec(v_toBind_1033_);
lean_dec_ref(v_inst_1032_);
lean_dec_ref(v_inst_1031_);
lean_dec_ref(v_inst_1030_);
lean_dec(v_inst_1029_);
v_val_1037_ = lean_ctor_get(v_mulFn_x3f_1036_, 0);
lean_inc(v_val_1037_);
lean_dec_ref_known(v_mulFn_x3f_1036_, 1);
v___x_1038_ = lean_apply_2(v_toPure_1028_, lean_box(0), v_val_1037_);
return v___x_1038_;
}
else
{
lean_object* v_type_1039_; lean_object* v_u_1040_; lean_object* v_semiringInst_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v_expectedInst_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec(v_toPure_1028_);
v_type_1039_ = lean_ctor_get(v_s_1035_, 1);
lean_inc_ref_n(v_type_1039_, 3);
v_u_1040_ = lean_ctor_get(v_s_1035_, 2);
lean_inc_n(v_u_1040_, 2);
v_semiringInst_1041_ = lean_ctor_get(v_s_1035_, 3);
lean_inc_ref(v_semiringInst_1041_);
lean_dec_ref(v_s_1035_);
v___x_1042_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1044_, 0, v_u_1040_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
lean_inc_ref(v___x_1044_);
v___x_1045_ = l_Lean_mkConst(v___x_1042_, v___x_1044_);
v___x_1046_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_1047_ = l_Lean_mkConst(v___x_1046_, v___x_1044_);
v___x_1048_ = l_Lean_mkAppB(v___x_1047_, v_type_1039_, v_semiringInst_1041_);
v_expectedInst_1049_ = l_Lean_mkAppB(v___x_1045_, v_type_1039_, v___x_1048_);
v___x_1050_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_1051_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_1052_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_1029_, v_inst_1030_, v_inst_1031_, v_inst_1032_, v_type_1039_, v_u_1040_, v___x_1050_, v___x_1051_, v_expectedInst_1049_);
v___x_1053_ = lean_apply_4(v_toBind_1033_, lean_box(0), lean_box(0), v___x_1052_, v___f_1034_);
return v___x_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_){
_start:
{
lean_object* v_toApplicative_1059_; lean_object* v_toBind_1060_; lean_object* v_getSemiring_1061_; lean_object* v_modifySemiring_1062_; lean_object* v_toPure_1063_; lean_object* v___f_1064_; lean_object* v___f_1065_; lean_object* v___x_1066_; 
v_toApplicative_1059_ = lean_ctor_get(v_inst_1056_, 0);
v_toBind_1060_ = lean_ctor_get(v_inst_1056_, 1);
lean_inc_n(v_toBind_1060_, 3);
v_getSemiring_1061_ = lean_ctor_get(v_inst_1058_, 0);
lean_inc(v_getSemiring_1061_);
v_modifySemiring_1062_ = lean_ctor_get(v_inst_1058_, 1);
lean_inc(v_modifySemiring_1062_);
lean_dec_ref(v_inst_1058_);
v_toPure_1063_ = lean_ctor_get(v_toApplicative_1059_, 1);
lean_inc_n(v_toPure_1063_, 2);
v___f_1064_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1064_, 0, v_toPure_1063_);
lean_closure_set(v___f_1064_, 1, v_modifySemiring_1062_);
lean_closure_set(v___f_1064_, 2, v_toBind_1060_);
v___f_1065_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1065_, 0, v_toPure_1063_);
lean_closure_set(v___f_1065_, 1, v_inst_1054_);
lean_closure_set(v___f_1065_, 2, v_inst_1055_);
lean_closure_set(v___f_1065_, 3, v_inst_1056_);
lean_closure_set(v___f_1065_, 4, v_inst_1057_);
lean_closure_set(v___f_1065_, 5, v_toBind_1060_);
lean_closure_set(v___f_1065_, 6, v___f_1064_);
v___x_1066_ = lean_apply_4(v_toBind_1060_, lean_box(0), lean_box(0), v_getSemiring_1061_, v___f_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27(lean_object* v_m_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(v_inst_1068_, v_inst_1069_, v_inst_1070_, v_inst_1071_, v_inst_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1074_, lean_object* v_s_1075_){
_start:
{
lean_object* v_id_1076_; lean_object* v_type_1077_; lean_object* v_u_1078_; lean_object* v_semiringInst_1079_; lean_object* v_addFn_x3f_1080_; lean_object* v_mulFn_x3f_1081_; lean_object* v_natCastFn_x3f_1082_; lean_object* v_denote_1083_; lean_object* v_vars_1084_; lean_object* v_varMap_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1093_; 
v_id_1076_ = lean_ctor_get(v_s_1075_, 0);
v_type_1077_ = lean_ctor_get(v_s_1075_, 1);
v_u_1078_ = lean_ctor_get(v_s_1075_, 2);
v_semiringInst_1079_ = lean_ctor_get(v_s_1075_, 3);
v_addFn_x3f_1080_ = lean_ctor_get(v_s_1075_, 4);
v_mulFn_x3f_1081_ = lean_ctor_get(v_s_1075_, 5);
v_natCastFn_x3f_1082_ = lean_ctor_get(v_s_1075_, 7);
v_denote_1083_ = lean_ctor_get(v_s_1075_, 8);
v_vars_1084_ = lean_ctor_get(v_s_1075_, 9);
v_varMap_1085_ = lean_ctor_get(v_s_1075_, 10);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_s_1075_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v_s_1075_, 6);
lean_dec(v_unused_1094_);
v___x_1087_ = v_s_1075_;
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_varMap_1085_);
lean_inc(v_vars_1084_);
lean_inc(v_denote_1083_);
lean_inc(v_natCastFn_x3f_1082_);
lean_inc(v_mulFn_x3f_1081_);
lean_inc(v_addFn_x3f_1080_);
lean_inc(v_semiringInst_1079_);
lean_inc(v_u_1078_);
lean_inc(v_type_1077_);
lean_inc(v_id_1076_);
lean_dec(v_s_1075_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v_powFn_1074_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 6, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_id_1076_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_type_1077_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_u_1078_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_semiringInst_1079_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v_addFn_x3f_1080_);
lean_ctor_set(v_reuseFailAlloc_1092_, 5, v_mulFn_x3f_1081_);
lean_ctor_set(v_reuseFailAlloc_1092_, 6, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1092_, 7, v_natCastFn_x3f_1082_);
lean_ctor_set(v_reuseFailAlloc_1092_, 8, v_denote_1083_);
lean_ctor_set(v_reuseFailAlloc_1092_, 9, v_vars_1084_);
lean_ctor_set(v_reuseFailAlloc_1092_, 10, v_varMap_1085_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1095_, lean_object* v_powFn_1096_, lean_object* v_____r_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_apply_2(v_toPure_1095_, lean_box(0), v_powFn_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1099_, lean_object* v_modifySemiring_1100_, lean_object* v_toBind_1101_, lean_object* v_powFn_1102_){
_start:
{
lean_object* v___f_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_inc_ref(v_powFn_1102_);
v___f_1103_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1103_, 0, v_powFn_1102_);
v___f_1104_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1104_, 0, v_toPure_1099_);
lean_closure_set(v___f_1104_, 1, v_powFn_1102_);
v___x_1105_ = lean_apply_1(v_modifySemiring_1100_, v___f_1103_);
v___x_1106_ = lean_apply_4(v_toBind_1101_, lean_box(0), lean_box(0), v___x_1105_, v___f_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3(lean_object* v_toPure_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_inst_1111_, lean_object* v_toBind_1112_, lean_object* v___f_1113_, lean_object* v_s_1114_){
_start:
{
lean_object* v_powFn_x3f_1115_; 
v_powFn_x3f_1115_ = lean_ctor_get(v_s_1114_, 6);
if (lean_obj_tag(v_powFn_x3f_1115_) == 1)
{
lean_object* v_val_1116_; lean_object* v___x_1117_; 
lean_inc_ref(v_powFn_x3f_1115_);
lean_dec_ref(v_s_1114_);
lean_dec(v___f_1113_);
lean_dec(v_toBind_1112_);
lean_dec_ref(v_inst_1111_);
lean_dec_ref(v_inst_1110_);
lean_dec_ref(v_inst_1109_);
lean_dec(v_inst_1108_);
v_val_1116_ = lean_ctor_get(v_powFn_x3f_1115_, 0);
lean_inc(v_val_1116_);
lean_dec_ref_known(v_powFn_x3f_1115_, 1);
v___x_1117_ = lean_apply_2(v_toPure_1107_, lean_box(0), v_val_1116_);
return v___x_1117_;
}
else
{
lean_object* v_type_1118_; lean_object* v_u_1119_; lean_object* v_semiringInst_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec(v_toPure_1107_);
v_type_1118_ = lean_ctor_get(v_s_1114_, 1);
lean_inc_ref(v_type_1118_);
v_u_1119_ = lean_ctor_get(v_s_1114_, 2);
lean_inc(v_u_1119_);
v_semiringInst_1120_ = lean_ctor_get(v_s_1114_, 3);
lean_inc_ref(v_semiringInst_1120_);
lean_dec_ref(v_s_1114_);
v___x_1121_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(v_inst_1108_, v_inst_1109_, v_inst_1110_, v_inst_1111_, v_u_1119_, v_type_1118_, v_semiringInst_1120_);
v___x_1122_ = lean_apply_4(v_toBind_1112_, lean_box(0), lean_box(0), v___x_1121_, v___f_1113_);
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_){
_start:
{
lean_object* v_toApplicative_1128_; lean_object* v_toBind_1129_; lean_object* v_getSemiring_1130_; lean_object* v_modifySemiring_1131_; lean_object* v_toPure_1132_; lean_object* v___f_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; 
v_toApplicative_1128_ = lean_ctor_get(v_inst_1125_, 0);
v_toBind_1129_ = lean_ctor_get(v_inst_1125_, 1);
lean_inc_n(v_toBind_1129_, 3);
v_getSemiring_1130_ = lean_ctor_get(v_inst_1127_, 0);
lean_inc(v_getSemiring_1130_);
v_modifySemiring_1131_ = lean_ctor_get(v_inst_1127_, 1);
lean_inc(v_modifySemiring_1131_);
lean_dec_ref(v_inst_1127_);
v_toPure_1132_ = lean_ctor_get(v_toApplicative_1128_, 1);
lean_inc_n(v_toPure_1132_, 2);
v___f_1133_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1133_, 0, v_toPure_1132_);
lean_closure_set(v___f_1133_, 1, v_modifySemiring_1131_);
lean_closure_set(v___f_1133_, 2, v_toBind_1129_);
v___f_1134_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1134_, 0, v_toPure_1132_);
lean_closure_set(v___f_1134_, 1, v_inst_1123_);
lean_closure_set(v___f_1134_, 2, v_inst_1124_);
lean_closure_set(v___f_1134_, 3, v_inst_1125_);
lean_closure_set(v___f_1134_, 4, v_inst_1126_);
lean_closure_set(v___f_1134_, 5, v_toBind_1129_);
lean_closure_set(v___f_1134_, 6, v___f_1133_);
v___x_1135_ = lean_apply_4(v_toBind_1129_, lean_box(0), lean_box(0), v_getSemiring_1130_, v___f_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27(lean_object* v_m_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(v_inst_1137_, v_inst_1138_, v_inst_1139_, v_inst_1140_, v_inst_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1143_, lean_object* v_s_1144_){
_start:
{
lean_object* v_id_1145_; lean_object* v_type_1146_; lean_object* v_u_1147_; lean_object* v_semiringInst_1148_; lean_object* v_addFn_x3f_1149_; lean_object* v_mulFn_x3f_1150_; lean_object* v_powFn_x3f_1151_; lean_object* v_denote_1152_; lean_object* v_vars_1153_; lean_object* v_varMap_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1162_; 
v_id_1145_ = lean_ctor_get(v_s_1144_, 0);
v_type_1146_ = lean_ctor_get(v_s_1144_, 1);
v_u_1147_ = lean_ctor_get(v_s_1144_, 2);
v_semiringInst_1148_ = lean_ctor_get(v_s_1144_, 3);
v_addFn_x3f_1149_ = lean_ctor_get(v_s_1144_, 4);
v_mulFn_x3f_1150_ = lean_ctor_get(v_s_1144_, 5);
v_powFn_x3f_1151_ = lean_ctor_get(v_s_1144_, 6);
v_denote_1152_ = lean_ctor_get(v_s_1144_, 8);
v_vars_1153_ = lean_ctor_get(v_s_1144_, 9);
v_varMap_1154_ = lean_ctor_get(v_s_1144_, 10);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_s_1144_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; 
v_unused_1163_ = lean_ctor_get(v_s_1144_, 7);
lean_dec(v_unused_1163_);
v___x_1156_ = v_s_1144_;
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_varMap_1154_);
lean_inc(v_vars_1153_);
lean_inc(v_denote_1152_);
lean_inc(v_powFn_x3f_1151_);
lean_inc(v_mulFn_x3f_1150_);
lean_inc(v_addFn_x3f_1149_);
lean_inc(v_semiringInst_1148_);
lean_inc(v_u_1147_);
lean_inc(v_type_1146_);
lean_inc(v_id_1145_);
lean_dec(v_s_1144_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_natCastFn_1143_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 7, v___x_1158_);
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_id_1145_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_type_1146_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_u_1147_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_semiringInst_1148_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_addFn_x3f_1149_);
lean_ctor_set(v_reuseFailAlloc_1161_, 5, v_mulFn_x3f_1150_);
lean_ctor_set(v_reuseFailAlloc_1161_, 6, v_powFn_x3f_1151_);
lean_ctor_set(v_reuseFailAlloc_1161_, 7, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1161_, 8, v_denote_1152_);
lean_ctor_set(v_reuseFailAlloc_1161_, 9, v_vars_1153_);
lean_ctor_set(v_reuseFailAlloc_1161_, 10, v_varMap_1154_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1164_, lean_object* v_natCastFn_1165_, lean_object* v_____r_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_apply_2(v_toPure_1164_, lean_box(0), v_natCastFn_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1168_, lean_object* v_modifySemiring_1169_, lean_object* v_toBind_1170_, lean_object* v_natCastFn_1171_){
_start:
{
lean_object* v___f_1172_; lean_object* v___f_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_inc_ref(v_natCastFn_1171_);
v___f_1172_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1172_, 0, v_natCastFn_1171_);
v___f_1173_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1173_, 0, v_toPure_1168_);
lean_closure_set(v___f_1173_, 1, v_natCastFn_1171_);
v___x_1174_ = lean_apply_1(v_modifySemiring_1169_, v___f_1172_);
v___x_1175_ = lean_apply_4(v_toBind_1170_, lean_box(0), lean_box(0), v___x_1174_, v___f_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3(lean_object* v_toPure_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_toBind_1180_, lean_object* v___f_1181_, lean_object* v_s_1182_){
_start:
{
lean_object* v_natCastFn_x3f_1183_; 
v_natCastFn_x3f_1183_ = lean_ctor_get(v_s_1182_, 7);
if (lean_obj_tag(v_natCastFn_x3f_1183_) == 1)
{
lean_object* v_val_1184_; lean_object* v___x_1185_; 
lean_inc_ref(v_natCastFn_x3f_1183_);
lean_dec_ref(v_s_1182_);
lean_dec(v___f_1181_);
lean_dec(v_toBind_1180_);
lean_dec_ref(v_inst_1179_);
lean_dec_ref(v_inst_1178_);
lean_dec(v_inst_1177_);
v_val_1184_ = lean_ctor_get(v_natCastFn_x3f_1183_, 0);
lean_inc(v_val_1184_);
lean_dec_ref_known(v_natCastFn_x3f_1183_, 1);
v___x_1185_ = lean_apply_2(v_toPure_1176_, lean_box(0), v_val_1184_);
return v___x_1185_;
}
else
{
lean_object* v_type_1186_; lean_object* v_u_1187_; lean_object* v_semiringInst_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec(v_toPure_1176_);
v_type_1186_ = lean_ctor_get(v_s_1182_, 1);
lean_inc_ref(v_type_1186_);
v_u_1187_ = lean_ctor_get(v_s_1182_, 2);
lean_inc(v_u_1187_);
v_semiringInst_1188_ = lean_ctor_get(v_s_1182_, 3);
lean_inc_ref(v_semiringInst_1188_);
lean_dec_ref(v_s_1182_);
v___x_1189_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(v_inst_1177_, v_inst_1178_, v_inst_1179_, v_u_1187_, v_type_1186_, v_semiringInst_1188_);
v___x_1190_ = lean_apply_4(v_toBind_1180_, lean_box(0), lean_box(0), v___x_1189_, v___f_1181_);
return v___x_1190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_){
_start:
{
lean_object* v_toApplicative_1195_; lean_object* v_toBind_1196_; lean_object* v_getSemiring_1197_; lean_object* v_modifySemiring_1198_; lean_object* v_toPure_1199_; lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; 
v_toApplicative_1195_ = lean_ctor_get(v_inst_1192_, 0);
v_toBind_1196_ = lean_ctor_get(v_inst_1192_, 1);
lean_inc_n(v_toBind_1196_, 3);
v_getSemiring_1197_ = lean_ctor_get(v_inst_1194_, 0);
lean_inc(v_getSemiring_1197_);
v_modifySemiring_1198_ = lean_ctor_get(v_inst_1194_, 1);
lean_inc(v_modifySemiring_1198_);
lean_dec_ref(v_inst_1194_);
v_toPure_1199_ = lean_ctor_get(v_toApplicative_1195_, 1);
lean_inc_n(v_toPure_1199_, 2);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1200_, 0, v_toPure_1199_);
lean_closure_set(v___f_1200_, 1, v_modifySemiring_1198_);
lean_closure_set(v___f_1200_, 2, v_toBind_1196_);
v___f_1201_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1201_, 0, v_toPure_1199_);
lean_closure_set(v___f_1201_, 1, v_inst_1191_);
lean_closure_set(v___f_1201_, 2, v_inst_1192_);
lean_closure_set(v___f_1201_, 3, v_inst_1193_);
lean_closure_set(v___f_1201_, 4, v_toBind_1196_);
lean_closure_set(v___f_1201_, 5, v___f_1200_);
v___x_1202_ = lean_apply_4(v_toBind_1196_, lean_box(0), lean_box(0), v_getSemiring_1197_, v___f_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27(lean_object* v_m_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(v_inst_1204_, v_inst_1205_, v_inst_1206_, v_inst_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1209_, lean_object* v_vals_1210_, lean_object* v_i_1211_, lean_object* v_k_1212_){
_start:
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_array_get_size(v_keys_1209_);
v___x_1214_ = lean_nat_dec_lt(v_i_1211_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; 
lean_dec(v_i_1211_);
v___x_1215_ = lean_box(0);
return v___x_1215_;
}
else
{
lean_object* v_k_x27_1216_; size_t v___x_1217_; size_t v___x_1218_; uint8_t v___x_1219_; 
v_k_x27_1216_ = lean_array_fget_borrowed(v_keys_1209_, v_i_1211_);
v___x_1217_ = lean_ptr_addr(v_k_1212_);
v___x_1218_ = lean_ptr_addr(v_k_x27_1216_);
v___x_1219_ = lean_usize_dec_eq(v___x_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_unsigned_to_nat(1u);
v___x_1221_ = lean_nat_add(v_i_1211_, v___x_1220_);
lean_dec(v_i_1211_);
v_i_1211_ = v___x_1221_;
goto _start;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_array_fget_borrowed(v_vals_1210_, v_i_1211_);
lean_dec(v_i_1211_);
lean_inc(v___x_1223_);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1225_, lean_object* v_vals_1226_, lean_object* v_i_1227_, lean_object* v_k_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1225_, v_vals_1226_, v_i_1227_, v_k_1228_);
lean_dec_ref(v_k_1228_);
lean_dec_ref(v_vals_1226_);
lean_dec_ref(v_keys_1225_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_1230_, size_t v_x_1231_, lean_object* v_x_1232_){
_start:
{
if (lean_obj_tag(v_x_1230_) == 0)
{
lean_object* v_es_1233_; lean_object* v___x_1234_; size_t v___x_1235_; size_t v___x_1236_; lean_object* v_j_1237_; lean_object* v___x_1238_; 
v_es_1233_ = lean_ctor_get(v_x_1230_, 0);
v___x_1234_ = lean_box(2);
v___x_1235_ = ((size_t)31ULL);
v___x_1236_ = lean_usize_land(v_x_1231_, v___x_1235_);
v_j_1237_ = lean_usize_to_nat(v___x_1236_);
v___x_1238_ = lean_array_get_borrowed(v___x_1234_, v_es_1233_, v_j_1237_);
lean_dec(v_j_1237_);
switch(lean_obj_tag(v___x_1238_))
{
case 0:
{
lean_object* v_key_1239_; lean_object* v_val_1240_; size_t v___x_1241_; size_t v___x_1242_; uint8_t v___x_1243_; 
v_key_1239_ = lean_ctor_get(v___x_1238_, 0);
v_val_1240_ = lean_ctor_get(v___x_1238_, 1);
v___x_1241_ = lean_ptr_addr(v_x_1232_);
v___x_1242_ = lean_ptr_addr(v_key_1239_);
v___x_1243_ = lean_usize_dec_eq(v___x_1241_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_box(0);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; 
lean_inc(v_val_1240_);
v___x_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_val_1240_);
return v___x_1245_;
}
}
case 1:
{
lean_object* v_node_1246_; size_t v___x_1247_; size_t v___x_1248_; 
v_node_1246_ = lean_ctor_get(v___x_1238_, 0);
v___x_1247_ = ((size_t)5ULL);
v___x_1248_ = lean_usize_shift_right(v_x_1231_, v___x_1247_);
v_x_1230_ = v_node_1246_;
v_x_1231_ = v___x_1248_;
goto _start;
}
default: 
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_box(0);
return v___x_1250_;
}
}
}
else
{
lean_object* v_ks_1251_; lean_object* v_vs_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_ks_1251_ = lean_ctor_get(v_x_1230_, 0);
v_vs_1252_ = lean_ctor_get(v_x_1230_, 1);
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1251_, v_vs_1252_, v___x_1253_, v_x_1232_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
size_t v_x_890__boxed_1258_; lean_object* v_res_1259_; 
v_x_890__boxed_1258_ = lean_unbox_usize(v_x_1256_);
lean_dec(v_x_1256_);
v_res_1259_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1255_, v_x_890__boxed_1258_, v_x_1257_);
lean_dec_ref(v_x_1257_);
lean_dec_ref(v_x_1255_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
size_t v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; uint64_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; 
v___x_1262_ = lean_ptr_addr(v_x_1261_);
v___x_1263_ = ((size_t)3ULL);
v___x_1264_ = lean_usize_shift_right(v___x_1262_, v___x_1263_);
v___x_1265_ = lean_usize_to_uint64(v___x_1264_);
v___x_1266_ = lean_uint64_to_usize(v___x_1265_);
v___x_1267_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1260_, v___x_1266_, v_x_1261_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_1268_, lean_object* v_x_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_1268_, v_x_1269_);
lean_dec_ref(v_x_1269_);
lean_dec_ref(v_x_1268_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(lean_object* v_e_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1272_, v_a_1273_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1285_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_exprToSemiringId_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v_exprToSemiringId_1280_ = lean_ctor_get(v_a_1276_, 5);
lean_inc_ref(v_exprToSemiringId_1280_);
lean_dec(v_a_1276_);
v___x_1281_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_exprToSemiringId_1280_, v_e_1271_);
lean_dec_ref(v_exprToSemiringId_1280_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1281_);
v___x_1283_ = v___x_1278_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1275_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1275_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(lean_object* v_e_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1294_, v_a_1295_, v_a_1296_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_e_1294_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(lean_object* v_e_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1299_, v_a_1300_, v_a_1308_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(lean_object* v_e_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(v_e_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_e_1312_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(lean_object* v_00_u03b2_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_1326_, v_x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(v_00_u03b2_1329_, v_x_1330_, v_x_1331_);
lean_dec_ref(v_x_1331_);
lean_dec_ref(v_x_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1333_, lean_object* v_x_1334_, size_t v_x_1335_, lean_object* v_x_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1334_, v_x_1335_, v_x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_){
_start:
{
size_t v_x_1011__boxed_1342_; lean_object* v_res_1343_; 
v_x_1011__boxed_1342_ = lean_unbox_usize(v_x_1340_);
lean_dec(v_x_1340_);
v_res_1343_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(v_00_u03b2_1338_, v_x_1339_, v_x_1011__boxed_1342_, v_x_1341_);
lean_dec_ref(v_x_1341_);
lean_dec_ref(v_x_1339_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1344_, lean_object* v_keys_1345_, lean_object* v_vals_1346_, lean_object* v_heq_1347_, lean_object* v_i_1348_, lean_object* v_k_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1345_, v_vals_1346_, v_i_1348_, v_k_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1351_, lean_object* v_keys_1352_, lean_object* v_vals_1353_, lean_object* v_heq_1354_, lean_object* v_i_1355_, lean_object* v_k_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1351_, v_keys_1352_, v_vals_1353_, v_heq_1354_, v_i_1355_, v_k_1356_);
lean_dec_ref(v_k_1356_);
lean_dec_ref(v_vals_1353_);
lean_dec_ref(v_keys_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_){
_start:
{
lean_object* v_ks_1362_; lean_object* v_vs_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1389_; 
v_ks_1362_ = lean_ctor_get(v_x_1358_, 0);
v_vs_1363_ = lean_ctor_get(v_x_1358_, 1);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_x_1358_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1365_ = v_x_1358_;
v_isShared_1366_ = v_isSharedCheck_1389_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_vs_1363_);
lean_inc(v_ks_1362_);
lean_dec(v_x_1358_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1389_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = lean_array_get_size(v_ks_1362_);
v___x_1368_ = lean_nat_dec_lt(v_x_1359_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_dec(v_x_1359_);
v___x_1369_ = lean_array_push(v_ks_1362_, v_x_1360_);
v___x_1370_ = lean_array_push(v_vs_1363_, v_x_1361_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___x_1370_);
lean_ctor_set(v___x_1365_, 0, v___x_1369_);
v___x_1372_ = v___x_1365_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
lean_object* v_k_x27_1374_; size_t v___x_1375_; size_t v___x_1376_; uint8_t v___x_1377_; 
v_k_x27_1374_ = lean_array_fget_borrowed(v_ks_1362_, v_x_1359_);
v___x_1375_ = lean_ptr_addr(v_x_1360_);
v___x_1376_ = lean_ptr_addr(v_k_x27_1374_);
v___x_1377_ = lean_usize_dec_eq(v___x_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1379_; 
if (v_isShared_1366_ == 0)
{
v___x_1379_ = v___x_1365_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_ks_1362_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_vs_1363_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_unsigned_to_nat(1u);
v___x_1381_ = lean_nat_add(v_x_1359_, v___x_1380_);
lean_dec(v_x_1359_);
v_x_1358_ = v___x_1379_;
v_x_1359_ = v___x_1381_;
goto _start;
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1384_ = lean_array_fset(v_ks_1362_, v_x_1359_, v_x_1360_);
v___x_1385_ = lean_array_fset(v_vs_1363_, v_x_1359_, v_x_1361_);
lean_dec(v_x_1359_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___x_1385_);
lean_ctor_set(v___x_1365_, 0, v___x_1384_);
v___x_1387_ = v___x_1365_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1390_, lean_object* v_k_1391_, lean_object* v_v_1392_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1390_, v___x_1393_, v_k_1391_, v_v_1392_);
return v___x_1394_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(lean_object* v_x_1396_, size_t v_x_1397_, size_t v_x_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_){
_start:
{
if (lean_obj_tag(v_x_1396_) == 0)
{
lean_object* v_es_1401_; size_t v___x_1402_; size_t v___x_1403_; lean_object* v_j_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_es_1401_ = lean_ctor_get(v_x_1396_, 0);
v___x_1402_ = ((size_t)31ULL);
v___x_1403_ = lean_usize_land(v_x_1397_, v___x_1402_);
v_j_1404_ = lean_usize_to_nat(v___x_1403_);
v___x_1405_ = lean_array_get_size(v_es_1401_);
v___x_1406_ = lean_nat_dec_lt(v_j_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_dec(v_j_1404_);
lean_dec(v_x_1400_);
lean_dec_ref(v_x_1399_);
return v_x_1396_;
}
else
{
lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1447_; 
lean_inc_ref(v_es_1401_);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1396_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v_x_1396_, 0);
lean_dec(v_unused_1448_);
v___x_1408_ = v_x_1396_;
v_isShared_1409_ = v_isSharedCheck_1447_;
goto v_resetjp_1407_;
}
else
{
lean_dec(v_x_1396_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1447_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_v_1410_; lean_object* v___x_1411_; lean_object* v_xs_x27_1412_; lean_object* v___y_1414_; 
v_v_1410_ = lean_array_fget(v_es_1401_, v_j_1404_);
v___x_1411_ = lean_box(0);
v_xs_x27_1412_ = lean_array_fset(v_es_1401_, v_j_1404_, v___x_1411_);
switch(lean_obj_tag(v_v_1410_))
{
case 0:
{
lean_object* v_key_1419_; lean_object* v_val_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1432_; 
v_key_1419_ = lean_ctor_get(v_v_1410_, 0);
v_val_1420_ = lean_ctor_get(v_v_1410_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_v_1410_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1422_ = v_v_1410_;
v_isShared_1423_ = v_isSharedCheck_1432_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_val_1420_);
lean_inc(v_key_1419_);
lean_dec(v_v_1410_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1432_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
size_t v___x_1424_; size_t v___x_1425_; uint8_t v___x_1426_; 
v___x_1424_ = lean_ptr_addr(v_x_1399_);
v___x_1425_ = lean_ptr_addr(v_key_1419_);
v___x_1426_ = lean_usize_dec_eq(v___x_1424_, v___x_1425_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_del_object(v___x_1422_);
v___x_1427_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1419_, v_val_1420_, v_x_1399_, v_x_1400_);
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
v___y_1414_ = v___x_1428_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1430_; 
lean_dec(v_val_1420_);
lean_dec(v_key_1419_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 1, v_x_1400_);
lean_ctor_set(v___x_1422_, 0, v_x_1399_);
v___x_1430_ = v___x_1422_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_x_1399_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_x_1400_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
v___y_1414_ = v___x_1430_;
goto v___jp_1413_;
}
}
}
}
case 1:
{
lean_object* v_node_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1445_; 
v_node_1433_ = lean_ctor_get(v_v_1410_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_v_1410_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1435_ = v_v_1410_;
v_isShared_1436_ = v_isSharedCheck_1445_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_node_1433_);
lean_dec(v_v_1410_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1445_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
size_t v___x_1437_; size_t v___x_1438_; size_t v___x_1439_; size_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1437_ = ((size_t)5ULL);
v___x_1438_ = lean_usize_shift_right(v_x_1397_, v___x_1437_);
v___x_1439_ = ((size_t)1ULL);
v___x_1440_ = lean_usize_add(v_x_1398_, v___x_1439_);
v___x_1441_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_node_1433_, v___x_1438_, v___x_1440_, v_x_1399_, v_x_1400_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1441_);
v___x_1443_ = v___x_1435_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
v___y_1414_ = v___x_1443_;
goto v___jp_1413_;
}
}
}
default: 
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v_x_1399_);
lean_ctor_set(v___x_1446_, 1, v_x_1400_);
v___y_1414_ = v___x_1446_;
goto v___jp_1413_;
}
}
v___jp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1415_ = lean_array_fset(v_xs_x27_1412_, v_j_1404_, v___y_1414_);
lean_dec(v_j_1404_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1415_);
v___x_1417_ = v___x_1408_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
else
{
lean_object* v_ks_1449_; lean_object* v_vs_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1470_; 
v_ks_1449_ = lean_ctor_get(v_x_1396_, 0);
v_vs_1450_ = lean_ctor_get(v_x_1396_, 1);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_x_1396_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1452_ = v_x_1396_;
v_isShared_1453_ = v_isSharedCheck_1470_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_vs_1450_);
lean_inc(v_ks_1449_);
lean_dec(v_x_1396_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1470_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_ks_1449_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_vs_1450_);
v___x_1455_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v_newNode_1456_; uint8_t v___y_1458_; size_t v___x_1464_; uint8_t v___x_1465_; 
v_newNode_1456_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v___x_1455_, v_x_1399_, v_x_1400_);
v___x_1464_ = ((size_t)7ULL);
v___x_1465_ = lean_usize_dec_le(v___x_1464_, v_x_1398_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1456_);
v___x_1467_ = lean_unsigned_to_nat(4u);
v___x_1468_ = lean_nat_dec_lt(v___x_1466_, v___x_1467_);
lean_dec(v___x_1466_);
v___y_1458_ = v___x_1468_;
goto v___jp_1457_;
}
else
{
v___y_1458_ = v___x_1465_;
goto v___jp_1457_;
}
v___jp_1457_:
{
if (v___y_1458_ == 0)
{
lean_object* v_ks_1459_; lean_object* v_vs_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_ks_1459_ = lean_ctor_get(v_newNode_1456_, 0);
lean_inc_ref(v_ks_1459_);
v_vs_1460_ = lean_ctor_get(v_newNode_1456_, 1);
lean_inc_ref(v_vs_1460_);
lean_dec_ref(v_newNode_1456_);
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_1463_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_x_1398_, v_ks_1459_, v_vs_1460_, v___x_1461_, v___x_1462_);
lean_dec_ref(v_vs_1460_);
lean_dec_ref(v_ks_1459_);
return v___x_1463_;
}
else
{
return v_newNode_1456_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1471_, lean_object* v_keys_1472_, lean_object* v_vals_1473_, lean_object* v_i_1474_, lean_object* v_entries_1475_){
_start:
{
lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = lean_array_get_size(v_keys_1472_);
v___x_1477_ = lean_nat_dec_lt(v_i_1474_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_dec(v_i_1474_);
return v_entries_1475_;
}
else
{
lean_object* v_k_1478_; lean_object* v_v_1479_; size_t v___x_1480_; size_t v___x_1481_; size_t v___x_1482_; uint64_t v___x_1483_; size_t v_h_1484_; size_t v___x_1485_; lean_object* v___x_1486_; size_t v___x_1487_; size_t v___x_1488_; size_t v___x_1489_; size_t v_h_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_k_1478_ = lean_array_fget_borrowed(v_keys_1472_, v_i_1474_);
v_v_1479_ = lean_array_fget_borrowed(v_vals_1473_, v_i_1474_);
v___x_1480_ = lean_ptr_addr(v_k_1478_);
v___x_1481_ = ((size_t)3ULL);
v___x_1482_ = lean_usize_shift_right(v___x_1480_, v___x_1481_);
v___x_1483_ = lean_usize_to_uint64(v___x_1482_);
v_h_1484_ = lean_uint64_to_usize(v___x_1483_);
v___x_1485_ = ((size_t)5ULL);
v___x_1486_ = lean_unsigned_to_nat(1u);
v___x_1487_ = ((size_t)1ULL);
v___x_1488_ = lean_usize_sub(v_depth_1471_, v___x_1487_);
v___x_1489_ = lean_usize_mul(v___x_1485_, v___x_1488_);
v_h_1490_ = lean_usize_shift_right(v_h_1484_, v___x_1489_);
v___x_1491_ = lean_nat_add(v_i_1474_, v___x_1486_);
lean_dec(v_i_1474_);
lean_inc(v_v_1479_);
lean_inc(v_k_1478_);
v___x_1492_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_entries_1475_, v_h_1490_, v_depth_1471_, v_k_1478_, v_v_1479_);
v_i_1474_ = v___x_1491_;
v_entries_1475_ = v___x_1492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1494_, lean_object* v_keys_1495_, lean_object* v_vals_1496_, lean_object* v_i_1497_, lean_object* v_entries_1498_){
_start:
{
size_t v_depth_boxed_1499_; lean_object* v_res_1500_; 
v_depth_boxed_1499_ = lean_unbox_usize(v_depth_1494_);
lean_dec(v_depth_1494_);
v_res_1500_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1499_, v_keys_1495_, v_vals_1496_, v_i_1497_, v_entries_1498_);
lean_dec_ref(v_vals_1496_);
lean_dec_ref(v_keys_1495_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_1501_, lean_object* v_x_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_){
_start:
{
size_t v_x_7265__boxed_1506_; size_t v_x_7266__boxed_1507_; lean_object* v_res_1508_; 
v_x_7265__boxed_1506_ = lean_unbox_usize(v_x_1502_);
lean_dec(v_x_1502_);
v_x_7266__boxed_1507_ = lean_unbox_usize(v_x_1503_);
lean_dec(v_x_1503_);
v_res_1508_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1501_, v_x_7265__boxed_1506_, v_x_7266__boxed_1507_, v_x_1504_, v_x_1505_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object* v_x_1509_, lean_object* v_x_1510_, lean_object* v_x_1511_){
_start:
{
size_t v___x_1512_; size_t v___x_1513_; size_t v___x_1514_; uint64_t v___x_1515_; size_t v___x_1516_; size_t v___x_1517_; lean_object* v___x_1518_; 
v___x_1512_ = lean_ptr_addr(v_x_1510_);
v___x_1513_ = ((size_t)3ULL);
v___x_1514_ = lean_usize_shift_right(v___x_1512_, v___x_1513_);
v___x_1515_ = lean_usize_to_uint64(v___x_1514_);
v___x_1516_ = lean_uint64_to_usize(v___x_1515_);
v___x_1517_ = ((size_t)1ULL);
v___x_1518_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1509_, v___x_1516_, v___x_1517_, v_x_1510_, v_x_1511_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object* v_e_1519_, lean_object* v_a_1520_, lean_object* v_s_1521_){
_start:
{
lean_object* v_rings_1522_; lean_object* v_typeIdOf_1523_; lean_object* v_exprToRingId_1524_; lean_object* v_semirings_1525_; lean_object* v_stypeIdOf_1526_; lean_object* v_exprToSemiringId_1527_; lean_object* v_ncRings_1528_; lean_object* v_exprToNCRingId_1529_; lean_object* v_nctypeIdOf_1530_; lean_object* v_ncSemirings_1531_; lean_object* v_exprToNCSemiringId_1532_; lean_object* v_ncstypeIdOf_1533_; lean_object* v_steps_1534_; uint8_t v_reportedMaxDegreeIssue_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1543_; 
v_rings_1522_ = lean_ctor_get(v_s_1521_, 0);
v_typeIdOf_1523_ = lean_ctor_get(v_s_1521_, 1);
v_exprToRingId_1524_ = lean_ctor_get(v_s_1521_, 2);
v_semirings_1525_ = lean_ctor_get(v_s_1521_, 3);
v_stypeIdOf_1526_ = lean_ctor_get(v_s_1521_, 4);
v_exprToSemiringId_1527_ = lean_ctor_get(v_s_1521_, 5);
v_ncRings_1528_ = lean_ctor_get(v_s_1521_, 6);
v_exprToNCRingId_1529_ = lean_ctor_get(v_s_1521_, 7);
v_nctypeIdOf_1530_ = lean_ctor_get(v_s_1521_, 8);
v_ncSemirings_1531_ = lean_ctor_get(v_s_1521_, 9);
v_exprToNCSemiringId_1532_ = lean_ctor_get(v_s_1521_, 10);
v_ncstypeIdOf_1533_ = lean_ctor_get(v_s_1521_, 11);
v_steps_1534_ = lean_ctor_get(v_s_1521_, 12);
v_reportedMaxDegreeIssue_1535_ = lean_ctor_get_uint8(v_s_1521_, sizeof(void*)*13);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_s_1521_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1537_ = v_s_1521_;
v_isShared_1538_ = v_isSharedCheck_1543_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_steps_1534_);
lean_inc(v_ncstypeIdOf_1533_);
lean_inc(v_exprToNCSemiringId_1532_);
lean_inc(v_ncSemirings_1531_);
lean_inc(v_nctypeIdOf_1530_);
lean_inc(v_exprToNCRingId_1529_);
lean_inc(v_ncRings_1528_);
lean_inc(v_exprToSemiringId_1527_);
lean_inc(v_stypeIdOf_1526_);
lean_inc(v_semirings_1525_);
lean_inc(v_exprToRingId_1524_);
lean_inc(v_typeIdOf_1523_);
lean_inc(v_rings_1522_);
lean_dec(v_s_1521_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1543_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
lean_inc(v_a_1520_);
v___x_1539_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_exprToSemiringId_1527_, v_e_1519_, v_a_1520_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 5, v___x_1539_);
v___x_1541_ = v___x_1537_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_rings_1522_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_typeIdOf_1523_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_exprToRingId_1524_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_semirings_1525_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_stypeIdOf_1526_);
lean_ctor_set(v_reuseFailAlloc_1542_, 5, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1542_, 6, v_ncRings_1528_);
lean_ctor_set(v_reuseFailAlloc_1542_, 7, v_exprToNCRingId_1529_);
lean_ctor_set(v_reuseFailAlloc_1542_, 8, v_nctypeIdOf_1530_);
lean_ctor_set(v_reuseFailAlloc_1542_, 9, v_ncSemirings_1531_);
lean_ctor_set(v_reuseFailAlloc_1542_, 10, v_exprToNCSemiringId_1532_);
lean_ctor_set(v_reuseFailAlloc_1542_, 11, v_ncstypeIdOf_1533_);
lean_ctor_set(v_reuseFailAlloc_1542_, 12, v_steps_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1535_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object* v_e_1544_, lean_object* v_a_1545_, lean_object* v_s_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(v_e_1544_, v_a_1545_, v_s_1546_);
lean_dec(v_a_1545_);
return v_res_1547_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0));
v___x_1550_ = l_Lean_stringToMessageData(v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object* v_e_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1551_, v_a_1553_, v_a_1558_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
if (lean_obj_tag(v_a_1565_) == 1)
{
lean_object* v_val_1566_; uint8_t v___x_1567_; 
v_val_1566_ = lean_ctor_get(v_a_1565_, 0);
lean_inc(v_val_1566_);
lean_dec_ref_known(v_a_1565_, 1);
v___x_1567_ = lean_nat_dec_eq(v_val_1566_, v_a_1552_);
lean_dec(v_val_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1554_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; uint8_t v_verbose_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
v_verbose_1570_ = lean_ctor_get_uint8(v_a_1569_, 0);
lean_dec(v_a_1569_);
if (v_verbose_1570_ == 0)
{
lean_dec_ref(v_e_1551_);
goto v___jp_1561_;
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1571_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1);
v___x_1572_ = l_Lean_indentExpr(v_e_1551_);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = l_Lean_Meta_Sym_reportIssue(v___x_1573_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_dec_ref_known(v___x_1574_, 1);
goto v___jp_1561_;
}
else
{
return v___x_1574_;
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v_e_1551_);
v_a_1575_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1568_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1568_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
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
else
{
lean_dec_ref(v_e_1551_);
goto v___jp_1561_;
}
}
else
{
lean_object* v___f_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec(v_a_1565_);
lean_inc(v_a_1552_);
v___f_1583_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1583_, 0, v_e_1551_);
lean_closure_set(v___f_1583_, 1, v_a_1552_);
v___x_1584_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1585_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1584_, v___f_1583_, v_a_1553_);
return v___x_1585_;
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v_e_1551_);
v_a_1586_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1564_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1564_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
v___jp_1561_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object* v_e_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec(v_a_1595_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object* v_e_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1605_, v_a_1606_, v_a_1607_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object* v_e_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec(v_a_1620_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object* v_00_u03b2_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_1634_, v_x_1635_, v_x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_1638_, lean_object* v_x_1639_, size_t v_x_1640_, size_t v_x_1641_, lean_object* v_x_1642_, lean_object* v_x_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1639_, v_x_1640_, v_x_1641_, v_x_1642_, v_x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1645_, lean_object* v_x_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_){
_start:
{
size_t v_x_7555__boxed_1651_; size_t v_x_7556__boxed_1652_; lean_object* v_res_1653_; 
v_x_7555__boxed_1651_ = lean_unbox_usize(v_x_1647_);
lean_dec(v_x_1647_);
v_x_7556__boxed_1652_ = lean_unbox_usize(v_x_1648_);
lean_dec(v_x_1648_);
v_res_1653_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_1645_, v_x_1646_, v_x_7555__boxed_1651_, v_x_7556__boxed_1652_, v_x_1649_, v_x_1650_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1654_, lean_object* v_n_1655_, lean_object* v_k_1656_, lean_object* v_v_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_1655_, v_k_1656_, v_v_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1659_, size_t v_depth_1660_, lean_object* v_keys_1661_, lean_object* v_vals_1662_, lean_object* v_heq_1663_, lean_object* v_i_1664_, lean_object* v_entries_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_1660_, v_keys_1661_, v_vals_1662_, v_i_1664_, v_entries_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1667_, lean_object* v_depth_1668_, lean_object* v_keys_1669_, lean_object* v_vals_1670_, lean_object* v_heq_1671_, lean_object* v_i_1672_, lean_object* v_entries_1673_){
_start:
{
size_t v_depth_boxed_1674_; lean_object* v_res_1675_; 
v_depth_boxed_1674_ = lean_unbox_usize(v_depth_1668_);
lean_dec(v_depth_1668_);
v_res_1675_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_1667_, v_depth_boxed_1674_, v_keys_1669_, v_vals_1670_, v_heq_1671_, v_i_1672_, v_entries_1673_);
lean_dec_ref(v_vals_1670_);
lean_dec_ref(v_keys_1669_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1676_, lean_object* v_x_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1677_, v_x_1678_, v_x_1679_, v_x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object* v_e_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1682_, v___y_1683_, v___y_1684_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object* v_e_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(v_e_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object* v_e_1712_, lean_object* v___f_1713_, lean_object* v___f_1714_, lean_object* v_size_1715_, lean_object* v_s_1716_){
_start:
{
lean_object* v_id_1717_; lean_object* v_type_1718_; lean_object* v_u_1719_; lean_object* v_semiringInst_1720_; lean_object* v_addFn_x3f_1721_; lean_object* v_mulFn_x3f_1722_; lean_object* v_powFn_x3f_1723_; lean_object* v_natCastFn_x3f_1724_; lean_object* v_denote_1725_; lean_object* v_vars_1726_; lean_object* v_varMap_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1736_; 
v_id_1717_ = lean_ctor_get(v_s_1716_, 0);
v_type_1718_ = lean_ctor_get(v_s_1716_, 1);
v_u_1719_ = lean_ctor_get(v_s_1716_, 2);
v_semiringInst_1720_ = lean_ctor_get(v_s_1716_, 3);
v_addFn_x3f_1721_ = lean_ctor_get(v_s_1716_, 4);
v_mulFn_x3f_1722_ = lean_ctor_get(v_s_1716_, 5);
v_powFn_x3f_1723_ = lean_ctor_get(v_s_1716_, 6);
v_natCastFn_x3f_1724_ = lean_ctor_get(v_s_1716_, 7);
v_denote_1725_ = lean_ctor_get(v_s_1716_, 8);
v_vars_1726_ = lean_ctor_get(v_s_1716_, 9);
v_varMap_1727_ = lean_ctor_get(v_s_1716_, 10);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_s_1716_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1729_ = v_s_1716_;
v_isShared_1730_ = v_isSharedCheck_1736_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_varMap_1727_);
lean_inc(v_vars_1726_);
lean_inc(v_denote_1725_);
lean_inc(v_natCastFn_x3f_1724_);
lean_inc(v_powFn_x3f_1723_);
lean_inc(v_mulFn_x3f_1722_);
lean_inc(v_addFn_x3f_1721_);
lean_inc(v_semiringInst_1720_);
lean_inc(v_u_1719_);
lean_inc(v_type_1718_);
lean_inc(v_id_1717_);
lean_dec(v_s_1716_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1736_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_inc_ref(v_e_1712_);
v___x_1731_ = l_Lean_PersistentArray_push___redArg(v_vars_1726_, v_e_1712_);
v___x_1732_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1713_, v___f_1714_, v_varMap_1727_, v_e_1712_, v_size_1715_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 10, v___x_1732_);
lean_ctor_set(v___x_1729_, 9, v___x_1731_);
v___x_1734_ = v___x_1729_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_id_1717_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_type_1718_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_u_1719_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_semiringInst_1720_);
lean_ctor_set(v_reuseFailAlloc_1735_, 4, v_addFn_x3f_1721_);
lean_ctor_set(v_reuseFailAlloc_1735_, 5, v_mulFn_x3f_1722_);
lean_ctor_set(v_reuseFailAlloc_1735_, 6, v_powFn_x3f_1723_);
lean_ctor_set(v_reuseFailAlloc_1735_, 7, v_natCastFn_x3f_1724_);
lean_ctor_set(v_reuseFailAlloc_1735_, 8, v_denote_1725_);
lean_ctor_set(v_reuseFailAlloc_1735_, 9, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1735_, 10, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object* v_toPure_1737_, lean_object* v_size_1738_, lean_object* v_____r_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_apply_2(v_toPure_1737_, lean_box(0), v_size_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object* v_e_1741_, lean_object* v_inst_1742_, lean_object* v_toBind_1743_, lean_object* v___f_1744_, lean_object* v_____r_1745_){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1746_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1747_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_1747_, 0, lean_box(0));
lean_closure_set(v___x_1747_, 1, v___x_1746_);
lean_closure_set(v___x_1747_, 2, v_e_1741_);
v___x_1748_ = lean_apply_2(v_inst_1742_, lean_box(0), v___x_1747_);
v___x_1749_ = lean_apply_4(v_toBind_1743_, lean_box(0), lean_box(0), v___x_1748_, v___f_1744_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object* v_inst_1750_, lean_object* v_e_1751_, lean_object* v_toBind_1752_, lean_object* v___f_1753_, lean_object* v_____r_1754_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_apply_1(v_inst_1750_, v_e_1751_);
v___x_1756_ = lean_apply_4(v_toBind_1752_, lean_box(0), lean_box(0), v___x_1755_, v___f_1753_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object* v___f_1757_, lean_object* v___f_1758_, lean_object* v_e_1759_, lean_object* v_toPure_1760_, lean_object* v_inst_1761_, lean_object* v_toBind_1762_, lean_object* v_inst_1763_, lean_object* v_modifySemiring_1764_, lean_object* v_s_1765_){
_start:
{
lean_object* v_vars_1766_; lean_object* v_varMap_1767_; lean_object* v___x_1768_; 
v_vars_1766_ = lean_ctor_get(v_s_1765_, 9);
lean_inc_ref(v_vars_1766_);
v_varMap_1767_ = lean_ctor_get(v_s_1765_, 10);
lean_inc_ref(v_varMap_1767_);
lean_dec_ref(v_s_1765_);
lean_inc_ref(v_e_1759_);
lean_inc_ref(v___f_1758_);
lean_inc_ref(v___f_1757_);
v___x_1768_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_1757_, v___f_1758_, v_varMap_1767_, v_e_1759_);
lean_dec_ref(v_varMap_1767_);
if (lean_obj_tag(v___x_1768_) == 1)
{
lean_object* v_val_1769_; lean_object* v___x_1770_; 
lean_dec_ref(v_vars_1766_);
lean_dec(v_modifySemiring_1764_);
lean_dec(v_inst_1763_);
lean_dec(v_toBind_1762_);
lean_dec(v_inst_1761_);
lean_dec_ref(v_e_1759_);
lean_dec_ref(v___f_1758_);
lean_dec_ref(v___f_1757_);
v_val_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_val_1769_);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1770_ = lean_apply_2(v_toPure_1760_, lean_box(0), v_val_1769_);
return v___x_1770_;
}
else
{
lean_object* v_size_1771_; lean_object* v___f_1772_; lean_object* v___f_1773_; lean_object* v___f_1774_; lean_object* v___f_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec(v___x_1768_);
v_size_1771_ = lean_ctor_get(v_vars_1766_, 2);
lean_inc_n(v_size_1771_, 2);
lean_dec_ref(v_vars_1766_);
lean_inc_ref_n(v_e_1759_, 2);
v___f_1772_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1772_, 0, v_e_1759_);
lean_closure_set(v___f_1772_, 1, v___f_1757_);
lean_closure_set(v___f_1772_, 2, v___f_1758_);
lean_closure_set(v___f_1772_, 3, v_size_1771_);
v___f_1773_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1773_, 0, v_toPure_1760_);
lean_closure_set(v___f_1773_, 1, v_size_1771_);
lean_inc_n(v_toBind_1762_, 2);
v___f_1774_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1774_, 0, v_e_1759_);
lean_closure_set(v___f_1774_, 1, v_inst_1761_);
lean_closure_set(v___f_1774_, 2, v_toBind_1762_);
lean_closure_set(v___f_1774_, 3, v___f_1773_);
v___f_1775_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1775_, 0, v_inst_1763_);
lean_closure_set(v___f_1775_, 1, v_e_1759_);
lean_closure_set(v___f_1775_, 2, v_toBind_1762_);
lean_closure_set(v___f_1775_, 3, v___f_1774_);
v___x_1776_ = lean_apply_1(v_modifySemiring_1764_, v___f_1772_);
v___x_1777_ = lean_apply_4(v_toBind_1762_, lean_box(0), lean_box(0), v___x_1776_, v___f_1775_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_e_1784_){
_start:
{
lean_object* v_toApplicative_1785_; lean_object* v_toBind_1786_; lean_object* v_getSemiring_1787_; lean_object* v_modifySemiring_1788_; lean_object* v_toPure_1789_; lean_object* v___f_1790_; lean_object* v___f_1791_; lean_object* v___f_1792_; lean_object* v___x_1793_; 
v_toApplicative_1785_ = lean_ctor_get(v_inst_1781_, 0);
lean_inc_ref(v_toApplicative_1785_);
v_toBind_1786_ = lean_ctor_get(v_inst_1781_, 1);
lean_inc_n(v_toBind_1786_, 2);
lean_dec_ref(v_inst_1781_);
v_getSemiring_1787_ = lean_ctor_get(v_inst_1782_, 0);
lean_inc(v_getSemiring_1787_);
v_modifySemiring_1788_ = lean_ctor_get(v_inst_1782_, 1);
lean_inc(v_modifySemiring_1788_);
lean_dec_ref(v_inst_1782_);
v_toPure_1789_ = lean_ctor_get(v_toApplicative_1785_, 1);
lean_inc(v_toPure_1789_);
lean_dec_ref(v_toApplicative_1785_);
v___f_1790_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0));
v___f_1791_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1));
v___f_1792_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1792_, 0, v___f_1790_);
lean_closure_set(v___f_1792_, 1, v___f_1791_);
lean_closure_set(v___f_1792_, 2, v_e_1784_);
lean_closure_set(v___f_1792_, 3, v_toPure_1789_);
lean_closure_set(v___f_1792_, 4, v_inst_1780_);
lean_closure_set(v___f_1792_, 5, v_toBind_1786_);
lean_closure_set(v___f_1792_, 6, v_inst_1783_);
lean_closure_set(v___f_1792_, 7, v_modifySemiring_1788_);
v___x_1793_ = lean_apply_4(v_toBind_1786_, lean_box(0), lean_box(0), v_getSemiring_1787_, v___f_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object* v_m_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_inst_1798_, lean_object* v_e_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v_inst_1795_, v_inst_1796_, v_inst_1797_, v_inst_1798_, v_e_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(lean_object* v___y_1801_, lean_object* v_e_1802_, lean_object* v_size_1803_, lean_object* v_s_1804_){
_start:
{
lean_object* v_rings_1805_; lean_object* v_typeIdOf_1806_; lean_object* v_exprToRingId_1807_; lean_object* v_semirings_1808_; lean_object* v_stypeIdOf_1809_; lean_object* v_exprToSemiringId_1810_; lean_object* v_ncRings_1811_; lean_object* v_exprToNCRingId_1812_; lean_object* v_nctypeIdOf_1813_; lean_object* v_ncSemirings_1814_; lean_object* v_exprToNCSemiringId_1815_; lean_object* v_ncstypeIdOf_1816_; lean_object* v_steps_1817_; uint8_t v_reportedMaxDegreeIssue_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v_rings_1805_ = lean_ctor_get(v_s_1804_, 0);
v_typeIdOf_1806_ = lean_ctor_get(v_s_1804_, 1);
v_exprToRingId_1807_ = lean_ctor_get(v_s_1804_, 2);
v_semirings_1808_ = lean_ctor_get(v_s_1804_, 3);
v_stypeIdOf_1809_ = lean_ctor_get(v_s_1804_, 4);
v_exprToSemiringId_1810_ = lean_ctor_get(v_s_1804_, 5);
v_ncRings_1811_ = lean_ctor_get(v_s_1804_, 6);
v_exprToNCRingId_1812_ = lean_ctor_get(v_s_1804_, 7);
v_nctypeIdOf_1813_ = lean_ctor_get(v_s_1804_, 8);
v_ncSemirings_1814_ = lean_ctor_get(v_s_1804_, 9);
v_exprToNCSemiringId_1815_ = lean_ctor_get(v_s_1804_, 10);
v_ncstypeIdOf_1816_ = lean_ctor_get(v_s_1804_, 11);
v_steps_1817_ = lean_ctor_get(v_s_1804_, 12);
v_reportedMaxDegreeIssue_1818_ = lean_ctor_get_uint8(v_s_1804_, sizeof(void*)*13);
v___x_1819_ = lean_array_get_size(v_semirings_1808_);
v___x_1820_ = lean_nat_dec_lt(v___y_1801_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_dec(v_size_1803_);
lean_dec_ref(v_e_1802_);
return v_s_1804_;
}
else
{
lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1863_; 
lean_inc(v_steps_1817_);
lean_inc_ref(v_ncstypeIdOf_1816_);
lean_inc_ref(v_exprToNCSemiringId_1815_);
lean_inc_ref(v_ncSemirings_1814_);
lean_inc_ref(v_nctypeIdOf_1813_);
lean_inc_ref(v_exprToNCRingId_1812_);
lean_inc_ref(v_ncRings_1811_);
lean_inc_ref(v_exprToSemiringId_1810_);
lean_inc_ref(v_stypeIdOf_1809_);
lean_inc_ref(v_semirings_1808_);
lean_inc_ref(v_exprToRingId_1807_);
lean_inc_ref(v_typeIdOf_1806_);
lean_inc_ref(v_rings_1805_);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_s_1804_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; lean_object* v_unused_1865_; lean_object* v_unused_1866_; lean_object* v_unused_1867_; lean_object* v_unused_1868_; lean_object* v_unused_1869_; lean_object* v_unused_1870_; lean_object* v_unused_1871_; lean_object* v_unused_1872_; lean_object* v_unused_1873_; lean_object* v_unused_1874_; lean_object* v_unused_1875_; lean_object* v_unused_1876_; 
v_unused_1864_ = lean_ctor_get(v_s_1804_, 12);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_s_1804_, 11);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_s_1804_, 10);
lean_dec(v_unused_1866_);
v_unused_1867_ = lean_ctor_get(v_s_1804_, 9);
lean_dec(v_unused_1867_);
v_unused_1868_ = lean_ctor_get(v_s_1804_, 8);
lean_dec(v_unused_1868_);
v_unused_1869_ = lean_ctor_get(v_s_1804_, 7);
lean_dec(v_unused_1869_);
v_unused_1870_ = lean_ctor_get(v_s_1804_, 6);
lean_dec(v_unused_1870_);
v_unused_1871_ = lean_ctor_get(v_s_1804_, 5);
lean_dec(v_unused_1871_);
v_unused_1872_ = lean_ctor_get(v_s_1804_, 4);
lean_dec(v_unused_1872_);
v_unused_1873_ = lean_ctor_get(v_s_1804_, 3);
lean_dec(v_unused_1873_);
v_unused_1874_ = lean_ctor_get(v_s_1804_, 2);
lean_dec(v_unused_1874_);
v_unused_1875_ = lean_ctor_get(v_s_1804_, 1);
lean_dec(v_unused_1875_);
v_unused_1876_ = lean_ctor_get(v_s_1804_, 0);
lean_dec(v_unused_1876_);
v___x_1822_ = v_s_1804_;
v_isShared_1823_ = v_isSharedCheck_1863_;
goto v_resetjp_1821_;
}
else
{
lean_dec(v_s_1804_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1863_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_v_1824_; lean_object* v_toSemiring_1825_; lean_object* v_ringId_1826_; lean_object* v_commSemiringInst_1827_; lean_object* v_addRightCancelInst_x3f_1828_; lean_object* v_toQFn_x3f_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1862_; 
v_v_1824_ = lean_array_fget(v_semirings_1808_, v___y_1801_);
v_toSemiring_1825_ = lean_ctor_get(v_v_1824_, 0);
v_ringId_1826_ = lean_ctor_get(v_v_1824_, 1);
v_commSemiringInst_1827_ = lean_ctor_get(v_v_1824_, 2);
v_addRightCancelInst_x3f_1828_ = lean_ctor_get(v_v_1824_, 3);
v_toQFn_x3f_1829_ = lean_ctor_get(v_v_1824_, 4);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_v_1824_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1831_ = v_v_1824_;
v_isShared_1832_ = v_isSharedCheck_1862_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_toQFn_x3f_1829_);
lean_inc(v_addRightCancelInst_x3f_1828_);
lean_inc(v_commSemiringInst_1827_);
lean_inc(v_ringId_1826_);
lean_inc(v_toSemiring_1825_);
lean_dec(v_v_1824_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1862_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_id_1833_; lean_object* v_type_1834_; lean_object* v_u_1835_; lean_object* v_semiringInst_1836_; lean_object* v_addFn_x3f_1837_; lean_object* v_mulFn_x3f_1838_; lean_object* v_powFn_x3f_1839_; lean_object* v_natCastFn_x3f_1840_; lean_object* v_denote_1841_; lean_object* v_vars_1842_; lean_object* v_varMap_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1861_; 
v_id_1833_ = lean_ctor_get(v_toSemiring_1825_, 0);
v_type_1834_ = lean_ctor_get(v_toSemiring_1825_, 1);
v_u_1835_ = lean_ctor_get(v_toSemiring_1825_, 2);
v_semiringInst_1836_ = lean_ctor_get(v_toSemiring_1825_, 3);
v_addFn_x3f_1837_ = lean_ctor_get(v_toSemiring_1825_, 4);
v_mulFn_x3f_1838_ = lean_ctor_get(v_toSemiring_1825_, 5);
v_powFn_x3f_1839_ = lean_ctor_get(v_toSemiring_1825_, 6);
v_natCastFn_x3f_1840_ = lean_ctor_get(v_toSemiring_1825_, 7);
v_denote_1841_ = lean_ctor_get(v_toSemiring_1825_, 8);
v_vars_1842_ = lean_ctor_get(v_toSemiring_1825_, 9);
v_varMap_1843_ = lean_ctor_get(v_toSemiring_1825_, 10);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_toSemiring_1825_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1845_ = v_toSemiring_1825_;
v_isShared_1846_ = v_isSharedCheck_1861_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_varMap_1843_);
lean_inc(v_vars_1842_);
lean_inc(v_denote_1841_);
lean_inc(v_natCastFn_x3f_1840_);
lean_inc(v_powFn_x3f_1839_);
lean_inc(v_mulFn_x3f_1838_);
lean_inc(v_addFn_x3f_1837_);
lean_inc(v_semiringInst_1836_);
lean_inc(v_u_1835_);
lean_inc(v_type_1834_);
lean_inc(v_id_1833_);
lean_dec(v_toSemiring_1825_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1861_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v_xs_x27_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1847_ = lean_box(0);
v_xs_x27_1848_ = lean_array_fset(v_semirings_1808_, v___y_1801_, v___x_1847_);
lean_inc_ref(v_e_1802_);
v___x_1849_ = l_Lean_PersistentArray_push___redArg(v_vars_1842_, v_e_1802_);
v___x_1850_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_varMap_1843_, v_e_1802_, v_size_1803_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 10, v___x_1850_);
lean_ctor_set(v___x_1845_, 9, v___x_1849_);
v___x_1852_ = v___x_1845_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_id_1833_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_type_1834_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_u_1835_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_semiringInst_1836_);
lean_ctor_set(v_reuseFailAlloc_1860_, 4, v_addFn_x3f_1837_);
lean_ctor_set(v_reuseFailAlloc_1860_, 5, v_mulFn_x3f_1838_);
lean_ctor_set(v_reuseFailAlloc_1860_, 6, v_powFn_x3f_1839_);
lean_ctor_set(v_reuseFailAlloc_1860_, 7, v_natCastFn_x3f_1840_);
lean_ctor_set(v_reuseFailAlloc_1860_, 8, v_denote_1841_);
lean_ctor_set(v_reuseFailAlloc_1860_, 9, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1860_, 10, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1852_);
v___x_1854_ = v___x_1831_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_ringId_1826_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_commSemiringInst_1827_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_addRightCancelInst_x3f_1828_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_toQFn_x3f_1829_);
v___x_1854_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = lean_array_fset(v_xs_x27_1848_, v___y_1801_, v___x_1854_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 3, v___x_1855_);
v___x_1857_ = v___x_1822_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_rings_1805_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_typeIdOf_1806_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_exprToRingId_1807_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_stypeIdOf_1809_);
lean_ctor_set(v_reuseFailAlloc_1858_, 5, v_exprToSemiringId_1810_);
lean_ctor_set(v_reuseFailAlloc_1858_, 6, v_ncRings_1811_);
lean_ctor_set(v_reuseFailAlloc_1858_, 7, v_exprToNCRingId_1812_);
lean_ctor_set(v_reuseFailAlloc_1858_, 8, v_nctypeIdOf_1813_);
lean_ctor_set(v_reuseFailAlloc_1858_, 9, v_ncSemirings_1814_);
lean_ctor_set(v_reuseFailAlloc_1858_, 10, v_exprToNCSemiringId_1815_);
lean_ctor_set(v_reuseFailAlloc_1858_, 11, v_ncstypeIdOf_1816_);
lean_ctor_set(v_reuseFailAlloc_1858_, 12, v_steps_1817_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1818_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed(lean_object* v___y_1877_, lean_object* v_e_1878_, lean_object* v_size_1879_, lean_object* v_s_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(v___y_1877_, v_e_1878_, v_size_1879_, v_s_1880_);
lean_dec(v___y_1877_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(lean_object* v_e_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1946_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1946_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1946_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_toSemiring_1900_; lean_object* v_vars_1901_; lean_object* v_varMap_1902_; lean_object* v___x_1903_; 
v_toSemiring_1900_ = lean_ctor_get(v_a_1896_, 0);
lean_inc_ref(v_toSemiring_1900_);
lean_dec(v_a_1896_);
v_vars_1901_ = lean_ctor_get(v_toSemiring_1900_, 9);
lean_inc_ref(v_vars_1901_);
v_varMap_1902_ = lean_ctor_get(v_toSemiring_1900_, 10);
lean_inc_ref(v_varMap_1902_);
lean_dec_ref(v_toSemiring_1900_);
v___x_1903_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_varMap_1902_, v_e_1882_);
lean_dec_ref(v_varMap_1902_);
if (lean_obj_tag(v___x_1903_) == 1)
{
lean_object* v_val_1904_; lean_object* v___x_1906_; 
lean_dec_ref(v_vars_1901_);
lean_dec_ref(v_e_1882_);
v_val_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_val_1904_);
lean_dec_ref_known(v___x_1903_, 1);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v_val_1904_);
v___x_1906_ = v___x_1898_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_val_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
else
{
lean_object* v_size_1908_; lean_object* v___f_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_dec(v___x_1903_);
lean_del_object(v___x_1898_);
v_size_1908_ = lean_ctor_get(v_vars_1901_, 2);
lean_inc_n(v_size_1908_, 2);
lean_dec_ref(v_vars_1901_);
lean_inc_ref(v_e_1882_);
lean_inc(v___y_1883_);
v___f_1909_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1909_, 0, v___y_1883_);
lean_closure_set(v___f_1909_, 1, v_e_1882_);
lean_closure_set(v___f_1909_, 2, v_size_1908_);
v___x_1910_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1911_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1910_, v___f_1909_, v___y_1884_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v___x_1912_; 
lean_dec_ref_known(v___x_1911_, 1);
lean_inc_ref(v_e_1882_);
v___x_1912_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1882_, v___y_1883_, v___y_1884_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v___x_1913_; 
lean_dec_ref_known(v___x_1912_, 1);
v___x_1913_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1910_, v_e_1882_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; 
v_unused_1921_ = lean_ctor_get(v___x_1913_, 0);
lean_dec(v_unused_1921_);
v___x_1915_ = v___x_1913_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_dec(v___x_1913_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v_size_1908_);
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_size_1908_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_size_1908_);
v_a_1922_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1913_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1913_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_size_1908_);
lean_dec_ref(v_e_1882_);
v_a_1930_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1912_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1912_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_size_1908_);
lean_dec_ref(v_e_1882_);
v_a_1938_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1911_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1911_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v_e_1882_);
v_a_1947_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1895_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1895_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___boxed(lean_object* v_e_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v___y_1956_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object* v_e_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar___boxed(lean_object* v_e_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVar(v_e_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec(v_a_1984_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object* v_a_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_nat_to_int(v_a_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object* v_msg_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v___f_2014_; lean_object* v___x_40218__overap_2015_; lean_object* v___x_2016_; 
v___x_2013_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0);
v___f_2014_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2014_, 0, v___x_2013_);
v___x_40218__overap_2015_ = lean_panic_fn_borrowed(v___f_2014_, v_msg_2000_);
lean_dec_ref(v___f_2014_);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2008_);
lean_inc(v___y_2007_);
lean_inc_ref(v___y_2006_);
lean_inc(v___y_2005_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc(v___y_2002_);
lean_inc(v___y_2001_);
v___x_2016_ = lean_apply_12(v___x_40218__overap_2015_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, lean_box(0));
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object* v_msg_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_msg_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec(v___y_2018_);
return v_res_2030_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0));
v___x_2033_ = l_Lean_stringToMessageData(v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(lean_object* v_type_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___x_2041_; 
lean_inc_ref(v_type_2034_);
v___x_2041_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2054_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2054_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2054_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
if (lean_obj_tag(v_a_2042_) == 1)
{
lean_object* v_val_2046_; lean_object* v___x_2048_; 
lean_dec_ref(v_type_2034_);
v_val_2046_ = lean_ctor_get(v_a_2042_, 0);
lean_inc(v_val_2046_);
lean_dec_ref_known(v_a_2042_, 1);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v_val_2046_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_val_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_del_object(v___x_2044_);
lean_dec(v_a_2042_);
v___x_2050_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1);
v___x_2051_ = l_Lean_indentExpr(v_type_2034_);
v___x_2052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v___x_2053_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_2052_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
return v___x_2053_;
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref(v_type_2034_);
v_a_2055_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2041_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2041_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_type_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(lean_object* v_type_2071_, lean_object* v_u_2072_, lean_object* v_instDeclName_2073_, lean_object* v_declName_2074_, lean_object* v_expectedInst_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2088_ = lean_box(0);
lean_inc_n(v_u_2072_, 2);
v___x_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2089_, 0, v_u_2072_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2090_, 0, v_u_2072_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
v___x_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2091_, 0, v_u_2072_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
lean_inc_ref(v___x_2091_);
v___x_2092_ = l_Lean_mkConst(v_instDeclName_2073_, v___x_2091_);
lean_inc_ref_n(v_type_2071_, 3);
v___x_2093_ = l_Lean_mkApp3(v___x_2092_, v_type_2071_, v_type_2071_, v_type_2071_);
v___x_2094_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2093_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc_n(v_a_2095_, 2);
lean_dec_ref_known(v___x_2094_, 1);
lean_inc(v_declName_2074_);
v___x_2096_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2074_, v_a_2095_, v_expectedInst_2075_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec_ref_known(v___x_2096_, 1);
v___x_2097_ = l_Lean_mkConst(v_declName_2074_, v___x_2091_);
lean_inc_ref_n(v_type_2071_, 2);
v___x_2098_ = l_Lean_mkApp4(v___x_2097_, v_type_2071_, v_type_2071_, v_type_2071_, v_a_2095_);
v___x_2099_ = l_Lean_Meta_Sym_canon(v___x_2098_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = l_Lean_Meta_Sym_shareCommon(v_a_2100_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
return v___x_2101_;
}
else
{
return v___x_2099_;
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_a_2095_);
lean_dec_ref_known(v___x_2091_, 2);
lean_dec(v_declName_2074_);
lean_dec_ref(v_type_2071_);
v_a_2102_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2096_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2096_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2091_, 2);
lean_dec_ref(v_expectedInst_2075_);
lean_dec(v_declName_2074_);
lean_dec_ref(v_type_2071_);
return v___x_2094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_type_2110_ = _args[0];
lean_object* v_u_2111_ = _args[1];
lean_object* v_instDeclName_2112_ = _args[2];
lean_object* v_declName_2113_ = _args[3];
lean_object* v_expectedInst_2114_ = _args[4];
lean_object* v___y_2115_ = _args[5];
lean_object* v___y_2116_ = _args[6];
lean_object* v___y_2117_ = _args[7];
lean_object* v___y_2118_ = _args[8];
lean_object* v___y_2119_ = _args[9];
lean_object* v___y_2120_ = _args[10];
lean_object* v___y_2121_ = _args[11];
lean_object* v___y_2122_ = _args[12];
lean_object* v___y_2123_ = _args[13];
lean_object* v___y_2124_ = _args[14];
lean_object* v___y_2125_ = _args[15];
lean_object* v___y_2126_ = _args[16];
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2110_, v_u_2111_, v_instDeclName_2112_, v_declName_2113_, v_expectedInst_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec(v___y_2115_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object* v_a_2128_, lean_object* v_s_2129_){
_start:
{
lean_object* v_toRing_2130_; lean_object* v_invFn_x3f_2131_; lean_object* v_semiringId_x3f_2132_; lean_object* v_commSemiringInst_2133_; lean_object* v_commRingInst_2134_; lean_object* v_noZeroDivInst_x3f_2135_; lean_object* v_fieldInst_x3f_2136_; lean_object* v_powIdentityInst_x3f_2137_; lean_object* v_denoteEntries_2138_; lean_object* v_nextId_2139_; lean_object* v_steps_2140_; lean_object* v_queue_2141_; lean_object* v_basis_2142_; lean_object* v_diseqs_2143_; uint8_t v_recheck_2144_; lean_object* v_invSet_2145_; lean_object* v_powIdentityVarCount_2146_; lean_object* v_numEq0_x3f_2147_; uint8_t v_numEq0Updated_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2180_; 
v_toRing_2130_ = lean_ctor_get(v_s_2129_, 0);
v_invFn_x3f_2131_ = lean_ctor_get(v_s_2129_, 1);
v_semiringId_x3f_2132_ = lean_ctor_get(v_s_2129_, 2);
v_commSemiringInst_2133_ = lean_ctor_get(v_s_2129_, 3);
v_commRingInst_2134_ = lean_ctor_get(v_s_2129_, 4);
v_noZeroDivInst_x3f_2135_ = lean_ctor_get(v_s_2129_, 5);
v_fieldInst_x3f_2136_ = lean_ctor_get(v_s_2129_, 6);
v_powIdentityInst_x3f_2137_ = lean_ctor_get(v_s_2129_, 7);
v_denoteEntries_2138_ = lean_ctor_get(v_s_2129_, 8);
v_nextId_2139_ = lean_ctor_get(v_s_2129_, 9);
v_steps_2140_ = lean_ctor_get(v_s_2129_, 10);
v_queue_2141_ = lean_ctor_get(v_s_2129_, 11);
v_basis_2142_ = lean_ctor_get(v_s_2129_, 12);
v_diseqs_2143_ = lean_ctor_get(v_s_2129_, 13);
v_recheck_2144_ = lean_ctor_get_uint8(v_s_2129_, sizeof(void*)*17);
v_invSet_2145_ = lean_ctor_get(v_s_2129_, 14);
v_powIdentityVarCount_2146_ = lean_ctor_get(v_s_2129_, 15);
v_numEq0_x3f_2147_ = lean_ctor_get(v_s_2129_, 16);
v_numEq0Updated_2148_ = lean_ctor_get_uint8(v_s_2129_, sizeof(void*)*17 + 1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_s_2129_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2150_ = v_s_2129_;
v_isShared_2151_ = v_isSharedCheck_2180_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_numEq0_x3f_2147_);
lean_inc(v_powIdentityVarCount_2146_);
lean_inc(v_invSet_2145_);
lean_inc(v_diseqs_2143_);
lean_inc(v_basis_2142_);
lean_inc(v_queue_2141_);
lean_inc(v_steps_2140_);
lean_inc(v_nextId_2139_);
lean_inc(v_denoteEntries_2138_);
lean_inc(v_powIdentityInst_x3f_2137_);
lean_inc(v_fieldInst_x3f_2136_);
lean_inc(v_noZeroDivInst_x3f_2135_);
lean_inc(v_commRingInst_2134_);
lean_inc(v_commSemiringInst_2133_);
lean_inc(v_semiringId_x3f_2132_);
lean_inc(v_invFn_x3f_2131_);
lean_inc(v_toRing_2130_);
lean_dec(v_s_2129_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2180_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v_id_2152_; lean_object* v_type_2153_; lean_object* v_u_2154_; lean_object* v_ringInst_2155_; lean_object* v_semiringInst_2156_; lean_object* v_charInst_x3f_2157_; lean_object* v_addFn_x3f_2158_; lean_object* v_subFn_x3f_2159_; lean_object* v_negFn_x3f_2160_; lean_object* v_powFn_x3f_2161_; lean_object* v_intCastFn_x3f_2162_; lean_object* v_natCastFn_x3f_2163_; lean_object* v_one_x3f_2164_; lean_object* v_vars_2165_; lean_object* v_varMap_2166_; lean_object* v_denote_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2178_; 
v_id_2152_ = lean_ctor_get(v_toRing_2130_, 0);
v_type_2153_ = lean_ctor_get(v_toRing_2130_, 1);
v_u_2154_ = lean_ctor_get(v_toRing_2130_, 2);
v_ringInst_2155_ = lean_ctor_get(v_toRing_2130_, 3);
v_semiringInst_2156_ = lean_ctor_get(v_toRing_2130_, 4);
v_charInst_x3f_2157_ = lean_ctor_get(v_toRing_2130_, 5);
v_addFn_x3f_2158_ = lean_ctor_get(v_toRing_2130_, 6);
v_subFn_x3f_2159_ = lean_ctor_get(v_toRing_2130_, 8);
v_negFn_x3f_2160_ = lean_ctor_get(v_toRing_2130_, 9);
v_powFn_x3f_2161_ = lean_ctor_get(v_toRing_2130_, 10);
v_intCastFn_x3f_2162_ = lean_ctor_get(v_toRing_2130_, 11);
v_natCastFn_x3f_2163_ = lean_ctor_get(v_toRing_2130_, 12);
v_one_x3f_2164_ = lean_ctor_get(v_toRing_2130_, 13);
v_vars_2165_ = lean_ctor_get(v_toRing_2130_, 14);
v_varMap_2166_ = lean_ctor_get(v_toRing_2130_, 15);
v_denote_2167_ = lean_ctor_get(v_toRing_2130_, 16);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_toRing_2130_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; 
v_unused_2179_ = lean_ctor_get(v_toRing_2130_, 7);
lean_dec(v_unused_2179_);
v___x_2169_ = v_toRing_2130_;
v_isShared_2170_ = v_isSharedCheck_2178_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_denote_2167_);
lean_inc(v_varMap_2166_);
lean_inc(v_vars_2165_);
lean_inc(v_one_x3f_2164_);
lean_inc(v_natCastFn_x3f_2163_);
lean_inc(v_intCastFn_x3f_2162_);
lean_inc(v_powFn_x3f_2161_);
lean_inc(v_negFn_x3f_2160_);
lean_inc(v_subFn_x3f_2159_);
lean_inc(v_addFn_x3f_2158_);
lean_inc(v_charInst_x3f_2157_);
lean_inc(v_semiringInst_2156_);
lean_inc(v_ringInst_2155_);
lean_inc(v_u_2154_);
lean_inc(v_type_2153_);
lean_inc(v_id_2152_);
lean_dec(v_toRing_2130_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2178_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2171_, 0, v_a_2128_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 7, v___x_2171_);
v___x_2173_ = v___x_2169_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_id_2152_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_type_2153_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_u_2154_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_ringInst_2155_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v_semiringInst_2156_);
lean_ctor_set(v_reuseFailAlloc_2177_, 5, v_charInst_x3f_2157_);
lean_ctor_set(v_reuseFailAlloc_2177_, 6, v_addFn_x3f_2158_);
lean_ctor_set(v_reuseFailAlloc_2177_, 7, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2177_, 8, v_subFn_x3f_2159_);
lean_ctor_set(v_reuseFailAlloc_2177_, 9, v_negFn_x3f_2160_);
lean_ctor_set(v_reuseFailAlloc_2177_, 10, v_powFn_x3f_2161_);
lean_ctor_set(v_reuseFailAlloc_2177_, 11, v_intCastFn_x3f_2162_);
lean_ctor_set(v_reuseFailAlloc_2177_, 12, v_natCastFn_x3f_2163_);
lean_ctor_set(v_reuseFailAlloc_2177_, 13, v_one_x3f_2164_);
lean_ctor_set(v_reuseFailAlloc_2177_, 14, v_vars_2165_);
lean_ctor_set(v_reuseFailAlloc_2177_, 15, v_varMap_2166_);
lean_ctor_set(v_reuseFailAlloc_2177_, 16, v_denote_2167_);
v___x_2173_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2173_);
v___x_2175_ = v___x_2150_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_invFn_x3f_2131_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_semiringId_x3f_2132_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v_commSemiringInst_2133_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v_commRingInst_2134_);
lean_ctor_set(v_reuseFailAlloc_2176_, 5, v_noZeroDivInst_x3f_2135_);
lean_ctor_set(v_reuseFailAlloc_2176_, 6, v_fieldInst_x3f_2136_);
lean_ctor_set(v_reuseFailAlloc_2176_, 7, v_powIdentityInst_x3f_2137_);
lean_ctor_set(v_reuseFailAlloc_2176_, 8, v_denoteEntries_2138_);
lean_ctor_set(v_reuseFailAlloc_2176_, 9, v_nextId_2139_);
lean_ctor_set(v_reuseFailAlloc_2176_, 10, v_steps_2140_);
lean_ctor_set(v_reuseFailAlloc_2176_, 11, v_queue_2141_);
lean_ctor_set(v_reuseFailAlloc_2176_, 12, v_basis_2142_);
lean_ctor_set(v_reuseFailAlloc_2176_, 13, v_diseqs_2143_);
lean_ctor_set(v_reuseFailAlloc_2176_, 14, v_invSet_2145_);
lean_ctor_set(v_reuseFailAlloc_2176_, 15, v_powIdentityVarCount_2146_);
lean_ctor_set(v_reuseFailAlloc_2176_, 16, v_numEq0_x3f_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2176_, sizeof(void*)*17, v_recheck_2144_);
lean_ctor_set_uint8(v_reuseFailAlloc_2176_, sizeof(void*)*17 + 1, v_numEq0Updated_2148_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2237_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2196_ = v___x_2193_;
v_isShared_2197_ = v_isSharedCheck_2237_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2237_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v_toRing_2198_; lean_object* v_mulFn_x3f_2199_; 
v_toRing_2198_ = lean_ctor_get(v_a_2194_, 0);
lean_inc_ref(v_toRing_2198_);
lean_dec(v_a_2194_);
v_mulFn_x3f_2199_ = lean_ctor_get(v_toRing_2198_, 7);
if (lean_obj_tag(v_mulFn_x3f_2199_) == 1)
{
lean_object* v_val_2200_; lean_object* v___x_2202_; 
lean_inc_ref(v_mulFn_x3f_2199_);
lean_dec_ref(v_toRing_2198_);
v_val_2200_ = lean_ctor_get(v_mulFn_x3f_2199_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v_mulFn_x3f_2199_, 1);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v_val_2200_);
v___x_2202_ = v___x_2196_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_val_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
else
{
lean_object* v_type_2204_; lean_object* v_u_2205_; lean_object* v_semiringInst_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v_expectedInst_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_del_object(v___x_2196_);
v_type_2204_ = lean_ctor_get(v_toRing_2198_, 1);
lean_inc_ref_n(v_type_2204_, 3);
v_u_2205_ = lean_ctor_get(v_toRing_2198_, 2);
lean_inc_n(v_u_2205_, 2);
v_semiringInst_2206_ = lean_ctor_get(v_toRing_2198_, 4);
lean_inc_ref(v_semiringInst_2206_);
lean_dec_ref(v_toRing_2198_);
v___x_2207_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_2208_ = lean_box(0);
v___x_2209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2209_, 0, v_u_2205_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
lean_inc_ref(v___x_2209_);
v___x_2210_ = l_Lean_mkConst(v___x_2207_, v___x_2209_);
v___x_2211_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_2212_ = l_Lean_mkConst(v___x_2211_, v___x_2209_);
v___x_2213_ = l_Lean_mkAppB(v___x_2212_, v_type_2204_, v_semiringInst_2206_);
v_expectedInst_2214_ = l_Lean_mkAppB(v___x_2210_, v_type_2204_, v___x_2213_);
v___x_2215_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_2216_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_2217_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2204_, v_u_2205_, v___x_2215_, v___x_2216_, v_expectedInst_2214_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___f_2219_; lean_object* v___x_2220_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc_n(v_a_2218_, 2);
lean_dec_ref_known(v___x_2217_, 1);
v___f_2219_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2219_, 0, v_a_2218_);
v___x_2220_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2219_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; 
v_unused_2228_ = lean_ctor_get(v___x_2220_, 0);
lean_dec(v_unused_2228_);
v___x_2222_ = v___x_2220_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_dec(v___x_2220_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v_a_2218_);
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2218_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec(v_a_2218_);
v_a_2229_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2220_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2220_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
else
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
v_a_2238_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2193_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2193_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec(v___y_2246_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object* v_a_2259_, lean_object* v_s_2260_){
_start:
{
lean_object* v_toRing_2261_; lean_object* v_invFn_x3f_2262_; lean_object* v_semiringId_x3f_2263_; lean_object* v_commSemiringInst_2264_; lean_object* v_commRingInst_2265_; lean_object* v_noZeroDivInst_x3f_2266_; lean_object* v_fieldInst_x3f_2267_; lean_object* v_powIdentityInst_x3f_2268_; lean_object* v_denoteEntries_2269_; lean_object* v_nextId_2270_; lean_object* v_steps_2271_; lean_object* v_queue_2272_; lean_object* v_basis_2273_; lean_object* v_diseqs_2274_; uint8_t v_recheck_2275_; lean_object* v_invSet_2276_; lean_object* v_powIdentityVarCount_2277_; lean_object* v_numEq0_x3f_2278_; uint8_t v_numEq0Updated_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2311_; 
v_toRing_2261_ = lean_ctor_get(v_s_2260_, 0);
v_invFn_x3f_2262_ = lean_ctor_get(v_s_2260_, 1);
v_semiringId_x3f_2263_ = lean_ctor_get(v_s_2260_, 2);
v_commSemiringInst_2264_ = lean_ctor_get(v_s_2260_, 3);
v_commRingInst_2265_ = lean_ctor_get(v_s_2260_, 4);
v_noZeroDivInst_x3f_2266_ = lean_ctor_get(v_s_2260_, 5);
v_fieldInst_x3f_2267_ = lean_ctor_get(v_s_2260_, 6);
v_powIdentityInst_x3f_2268_ = lean_ctor_get(v_s_2260_, 7);
v_denoteEntries_2269_ = lean_ctor_get(v_s_2260_, 8);
v_nextId_2270_ = lean_ctor_get(v_s_2260_, 9);
v_steps_2271_ = lean_ctor_get(v_s_2260_, 10);
v_queue_2272_ = lean_ctor_get(v_s_2260_, 11);
v_basis_2273_ = lean_ctor_get(v_s_2260_, 12);
v_diseqs_2274_ = lean_ctor_get(v_s_2260_, 13);
v_recheck_2275_ = lean_ctor_get_uint8(v_s_2260_, sizeof(void*)*17);
v_invSet_2276_ = lean_ctor_get(v_s_2260_, 14);
v_powIdentityVarCount_2277_ = lean_ctor_get(v_s_2260_, 15);
v_numEq0_x3f_2278_ = lean_ctor_get(v_s_2260_, 16);
v_numEq0Updated_2279_ = lean_ctor_get_uint8(v_s_2260_, sizeof(void*)*17 + 1);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_s_2260_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2281_ = v_s_2260_;
v_isShared_2282_ = v_isSharedCheck_2311_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_numEq0_x3f_2278_);
lean_inc(v_powIdentityVarCount_2277_);
lean_inc(v_invSet_2276_);
lean_inc(v_diseqs_2274_);
lean_inc(v_basis_2273_);
lean_inc(v_queue_2272_);
lean_inc(v_steps_2271_);
lean_inc(v_nextId_2270_);
lean_inc(v_denoteEntries_2269_);
lean_inc(v_powIdentityInst_x3f_2268_);
lean_inc(v_fieldInst_x3f_2267_);
lean_inc(v_noZeroDivInst_x3f_2266_);
lean_inc(v_commRingInst_2265_);
lean_inc(v_commSemiringInst_2264_);
lean_inc(v_semiringId_x3f_2263_);
lean_inc(v_invFn_x3f_2262_);
lean_inc(v_toRing_2261_);
lean_dec(v_s_2260_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2311_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v_id_2283_; lean_object* v_type_2284_; lean_object* v_u_2285_; lean_object* v_ringInst_2286_; lean_object* v_semiringInst_2287_; lean_object* v_charInst_x3f_2288_; lean_object* v_mulFn_x3f_2289_; lean_object* v_subFn_x3f_2290_; lean_object* v_negFn_x3f_2291_; lean_object* v_powFn_x3f_2292_; lean_object* v_intCastFn_x3f_2293_; lean_object* v_natCastFn_x3f_2294_; lean_object* v_one_x3f_2295_; lean_object* v_vars_2296_; lean_object* v_varMap_2297_; lean_object* v_denote_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2309_; 
v_id_2283_ = lean_ctor_get(v_toRing_2261_, 0);
v_type_2284_ = lean_ctor_get(v_toRing_2261_, 1);
v_u_2285_ = lean_ctor_get(v_toRing_2261_, 2);
v_ringInst_2286_ = lean_ctor_get(v_toRing_2261_, 3);
v_semiringInst_2287_ = lean_ctor_get(v_toRing_2261_, 4);
v_charInst_x3f_2288_ = lean_ctor_get(v_toRing_2261_, 5);
v_mulFn_x3f_2289_ = lean_ctor_get(v_toRing_2261_, 7);
v_subFn_x3f_2290_ = lean_ctor_get(v_toRing_2261_, 8);
v_negFn_x3f_2291_ = lean_ctor_get(v_toRing_2261_, 9);
v_powFn_x3f_2292_ = lean_ctor_get(v_toRing_2261_, 10);
v_intCastFn_x3f_2293_ = lean_ctor_get(v_toRing_2261_, 11);
v_natCastFn_x3f_2294_ = lean_ctor_get(v_toRing_2261_, 12);
v_one_x3f_2295_ = lean_ctor_get(v_toRing_2261_, 13);
v_vars_2296_ = lean_ctor_get(v_toRing_2261_, 14);
v_varMap_2297_ = lean_ctor_get(v_toRing_2261_, 15);
v_denote_2298_ = lean_ctor_get(v_toRing_2261_, 16);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_toRing_2261_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; 
v_unused_2310_ = lean_ctor_get(v_toRing_2261_, 6);
lean_dec(v_unused_2310_);
v___x_2300_ = v_toRing_2261_;
v_isShared_2301_ = v_isSharedCheck_2309_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_denote_2298_);
lean_inc(v_varMap_2297_);
lean_inc(v_vars_2296_);
lean_inc(v_one_x3f_2295_);
lean_inc(v_natCastFn_x3f_2294_);
lean_inc(v_intCastFn_x3f_2293_);
lean_inc(v_powFn_x3f_2292_);
lean_inc(v_negFn_x3f_2291_);
lean_inc(v_subFn_x3f_2290_);
lean_inc(v_mulFn_x3f_2289_);
lean_inc(v_charInst_x3f_2288_);
lean_inc(v_semiringInst_2287_);
lean_inc(v_ringInst_2286_);
lean_inc(v_u_2285_);
lean_inc(v_type_2284_);
lean_inc(v_id_2283_);
lean_dec(v_toRing_2261_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2309_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2302_, 0, v_a_2259_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 6, v___x_2302_);
v___x_2304_ = v___x_2300_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_id_2283_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_type_2284_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_u_2285_);
lean_ctor_set(v_reuseFailAlloc_2308_, 3, v_ringInst_2286_);
lean_ctor_set(v_reuseFailAlloc_2308_, 4, v_semiringInst_2287_);
lean_ctor_set(v_reuseFailAlloc_2308_, 5, v_charInst_x3f_2288_);
lean_ctor_set(v_reuseFailAlloc_2308_, 6, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2308_, 7, v_mulFn_x3f_2289_);
lean_ctor_set(v_reuseFailAlloc_2308_, 8, v_subFn_x3f_2290_);
lean_ctor_set(v_reuseFailAlloc_2308_, 9, v_negFn_x3f_2291_);
lean_ctor_set(v_reuseFailAlloc_2308_, 10, v_powFn_x3f_2292_);
lean_ctor_set(v_reuseFailAlloc_2308_, 11, v_intCastFn_x3f_2293_);
lean_ctor_set(v_reuseFailAlloc_2308_, 12, v_natCastFn_x3f_2294_);
lean_ctor_set(v_reuseFailAlloc_2308_, 13, v_one_x3f_2295_);
lean_ctor_set(v_reuseFailAlloc_2308_, 14, v_vars_2296_);
lean_ctor_set(v_reuseFailAlloc_2308_, 15, v_varMap_2297_);
lean_ctor_set(v_reuseFailAlloc_2308_, 16, v_denote_2298_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2306_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2304_);
v___x_2306_ = v___x_2281_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_invFn_x3f_2262_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_semiringId_x3f_2263_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v_commSemiringInst_2264_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v_commRingInst_2265_);
lean_ctor_set(v_reuseFailAlloc_2307_, 5, v_noZeroDivInst_x3f_2266_);
lean_ctor_set(v_reuseFailAlloc_2307_, 6, v_fieldInst_x3f_2267_);
lean_ctor_set(v_reuseFailAlloc_2307_, 7, v_powIdentityInst_x3f_2268_);
lean_ctor_set(v_reuseFailAlloc_2307_, 8, v_denoteEntries_2269_);
lean_ctor_set(v_reuseFailAlloc_2307_, 9, v_nextId_2270_);
lean_ctor_set(v_reuseFailAlloc_2307_, 10, v_steps_2271_);
lean_ctor_set(v_reuseFailAlloc_2307_, 11, v_queue_2272_);
lean_ctor_set(v_reuseFailAlloc_2307_, 12, v_basis_2273_);
lean_ctor_set(v_reuseFailAlloc_2307_, 13, v_diseqs_2274_);
lean_ctor_set(v_reuseFailAlloc_2307_, 14, v_invSet_2276_);
lean_ctor_set(v_reuseFailAlloc_2307_, 15, v_powIdentityVarCount_2277_);
lean_ctor_set(v_reuseFailAlloc_2307_, 16, v_numEq0_x3f_2278_);
lean_ctor_set_uint8(v_reuseFailAlloc_2307_, sizeof(void*)*17, v_recheck_2275_);
lean_ctor_set_uint8(v_reuseFailAlloc_2307_, sizeof(void*)*17 + 1, v_numEq0Updated_2279_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2368_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2368_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2368_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v_toRing_2329_; lean_object* v_addFn_x3f_2330_; 
v_toRing_2329_ = lean_ctor_get(v_a_2325_, 0);
lean_inc_ref(v_toRing_2329_);
lean_dec(v_a_2325_);
v_addFn_x3f_2330_ = lean_ctor_get(v_toRing_2329_, 6);
if (lean_obj_tag(v_addFn_x3f_2330_) == 1)
{
lean_object* v_val_2331_; lean_object* v___x_2333_; 
lean_inc_ref(v_addFn_x3f_2330_);
lean_dec_ref(v_toRing_2329_);
v_val_2331_ = lean_ctor_get(v_addFn_x3f_2330_, 0);
lean_inc(v_val_2331_);
lean_dec_ref_known(v_addFn_x3f_2330_, 1);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v_val_2331_);
v___x_2333_ = v___x_2327_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_val_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
else
{
lean_object* v_type_2335_; lean_object* v_u_2336_; lean_object* v_semiringInst_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v_expectedInst_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_del_object(v___x_2327_);
v_type_2335_ = lean_ctor_get(v_toRing_2329_, 1);
lean_inc_ref_n(v_type_2335_, 3);
v_u_2336_ = lean_ctor_get(v_toRing_2329_, 2);
lean_inc_n(v_u_2336_, 2);
v_semiringInst_2337_ = lean_ctor_get(v_toRing_2329_, 4);
lean_inc_ref(v_semiringInst_2337_);
lean_dec_ref(v_toRing_2329_);
v___x_2338_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_2339_ = lean_box(0);
v___x_2340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2340_, 0, v_u_2336_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
lean_inc_ref(v___x_2340_);
v___x_2341_ = l_Lean_mkConst(v___x_2338_, v___x_2340_);
v___x_2342_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_2343_ = l_Lean_mkConst(v___x_2342_, v___x_2340_);
v___x_2344_ = l_Lean_mkAppB(v___x_2343_, v_type_2335_, v_semiringInst_2337_);
v_expectedInst_2345_ = l_Lean_mkAppB(v___x_2341_, v_type_2335_, v___x_2344_);
v___x_2346_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_2347_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_2348_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2335_, v_u_2336_, v___x_2346_, v___x_2347_, v_expectedInst_2345_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___f_2350_; lean_object* v___x_2351_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc_n(v_a_2349_, 2);
lean_dec_ref_known(v___x_2348_, 1);
v___f_2350_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_2350_, 0, v_a_2349_);
v___x_2351_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2350_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v___x_2351_, 0);
lean_dec(v_unused_2359_);
v___x_2353_ = v___x_2351_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_dec(v___x_2351_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v_a_2349_);
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2349_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_a_2349_);
v_a_2360_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2351_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2351_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
return v___x_2348_;
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_a_2369_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2324_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2324_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec(v___y_2377_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(lean_object* v_type_2390_, lean_object* v_u_2391_, lean_object* v_instDeclName_2392_, lean_object* v_declName_2393_, lean_object* v_expectedInst_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2407_ = lean_box(0);
v___x_2408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2408_, 0, v_u_2391_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
lean_inc_ref(v___x_2408_);
v___x_2409_ = l_Lean_mkConst(v_instDeclName_2392_, v___x_2408_);
lean_inc_ref(v_type_2390_);
v___x_2410_ = l_Lean_Expr_app___override(v___x_2409_, v_type_2390_);
v___x_2411_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2410_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2413_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc_n(v_a_2412_, 2);
lean_dec_ref_known(v___x_2411_, 1);
lean_inc(v_declName_2393_);
v___x_2413_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2393_, v_a_2412_, v_expectedInst_2394_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
lean_dec_ref_known(v___x_2413_, 1);
v___x_2414_ = l_Lean_mkConst(v_declName_2393_, v___x_2408_);
v___x_2415_ = l_Lean_mkAppB(v___x_2414_, v_type_2390_, v_a_2412_);
v___x_2416_ = l_Lean_Meta_Sym_canon(v___x_2415_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2418_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2416_, 1);
v___x_2418_ = l_Lean_Meta_Sym_shareCommon(v_a_2417_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2418_;
}
else
{
return v___x_2416_;
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v_a_2412_);
lean_dec_ref_known(v___x_2408_, 2);
lean_dec(v_declName_2393_);
lean_dec_ref(v_type_2390_);
v_a_2419_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2413_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2413_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2408_, 2);
lean_dec_ref(v_expectedInst_2394_);
lean_dec(v_declName_2393_);
lean_dec_ref(v_type_2390_);
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_type_2427_ = _args[0];
lean_object* v_u_2428_ = _args[1];
lean_object* v_instDeclName_2429_ = _args[2];
lean_object* v_declName_2430_ = _args[3];
lean_object* v_expectedInst_2431_ = _args[4];
lean_object* v___y_2432_ = _args[5];
lean_object* v___y_2433_ = _args[6];
lean_object* v___y_2434_ = _args[7];
lean_object* v___y_2435_ = _args[8];
lean_object* v___y_2436_ = _args[9];
lean_object* v___y_2437_ = _args[10];
lean_object* v___y_2438_ = _args[11];
lean_object* v___y_2439_ = _args[12];
lean_object* v___y_2440_ = _args[13];
lean_object* v___y_2441_ = _args[14];
lean_object* v___y_2442_ = _args[15];
lean_object* v___y_2443_ = _args[16];
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2427_, v_u_2428_, v_instDeclName_2429_, v_declName_2430_, v_expectedInst_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec(v___y_2432_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object* v_a_2445_, lean_object* v_s_2446_){
_start:
{
lean_object* v_toRing_2447_; lean_object* v_invFn_x3f_2448_; lean_object* v_semiringId_x3f_2449_; lean_object* v_commSemiringInst_2450_; lean_object* v_commRingInst_2451_; lean_object* v_noZeroDivInst_x3f_2452_; lean_object* v_fieldInst_x3f_2453_; lean_object* v_powIdentityInst_x3f_2454_; lean_object* v_denoteEntries_2455_; lean_object* v_nextId_2456_; lean_object* v_steps_2457_; lean_object* v_queue_2458_; lean_object* v_basis_2459_; lean_object* v_diseqs_2460_; uint8_t v_recheck_2461_; lean_object* v_invSet_2462_; lean_object* v_powIdentityVarCount_2463_; lean_object* v_numEq0_x3f_2464_; uint8_t v_numEq0Updated_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2497_; 
v_toRing_2447_ = lean_ctor_get(v_s_2446_, 0);
v_invFn_x3f_2448_ = lean_ctor_get(v_s_2446_, 1);
v_semiringId_x3f_2449_ = lean_ctor_get(v_s_2446_, 2);
v_commSemiringInst_2450_ = lean_ctor_get(v_s_2446_, 3);
v_commRingInst_2451_ = lean_ctor_get(v_s_2446_, 4);
v_noZeroDivInst_x3f_2452_ = lean_ctor_get(v_s_2446_, 5);
v_fieldInst_x3f_2453_ = lean_ctor_get(v_s_2446_, 6);
v_powIdentityInst_x3f_2454_ = lean_ctor_get(v_s_2446_, 7);
v_denoteEntries_2455_ = lean_ctor_get(v_s_2446_, 8);
v_nextId_2456_ = lean_ctor_get(v_s_2446_, 9);
v_steps_2457_ = lean_ctor_get(v_s_2446_, 10);
v_queue_2458_ = lean_ctor_get(v_s_2446_, 11);
v_basis_2459_ = lean_ctor_get(v_s_2446_, 12);
v_diseqs_2460_ = lean_ctor_get(v_s_2446_, 13);
v_recheck_2461_ = lean_ctor_get_uint8(v_s_2446_, sizeof(void*)*17);
v_invSet_2462_ = lean_ctor_get(v_s_2446_, 14);
v_powIdentityVarCount_2463_ = lean_ctor_get(v_s_2446_, 15);
v_numEq0_x3f_2464_ = lean_ctor_get(v_s_2446_, 16);
v_numEq0Updated_2465_ = lean_ctor_get_uint8(v_s_2446_, sizeof(void*)*17 + 1);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_s_2446_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2467_ = v_s_2446_;
v_isShared_2468_ = v_isSharedCheck_2497_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_numEq0_x3f_2464_);
lean_inc(v_powIdentityVarCount_2463_);
lean_inc(v_invSet_2462_);
lean_inc(v_diseqs_2460_);
lean_inc(v_basis_2459_);
lean_inc(v_queue_2458_);
lean_inc(v_steps_2457_);
lean_inc(v_nextId_2456_);
lean_inc(v_denoteEntries_2455_);
lean_inc(v_powIdentityInst_x3f_2454_);
lean_inc(v_fieldInst_x3f_2453_);
lean_inc(v_noZeroDivInst_x3f_2452_);
lean_inc(v_commRingInst_2451_);
lean_inc(v_commSemiringInst_2450_);
lean_inc(v_semiringId_x3f_2449_);
lean_inc(v_invFn_x3f_2448_);
lean_inc(v_toRing_2447_);
lean_dec(v_s_2446_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2497_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v_id_2469_; lean_object* v_type_2470_; lean_object* v_u_2471_; lean_object* v_ringInst_2472_; lean_object* v_semiringInst_2473_; lean_object* v_charInst_x3f_2474_; lean_object* v_addFn_x3f_2475_; lean_object* v_mulFn_x3f_2476_; lean_object* v_subFn_x3f_2477_; lean_object* v_powFn_x3f_2478_; lean_object* v_intCastFn_x3f_2479_; lean_object* v_natCastFn_x3f_2480_; lean_object* v_one_x3f_2481_; lean_object* v_vars_2482_; lean_object* v_varMap_2483_; lean_object* v_denote_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2495_; 
v_id_2469_ = lean_ctor_get(v_toRing_2447_, 0);
v_type_2470_ = lean_ctor_get(v_toRing_2447_, 1);
v_u_2471_ = lean_ctor_get(v_toRing_2447_, 2);
v_ringInst_2472_ = lean_ctor_get(v_toRing_2447_, 3);
v_semiringInst_2473_ = lean_ctor_get(v_toRing_2447_, 4);
v_charInst_x3f_2474_ = lean_ctor_get(v_toRing_2447_, 5);
v_addFn_x3f_2475_ = lean_ctor_get(v_toRing_2447_, 6);
v_mulFn_x3f_2476_ = lean_ctor_get(v_toRing_2447_, 7);
v_subFn_x3f_2477_ = lean_ctor_get(v_toRing_2447_, 8);
v_powFn_x3f_2478_ = lean_ctor_get(v_toRing_2447_, 10);
v_intCastFn_x3f_2479_ = lean_ctor_get(v_toRing_2447_, 11);
v_natCastFn_x3f_2480_ = lean_ctor_get(v_toRing_2447_, 12);
v_one_x3f_2481_ = lean_ctor_get(v_toRing_2447_, 13);
v_vars_2482_ = lean_ctor_get(v_toRing_2447_, 14);
v_varMap_2483_ = lean_ctor_get(v_toRing_2447_, 15);
v_denote_2484_ = lean_ctor_get(v_toRing_2447_, 16);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_toRing_2447_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; 
v_unused_2496_ = lean_ctor_get(v_toRing_2447_, 9);
lean_dec(v_unused_2496_);
v___x_2486_ = v_toRing_2447_;
v_isShared_2487_ = v_isSharedCheck_2495_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_denote_2484_);
lean_inc(v_varMap_2483_);
lean_inc(v_vars_2482_);
lean_inc(v_one_x3f_2481_);
lean_inc(v_natCastFn_x3f_2480_);
lean_inc(v_intCastFn_x3f_2479_);
lean_inc(v_powFn_x3f_2478_);
lean_inc(v_subFn_x3f_2477_);
lean_inc(v_mulFn_x3f_2476_);
lean_inc(v_addFn_x3f_2475_);
lean_inc(v_charInst_x3f_2474_);
lean_inc(v_semiringInst_2473_);
lean_inc(v_ringInst_2472_);
lean_inc(v_u_2471_);
lean_inc(v_type_2470_);
lean_inc(v_id_2469_);
lean_dec(v_toRing_2447_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2495_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_a_2445_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 9, v___x_2488_);
v___x_2490_ = v___x_2486_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_id_2469_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_type_2470_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_u_2471_);
lean_ctor_set(v_reuseFailAlloc_2494_, 3, v_ringInst_2472_);
lean_ctor_set(v_reuseFailAlloc_2494_, 4, v_semiringInst_2473_);
lean_ctor_set(v_reuseFailAlloc_2494_, 5, v_charInst_x3f_2474_);
lean_ctor_set(v_reuseFailAlloc_2494_, 6, v_addFn_x3f_2475_);
lean_ctor_set(v_reuseFailAlloc_2494_, 7, v_mulFn_x3f_2476_);
lean_ctor_set(v_reuseFailAlloc_2494_, 8, v_subFn_x3f_2477_);
lean_ctor_set(v_reuseFailAlloc_2494_, 9, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2494_, 10, v_powFn_x3f_2478_);
lean_ctor_set(v_reuseFailAlloc_2494_, 11, v_intCastFn_x3f_2479_);
lean_ctor_set(v_reuseFailAlloc_2494_, 12, v_natCastFn_x3f_2480_);
lean_ctor_set(v_reuseFailAlloc_2494_, 13, v_one_x3f_2481_);
lean_ctor_set(v_reuseFailAlloc_2494_, 14, v_vars_2482_);
lean_ctor_set(v_reuseFailAlloc_2494_, 15, v_varMap_2483_);
lean_ctor_set(v_reuseFailAlloc_2494_, 16, v_denote_2484_);
v___x_2490_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2492_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v___x_2490_);
v___x_2492_ = v___x_2467_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_invFn_x3f_2448_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_semiringId_x3f_2449_);
lean_ctor_set(v_reuseFailAlloc_2493_, 3, v_commSemiringInst_2450_);
lean_ctor_set(v_reuseFailAlloc_2493_, 4, v_commRingInst_2451_);
lean_ctor_set(v_reuseFailAlloc_2493_, 5, v_noZeroDivInst_x3f_2452_);
lean_ctor_set(v_reuseFailAlloc_2493_, 6, v_fieldInst_x3f_2453_);
lean_ctor_set(v_reuseFailAlloc_2493_, 7, v_powIdentityInst_x3f_2454_);
lean_ctor_set(v_reuseFailAlloc_2493_, 8, v_denoteEntries_2455_);
lean_ctor_set(v_reuseFailAlloc_2493_, 9, v_nextId_2456_);
lean_ctor_set(v_reuseFailAlloc_2493_, 10, v_steps_2457_);
lean_ctor_set(v_reuseFailAlloc_2493_, 11, v_queue_2458_);
lean_ctor_set(v_reuseFailAlloc_2493_, 12, v_basis_2459_);
lean_ctor_set(v_reuseFailAlloc_2493_, 13, v_diseqs_2460_);
lean_ctor_set(v_reuseFailAlloc_2493_, 14, v_invSet_2462_);
lean_ctor_set(v_reuseFailAlloc_2493_, 15, v_powIdentityVarCount_2463_);
lean_ctor_set(v_reuseFailAlloc_2493_, 16, v_numEq0_x3f_2464_);
lean_ctor_set_uint8(v_reuseFailAlloc_2493_, sizeof(void*)*17, v_recheck_2461_);
lean_ctor_set_uint8(v_reuseFailAlloc_2493_, sizeof(void*)*17 + 1, v_numEq0Updated_2465_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2564_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2564_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2564_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v_toRing_2528_; lean_object* v_negFn_x3f_2529_; 
v_toRing_2528_ = lean_ctor_get(v_a_2524_, 0);
lean_inc_ref(v_toRing_2528_);
lean_dec(v_a_2524_);
v_negFn_x3f_2529_ = lean_ctor_get(v_toRing_2528_, 9);
if (lean_obj_tag(v_negFn_x3f_2529_) == 1)
{
lean_object* v_val_2530_; lean_object* v___x_2532_; 
lean_inc_ref(v_negFn_x3f_2529_);
lean_dec_ref(v_toRing_2528_);
v_val_2530_ = lean_ctor_get(v_negFn_x3f_2529_, 0);
lean_inc(v_val_2530_);
lean_dec_ref_known(v_negFn_x3f_2529_, 1);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v_val_2530_);
v___x_2532_ = v___x_2526_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_val_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
else
{
lean_object* v_type_2534_; lean_object* v_u_2535_; lean_object* v_ringInst_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v_expectedInst_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_del_object(v___x_2526_);
v_type_2534_ = lean_ctor_get(v_toRing_2528_, 1);
lean_inc_ref_n(v_type_2534_, 2);
v_u_2535_ = lean_ctor_get(v_toRing_2528_, 2);
lean_inc_n(v_u_2535_, 2);
v_ringInst_2536_ = lean_ctor_get(v_toRing_2528_, 3);
lean_inc_ref(v_ringInst_2536_);
lean_dec_ref(v_toRing_2528_);
v___x_2537_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1));
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2539_, 0, v_u_2535_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = l_Lean_mkConst(v___x_2537_, v___x_2539_);
v_expectedInst_2541_ = l_Lean_mkAppB(v___x_2540_, v_type_2534_, v_ringInst_2536_);
v___x_2542_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3));
v___x_2543_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5));
v___x_2544_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2534_, v_u_2535_, v___x_2542_, v___x_2543_, v_expectedInst_2541_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___f_2546_; lean_object* v___x_2547_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc_n(v_a_2545_, 2);
lean_dec_ref_known(v___x_2544_, 1);
v___f_2546_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_2546_, 0, v_a_2545_);
v___x_2547_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2546_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2554_ == 0)
{
lean_object* v_unused_2555_; 
v_unused_2555_ = lean_ctor_get(v___x_2547_, 0);
lean_dec(v_unused_2555_);
v___x_2549_ = v___x_2547_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_dec(v___x_2547_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v_a_2545_);
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2545_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v_a_2545_);
v_a_2556_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2547_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2547_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
else
{
return v___x_2544_;
}
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
v_a_2565_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2523_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2523_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v___y_2573_);
return v_res_2585_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_unsigned_to_nat(0u);
v___x_2594_ = lean_nat_to_int(v___x_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object* v_k_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v_toRing_2615_; lean_object* v_type_2616_; lean_object* v_u_2617_; lean_object* v_semiringInst_2618_; lean_object* v___x_2619_; lean_object* v_n_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2613_, 1);
v_toRing_2615_ = lean_ctor_get(v_a_2614_, 0);
lean_inc_ref(v_toRing_2615_);
lean_dec(v_a_2614_);
v_type_2616_ = lean_ctor_get(v_toRing_2615_, 1);
lean_inc_ref_n(v_type_2616_, 2);
v_u_2617_ = lean_ctor_get(v_toRing_2615_, 2);
lean_inc(v_u_2617_);
v_semiringInst_2618_ = lean_ctor_get(v_toRing_2615_, 4);
lean_inc_ref(v_semiringInst_2618_);
lean_dec_ref(v_toRing_2615_);
v___x_2619_ = lean_nat_abs(v_k_2600_);
v_n_2620_ = l_Lean_mkRawNatLit(v___x_2619_);
v___x_2621_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1));
v___x_2622_ = lean_box(0);
v___x_2623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2623_, 0, v_u_2617_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
lean_inc_ref(v___x_2623_);
v___x_2624_ = l_Lean_mkConst(v___x_2621_, v___x_2623_);
lean_inc_ref(v_n_2620_);
v___x_2625_ = l_Lean_mkAppB(v___x_2624_, v_type_2616_, v_n_2620_);
v___x_2626_ = lean_box(0);
v___x_2627_ = l_Lean_Meta_synthInstance_x3f(v___x_2625_, v___x_2626_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2667_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2630_ = v___x_2627_;
v_isShared_2631_ = v_isSharedCheck_2667_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2627_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2667_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v_ofNatInst_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; 
if (lean_obj_tag(v_a_2628_) == 1)
{
lean_object* v_val_2663_; 
lean_dec_ref(v_semiringInst_2618_);
v_val_2663_ = lean_ctor_get(v_a_2628_, 0);
lean_inc(v_val_2663_);
lean_dec_ref_known(v_a_2628_, 1);
v_ofNatInst_2633_ = v_val_2663_;
v___y_2634_ = v___y_2601_;
v___y_2635_ = v___y_2602_;
v___y_2636_ = v___y_2603_;
v___y_2637_ = v___y_2604_;
v___y_2638_ = v___y_2605_;
v___y_2639_ = v___y_2606_;
v___y_2640_ = v___y_2607_;
v___y_2641_ = v___y_2608_;
v___y_2642_ = v___y_2609_;
v___y_2643_ = v___y_2610_;
v___y_2644_ = v___y_2611_;
goto v___jp_2632_;
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_dec(v_a_2628_);
v___x_2664_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5));
lean_inc_ref(v___x_2623_);
v___x_2665_ = l_Lean_mkConst(v___x_2664_, v___x_2623_);
lean_inc_ref(v_n_2620_);
lean_inc_ref(v_type_2616_);
v___x_2666_ = l_Lean_mkApp3(v___x_2665_, v_type_2616_, v_semiringInst_2618_, v_n_2620_);
v_ofNatInst_2633_ = v___x_2666_;
v___y_2634_ = v___y_2601_;
v___y_2635_ = v___y_2602_;
v___y_2636_ = v___y_2603_;
v___y_2637_ = v___y_2604_;
v___y_2638_ = v___y_2605_;
v___y_2639_ = v___y_2606_;
v___y_2640_ = v___y_2607_;
v___y_2641_ = v___y_2608_;
v___y_2642_ = v___y_2609_;
v___y_2643_ = v___y_2610_;
v___y_2644_ = v___y_2611_;
goto v___jp_2632_;
}
v___jp_2632_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v_n_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2645_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3));
v___x_2646_ = l_Lean_mkConst(v___x_2645_, v___x_2623_);
v_n_2647_ = l_Lean_mkApp3(v___x_2646_, v_type_2616_, v_n_2620_, v_ofNatInst_2633_);
v___x_2648_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4);
v___x_2649_ = lean_int_dec_lt(v_k_2600_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2651_; 
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v_n_2647_);
v___x_2651_ = v___x_2630_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_n_2647_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
else
{
lean_object* v___x_2653_; 
lean_del_object(v___x_2630_);
v___x_2653_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2662_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2656_ = v___x_2653_;
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = l_Lean_Expr_app___override(v_a_2654_, v_n_2647_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2658_);
v___x_2660_ = v___x_2656_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
else
{
lean_dec_ref(v_n_2647_);
return v___x_2653_;
}
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec_ref_known(v___x_2623_, 2);
lean_dec_ref(v_n_2620_);
lean_dec_ref(v_semiringInst_2618_);
lean_dec_ref(v_type_2616_);
v_a_2668_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2627_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2627_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
v_a_2676_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2613_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2613_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object* v_k_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec(v_k_2684_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object* v_a_2698_, lean_object* v_s_2699_){
_start:
{
lean_object* v_toRing_2700_; lean_object* v_invFn_x3f_2701_; lean_object* v_semiringId_x3f_2702_; lean_object* v_commSemiringInst_2703_; lean_object* v_commRingInst_2704_; lean_object* v_noZeroDivInst_x3f_2705_; lean_object* v_fieldInst_x3f_2706_; lean_object* v_powIdentityInst_x3f_2707_; lean_object* v_denoteEntries_2708_; lean_object* v_nextId_2709_; lean_object* v_steps_2710_; lean_object* v_queue_2711_; lean_object* v_basis_2712_; lean_object* v_diseqs_2713_; uint8_t v_recheck_2714_; lean_object* v_invSet_2715_; lean_object* v_powIdentityVarCount_2716_; lean_object* v_numEq0_x3f_2717_; uint8_t v_numEq0Updated_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2750_; 
v_toRing_2700_ = lean_ctor_get(v_s_2699_, 0);
v_invFn_x3f_2701_ = lean_ctor_get(v_s_2699_, 1);
v_semiringId_x3f_2702_ = lean_ctor_get(v_s_2699_, 2);
v_commSemiringInst_2703_ = lean_ctor_get(v_s_2699_, 3);
v_commRingInst_2704_ = lean_ctor_get(v_s_2699_, 4);
v_noZeroDivInst_x3f_2705_ = lean_ctor_get(v_s_2699_, 5);
v_fieldInst_x3f_2706_ = lean_ctor_get(v_s_2699_, 6);
v_powIdentityInst_x3f_2707_ = lean_ctor_get(v_s_2699_, 7);
v_denoteEntries_2708_ = lean_ctor_get(v_s_2699_, 8);
v_nextId_2709_ = lean_ctor_get(v_s_2699_, 9);
v_steps_2710_ = lean_ctor_get(v_s_2699_, 10);
v_queue_2711_ = lean_ctor_get(v_s_2699_, 11);
v_basis_2712_ = lean_ctor_get(v_s_2699_, 12);
v_diseqs_2713_ = lean_ctor_get(v_s_2699_, 13);
v_recheck_2714_ = lean_ctor_get_uint8(v_s_2699_, sizeof(void*)*17);
v_invSet_2715_ = lean_ctor_get(v_s_2699_, 14);
v_powIdentityVarCount_2716_ = lean_ctor_get(v_s_2699_, 15);
v_numEq0_x3f_2717_ = lean_ctor_get(v_s_2699_, 16);
v_numEq0Updated_2718_ = lean_ctor_get_uint8(v_s_2699_, sizeof(void*)*17 + 1);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_s_2699_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2720_ = v_s_2699_;
v_isShared_2721_ = v_isSharedCheck_2750_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_numEq0_x3f_2717_);
lean_inc(v_powIdentityVarCount_2716_);
lean_inc(v_invSet_2715_);
lean_inc(v_diseqs_2713_);
lean_inc(v_basis_2712_);
lean_inc(v_queue_2711_);
lean_inc(v_steps_2710_);
lean_inc(v_nextId_2709_);
lean_inc(v_denoteEntries_2708_);
lean_inc(v_powIdentityInst_x3f_2707_);
lean_inc(v_fieldInst_x3f_2706_);
lean_inc(v_noZeroDivInst_x3f_2705_);
lean_inc(v_commRingInst_2704_);
lean_inc(v_commSemiringInst_2703_);
lean_inc(v_semiringId_x3f_2702_);
lean_inc(v_invFn_x3f_2701_);
lean_inc(v_toRing_2700_);
lean_dec(v_s_2699_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2750_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v_id_2722_; lean_object* v_type_2723_; lean_object* v_u_2724_; lean_object* v_ringInst_2725_; lean_object* v_semiringInst_2726_; lean_object* v_charInst_x3f_2727_; lean_object* v_addFn_x3f_2728_; lean_object* v_mulFn_x3f_2729_; lean_object* v_subFn_x3f_2730_; lean_object* v_negFn_x3f_2731_; lean_object* v_intCastFn_x3f_2732_; lean_object* v_natCastFn_x3f_2733_; lean_object* v_one_x3f_2734_; lean_object* v_vars_2735_; lean_object* v_varMap_2736_; lean_object* v_denote_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2748_; 
v_id_2722_ = lean_ctor_get(v_toRing_2700_, 0);
v_type_2723_ = lean_ctor_get(v_toRing_2700_, 1);
v_u_2724_ = lean_ctor_get(v_toRing_2700_, 2);
v_ringInst_2725_ = lean_ctor_get(v_toRing_2700_, 3);
v_semiringInst_2726_ = lean_ctor_get(v_toRing_2700_, 4);
v_charInst_x3f_2727_ = lean_ctor_get(v_toRing_2700_, 5);
v_addFn_x3f_2728_ = lean_ctor_get(v_toRing_2700_, 6);
v_mulFn_x3f_2729_ = lean_ctor_get(v_toRing_2700_, 7);
v_subFn_x3f_2730_ = lean_ctor_get(v_toRing_2700_, 8);
v_negFn_x3f_2731_ = lean_ctor_get(v_toRing_2700_, 9);
v_intCastFn_x3f_2732_ = lean_ctor_get(v_toRing_2700_, 11);
v_natCastFn_x3f_2733_ = lean_ctor_get(v_toRing_2700_, 12);
v_one_x3f_2734_ = lean_ctor_get(v_toRing_2700_, 13);
v_vars_2735_ = lean_ctor_get(v_toRing_2700_, 14);
v_varMap_2736_ = lean_ctor_get(v_toRing_2700_, 15);
v_denote_2737_ = lean_ctor_get(v_toRing_2700_, 16);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_toRing_2700_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; 
v_unused_2749_ = lean_ctor_get(v_toRing_2700_, 10);
lean_dec(v_unused_2749_);
v___x_2739_ = v_toRing_2700_;
v_isShared_2740_ = v_isSharedCheck_2748_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_denote_2737_);
lean_inc(v_varMap_2736_);
lean_inc(v_vars_2735_);
lean_inc(v_one_x3f_2734_);
lean_inc(v_natCastFn_x3f_2733_);
lean_inc(v_intCastFn_x3f_2732_);
lean_inc(v_negFn_x3f_2731_);
lean_inc(v_subFn_x3f_2730_);
lean_inc(v_mulFn_x3f_2729_);
lean_inc(v_addFn_x3f_2728_);
lean_inc(v_charInst_x3f_2727_);
lean_inc(v_semiringInst_2726_);
lean_inc(v_ringInst_2725_);
lean_inc(v_u_2724_);
lean_inc(v_type_2723_);
lean_inc(v_id_2722_);
lean_dec(v_toRing_2700_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2748_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2741_, 0, v_a_2698_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 10, v___x_2741_);
v___x_2743_ = v___x_2739_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_id_2722_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_type_2723_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_u_2724_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v_ringInst_2725_);
lean_ctor_set(v_reuseFailAlloc_2747_, 4, v_semiringInst_2726_);
lean_ctor_set(v_reuseFailAlloc_2747_, 5, v_charInst_x3f_2727_);
lean_ctor_set(v_reuseFailAlloc_2747_, 6, v_addFn_x3f_2728_);
lean_ctor_set(v_reuseFailAlloc_2747_, 7, v_mulFn_x3f_2729_);
lean_ctor_set(v_reuseFailAlloc_2747_, 8, v_subFn_x3f_2730_);
lean_ctor_set(v_reuseFailAlloc_2747_, 9, v_negFn_x3f_2731_);
lean_ctor_set(v_reuseFailAlloc_2747_, 10, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2747_, 11, v_intCastFn_x3f_2732_);
lean_ctor_set(v_reuseFailAlloc_2747_, 12, v_natCastFn_x3f_2733_);
lean_ctor_set(v_reuseFailAlloc_2747_, 13, v_one_x3f_2734_);
lean_ctor_set(v_reuseFailAlloc_2747_, 14, v_vars_2735_);
lean_ctor_set(v_reuseFailAlloc_2747_, 15, v_varMap_2736_);
lean_ctor_set(v_reuseFailAlloc_2747_, 16, v_denote_2737_);
v___x_2743_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2745_; 
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2743_);
v___x_2745_ = v___x_2720_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v_invFn_x3f_2701_);
lean_ctor_set(v_reuseFailAlloc_2746_, 2, v_semiringId_x3f_2702_);
lean_ctor_set(v_reuseFailAlloc_2746_, 3, v_commSemiringInst_2703_);
lean_ctor_set(v_reuseFailAlloc_2746_, 4, v_commRingInst_2704_);
lean_ctor_set(v_reuseFailAlloc_2746_, 5, v_noZeroDivInst_x3f_2705_);
lean_ctor_set(v_reuseFailAlloc_2746_, 6, v_fieldInst_x3f_2706_);
lean_ctor_set(v_reuseFailAlloc_2746_, 7, v_powIdentityInst_x3f_2707_);
lean_ctor_set(v_reuseFailAlloc_2746_, 8, v_denoteEntries_2708_);
lean_ctor_set(v_reuseFailAlloc_2746_, 9, v_nextId_2709_);
lean_ctor_set(v_reuseFailAlloc_2746_, 10, v_steps_2710_);
lean_ctor_set(v_reuseFailAlloc_2746_, 11, v_queue_2711_);
lean_ctor_set(v_reuseFailAlloc_2746_, 12, v_basis_2712_);
lean_ctor_set(v_reuseFailAlloc_2746_, 13, v_diseqs_2713_);
lean_ctor_set(v_reuseFailAlloc_2746_, 14, v_invSet_2715_);
lean_ctor_set(v_reuseFailAlloc_2746_, 15, v_powIdentityVarCount_2716_);
lean_ctor_set(v_reuseFailAlloc_2746_, 16, v_numEq0_x3f_2717_);
lean_ctor_set_uint8(v_reuseFailAlloc_2746_, sizeof(void*)*17, v_recheck_2714_);
lean_ctor_set_uint8(v_reuseFailAlloc_2746_, sizeof(void*)*17 + 1, v_numEq0Updated_2718_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = lean_unsigned_to_nat(0u);
v___x_2755_ = l_Lean_Level_ofNat(v___x_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(lean_object* v_u_2766_, lean_object* v_type_2767_, lean_object* v_semiringInst_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2781_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1));
v___x_2782_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2);
v___x_2783_ = lean_box(0);
lean_inc(v_u_2766_);
v___x_2784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2784_, 0, v_u_2766_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
lean_inc_ref(v___x_2784_);
v___x_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2782_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2786_, 0, v_u_2766_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
lean_inc_ref(v___x_2786_);
v___x_2787_ = l_Lean_mkConst(v___x_2781_, v___x_2786_);
v___x_2788_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2767_, 2);
v___x_2789_ = l_Lean_mkApp3(v___x_2787_, v_type_2767_, v___x_2788_, v_type_2767_);
v___x_2790_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2789_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v_inst_x27_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc_n(v_a_2791_, 2);
lean_dec_ref_known(v___x_2790_, 1);
v___x_2792_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4));
v___x_2793_ = l_Lean_mkConst(v___x_2792_, v___x_2784_);
lean_inc_ref(v_type_2767_);
v_inst_x27_2794_ = l_Lean_mkAppB(v___x_2793_, v_type_2767_, v_semiringInst_2768_);
v___x_2795_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6));
v___x_2796_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_2795_, v_a_2791_, v_inst_x27_2794_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
lean_dec_ref_known(v___x_2796_, 1);
v___x_2797_ = l_Lean_mkConst(v___x_2795_, v___x_2786_);
lean_inc_ref(v_type_2767_);
v___x_2798_ = l_Lean_mkApp4(v___x_2797_, v_type_2767_, v___x_2788_, v_type_2767_, v_a_2791_);
v___x_2799_ = l_Lean_Meta_Sym_canon(v___x_2798_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = l_Lean_Meta_Sym_shareCommon(v_a_2800_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
return v___x_2801_;
}
else
{
return v___x_2799_;
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_a_2791_);
lean_dec_ref_known(v___x_2786_, 2);
lean_dec_ref(v_type_2767_);
v_a_2802_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2796_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2796_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2786_, 2);
lean_dec_ref_known(v___x_2784_, 2);
lean_dec_ref(v_semiringInst_2768_);
lean_dec_ref(v_type_2767_);
return v___x_2790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___boxed(lean_object* v_u_2810_, lean_object* v_type_2811_, lean_object* v_semiringInst_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2810_, v_type_2811_, v_semiringInst_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec(v___y_2813_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2872_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2872_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2872_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v_toRing_2843_; lean_object* v_powFn_x3f_2844_; 
v_toRing_2843_ = lean_ctor_get(v_a_2839_, 0);
lean_inc_ref(v_toRing_2843_);
lean_dec(v_a_2839_);
v_powFn_x3f_2844_ = lean_ctor_get(v_toRing_2843_, 10);
if (lean_obj_tag(v_powFn_x3f_2844_) == 1)
{
lean_object* v_val_2845_; lean_object* v___x_2847_; 
lean_inc_ref(v_powFn_x3f_2844_);
lean_dec_ref(v_toRing_2843_);
v_val_2845_ = lean_ctor_get(v_powFn_x3f_2844_, 0);
lean_inc(v_val_2845_);
lean_dec_ref_known(v_powFn_x3f_2844_, 1);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v_val_2845_);
v___x_2847_ = v___x_2841_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_val_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
else
{
lean_object* v_type_2849_; lean_object* v_u_2850_; lean_object* v_semiringInst_2851_; lean_object* v___x_2852_; 
lean_del_object(v___x_2841_);
v_type_2849_ = lean_ctor_get(v_toRing_2843_, 1);
lean_inc_ref(v_type_2849_);
v_u_2850_ = lean_ctor_get(v_toRing_2843_, 2);
lean_inc(v_u_2850_);
v_semiringInst_2851_ = lean_ctor_get(v_toRing_2843_, 4);
lean_inc_ref(v_semiringInst_2851_);
lean_dec_ref(v_toRing_2843_);
v___x_2852_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2850_, v_type_2849_, v_semiringInst_2851_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___f_2854_; lean_object* v___x_2855_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc_n(v_a_2853_, 2);
lean_dec_ref_known(v___x_2852_, 1);
v___f_2854_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_2854_, 0, v_a_2853_);
v___x_2855_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2854_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2862_ == 0)
{
lean_object* v_unused_2863_; 
v_unused_2863_ = lean_ctor_get(v___x_2855_, 0);
lean_dec(v_unused_2863_);
v___x_2857_ = v___x_2855_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_dec(v___x_2855_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v_a_2853_);
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2853_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_a_2853_);
v_a_2864_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2855_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2855_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
v_a_2873_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2838_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2838_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec(v___y_2881_);
return v_res_2893_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2897_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2));
v___x_2898_ = lean_unsigned_to_nat(39u);
v___x_2899_ = lean_unsigned_to_nat(159u);
v___x_2900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1));
v___x_2901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0));
v___x_2902_ = l_mkPanicMessageWithDecl(v___x_2901_, v___x_2900_, v___x_2899_, v___x_2898_, v___x_2897_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
switch(lean_obj_tag(v_a_2903_))
{
case 0:
{
lean_object* v_k_2916_; lean_object* v___x_2917_; 
v_k_2916_ = lean_ctor_get(v_a_2903_, 0);
lean_inc(v_k_2916_);
lean_dec_ref_known(v_a_2903_, 1);
v___x_2917_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2916_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
lean_dec(v_k_2916_);
return v___x_2917_;
}
case 1:
{
lean_object* v_k_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_k_2918_ = lean_ctor_get(v_a_2903_, 0);
lean_inc(v_k_2918_);
lean_dec_ref_known(v_a_2903_, 1);
v___x_2919_ = lean_nat_to_int(v_k_2918_);
v___x_2920_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_2919_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
lean_dec(v___x_2919_);
return v___x_2920_;
}
case 3:
{
lean_object* v_i_2921_; lean_object* v___x_2922_; 
v_i_2921_ = lean_ctor_get(v_a_2903_, 0);
lean_inc(v_i_2921_);
lean_dec_ref_known(v_a_2903_, 1);
v___x_2922_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2924_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2924_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2942_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2942_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2942_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___y_2930_; lean_object* v_toSemiring_2935_; lean_object* v_vars_2936_; lean_object* v_size_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
v_toSemiring_2935_ = lean_ctor_get(v_a_2925_, 0);
lean_inc_ref(v_toSemiring_2935_);
lean_dec(v_a_2925_);
v_vars_2936_ = lean_ctor_get(v_toSemiring_2935_, 9);
lean_inc_ref(v_vars_2936_);
lean_dec_ref(v_toSemiring_2935_);
v_size_2937_ = lean_ctor_get(v_vars_2936_, 2);
v___x_2938_ = l_Lean_instInhabitedExpr;
v___x_2939_ = lean_nat_dec_lt(v_i_2921_, v_size_2937_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; 
lean_dec_ref(v_vars_2936_);
lean_dec(v_i_2921_);
v___x_2940_ = l_outOfBounds___redArg(v___x_2938_);
v___y_2930_ = v___x_2940_;
goto v___jp_2929_;
}
else
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2938_, v_vars_2936_, v_i_2921_);
lean_dec(v_i_2921_);
lean_dec_ref(v_vars_2936_);
v___y_2930_ = v___x_2941_;
goto v___jp_2929_;
}
v___jp_2929_:
{
lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2931_ = l_Lean_Expr_app___override(v_a_2923_, v___y_2930_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v___x_2931_);
v___x_2933_ = v___x_2927_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_a_2923_);
lean_dec(v_i_2921_);
v_a_2943_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2924_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2924_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
else
{
lean_dec(v_i_2921_);
return v___x_2922_;
}
}
case 5:
{
lean_object* v_a_2951_; lean_object* v_b_2952_; lean_object* v___x_2953_; 
v_a_2951_ = lean_ctor_get(v_a_2903_, 0);
lean_inc_ref(v_a_2951_);
v_b_2952_ = lean_ctor_get(v_a_2903_, 1);
lean_inc_ref(v_b_2952_);
lean_dec_ref_known(v_a_2903_, 2);
v___x_2953_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2951_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2957_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v___x_2957_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2952_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2966_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2966_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2966_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2962_ = l_Lean_mkAppB(v_a_2954_, v_a_2956_, v_a_2958_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v___x_2962_);
v___x_2964_ = v___x_2960_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
else
{
lean_dec(v_a_2956_);
lean_dec(v_a_2954_);
return v___x_2957_;
}
}
else
{
lean_dec(v_a_2954_);
lean_dec_ref(v_b_2952_);
return v___x_2955_;
}
}
else
{
lean_dec_ref(v_b_2952_);
lean_dec_ref(v_a_2951_);
return v___x_2953_;
}
}
case 7:
{
lean_object* v_a_2967_; lean_object* v_b_2968_; lean_object* v___x_2969_; 
v_a_2967_ = lean_ctor_get(v_a_2903_, 0);
lean_inc_ref(v_a_2967_);
v_b_2968_ = lean_ctor_get(v_a_2903_, 1);
lean_inc_ref(v_b_2968_);
lean_dec_ref_known(v_a_2903_, 2);
v___x_2969_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2971_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2971_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2967_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2973_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref_known(v___x_2971_, 1);
v___x_2973_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2968_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2982_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2978_ = l_Lean_mkAppB(v_a_2970_, v_a_2972_, v_a_2974_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v___x_2978_);
v___x_2980_ = v___x_2976_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
else
{
lean_dec(v_a_2972_);
lean_dec(v_a_2970_);
return v___x_2973_;
}
}
else
{
lean_dec(v_a_2970_);
lean_dec_ref(v_b_2968_);
return v___x_2971_;
}
}
else
{
lean_dec_ref(v_b_2968_);
lean_dec_ref(v_a_2967_);
return v___x_2969_;
}
}
case 8:
{
lean_object* v_a_2983_; lean_object* v_k_2984_; lean_object* v___x_2985_; 
v_a_2983_ = lean_ctor_get(v_a_2903_, 0);
lean_inc_ref(v_a_2983_);
v_k_2984_ = lean_ctor_get(v_a_2903_, 1);
lean_inc(v_k_2984_);
lean_dec_ref_known(v_a_2903_, 2);
v___x_2985_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2987_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2985_, 1);
v___x_2987_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2983_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2997_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2990_ = v___x_2987_;
v_isShared_2991_ = v_isSharedCheck_2997_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2987_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2997_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2995_; 
v___x_2992_ = l_Lean_mkNatLit(v_k_2984_);
v___x_2993_ = l_Lean_mkAppB(v_a_2986_, v_a_2988_, v___x_2992_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v___x_2993_);
v___x_2995_ = v___x_2990_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2993_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
else
{
lean_dec(v_a_2986_);
lean_dec(v_k_2984_);
return v___x_2987_;
}
}
else
{
lean_dec(v_k_2984_);
lean_dec_ref(v_a_2983_);
return v___x_2985_;
}
}
default: 
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
lean_dec_ref(v_a_2903_);
v___x_2998_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
v___x_2999_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___x_2998_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
return v___x_2999_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
lean_dec(v_a_3005_);
lean_dec_ref(v_a_3004_);
lean_dec(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec(v_a_3001_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(lean_object* v_type_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_3014_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(lean_object* v_type_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(v_type_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec(v___y_3029_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object* v_e_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_e_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3057_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3055_, 1);
v___x_3057_ = l_Lean_Meta_Sym_shareCommon(v_a_3056_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_);
return v___x_3057_;
}
else
{
return v___x_3055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object* v_e_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(v_e_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec(v_a_3059_);
return v_res_3071_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
}
#ifdef __cplusplus
}
#endif
