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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
v_options_166_ = lean_ctor_get(v___y_158_, 1);
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
v_ref_183_ = lean_ctor_get(v___y_180_, 4);
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
size_t v_x_904__boxed_1258_; lean_object* v_res_1259_; 
v_x_904__boxed_1258_ = lean_unbox_usize(v_x_1256_);
lean_dec(v_x_1256_);
v_res_1259_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1255_, v_x_904__boxed_1258_, v_x_1257_);
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
size_t v_x_1025__boxed_1342_; lean_object* v_res_1343_; 
v_x_1025__boxed_1342_ = lean_unbox_usize(v_x_1340_);
lean_dec(v_x_1340_);
v_res_1343_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(v_00_u03b2_1338_, v_x_1339_, v_x_1025__boxed_1342_, v_x_1341_);
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
lean_object* v_ks_1449_; lean_object* v_vs_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1468_; 
v_ks_1449_ = lean_ctor_get(v_x_1396_, 0);
v_vs_1450_ = lean_ctor_get(v_x_1396_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_x_1396_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1452_ = v_x_1396_;
v_isShared_1453_ = v_isSharedCheck_1468_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_vs_1450_);
lean_inc(v_ks_1449_);
lean_dec(v_x_1396_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1468_;
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
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_ks_1449_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_vs_1450_);
v___x_1455_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v_newNode_1456_; size_t v___x_1457_; uint8_t v___x_1458_; 
v_newNode_1456_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v___x_1455_, v_x_1399_, v_x_1400_);
v___x_1457_ = ((size_t)7ULL);
v___x_1458_ = lean_usize_dec_le(v___x_1457_, v_x_1398_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1459_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1456_);
v___x_1460_ = lean_unsigned_to_nat(4u);
v___x_1461_ = lean_nat_dec_lt(v___x_1459_, v___x_1460_);
lean_dec(v___x_1459_);
if (v___x_1461_ == 0)
{
lean_object* v_ks_1462_; lean_object* v_vs_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_ks_1462_ = lean_ctor_get(v_newNode_1456_, 0);
lean_inc_ref(v_ks_1462_);
v_vs_1463_ = lean_ctor_get(v_newNode_1456_, 1);
lean_inc_ref(v_vs_1463_);
lean_dec_ref(v_newNode_1456_);
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_1466_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_x_1398_, v_ks_1462_, v_vs_1463_, v___x_1464_, v___x_1465_);
lean_dec_ref(v_vs_1463_);
lean_dec_ref(v_ks_1462_);
return v___x_1466_;
}
else
{
return v_newNode_1456_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1469_, lean_object* v_keys_1470_, lean_object* v_vals_1471_, lean_object* v_i_1472_, lean_object* v_entries_1473_){
_start:
{
lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1474_ = lean_array_get_size(v_keys_1470_);
v___x_1475_ = lean_nat_dec_lt(v_i_1472_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_dec(v_i_1472_);
return v_entries_1473_;
}
else
{
lean_object* v_k_1476_; lean_object* v_v_1477_; size_t v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; uint64_t v___x_1481_; size_t v_h_1482_; size_t v___x_1483_; lean_object* v___x_1484_; size_t v___x_1485_; size_t v___x_1486_; size_t v___x_1487_; size_t v_h_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v_k_1476_ = lean_array_fget_borrowed(v_keys_1470_, v_i_1472_);
v_v_1477_ = lean_array_fget_borrowed(v_vals_1471_, v_i_1472_);
v___x_1478_ = lean_ptr_addr(v_k_1476_);
v___x_1479_ = ((size_t)3ULL);
v___x_1480_ = lean_usize_shift_right(v___x_1478_, v___x_1479_);
v___x_1481_ = lean_usize_to_uint64(v___x_1480_);
v_h_1482_ = lean_uint64_to_usize(v___x_1481_);
v___x_1483_ = ((size_t)5ULL);
v___x_1484_ = lean_unsigned_to_nat(1u);
v___x_1485_ = ((size_t)1ULL);
v___x_1486_ = lean_usize_sub(v_depth_1469_, v___x_1485_);
v___x_1487_ = lean_usize_mul(v___x_1483_, v___x_1486_);
v_h_1488_ = lean_usize_shift_right(v_h_1482_, v___x_1487_);
v___x_1489_ = lean_nat_add(v_i_1472_, v___x_1484_);
lean_dec(v_i_1472_);
lean_inc(v_v_1477_);
lean_inc(v_k_1476_);
v___x_1490_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_entries_1473_, v_h_1488_, v_depth_1469_, v_k_1476_, v_v_1477_);
v_i_1472_ = v___x_1489_;
v_entries_1473_ = v___x_1490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1492_, lean_object* v_keys_1493_, lean_object* v_vals_1494_, lean_object* v_i_1495_, lean_object* v_entries_1496_){
_start:
{
size_t v_depth_boxed_1497_; lean_object* v_res_1498_; 
v_depth_boxed_1497_ = lean_unbox_usize(v_depth_1492_);
lean_dec(v_depth_1492_);
v_res_1498_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1497_, v_keys_1493_, v_vals_1494_, v_i_1495_, v_entries_1496_);
lean_dec_ref(v_vals_1494_);
lean_dec_ref(v_keys_1493_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_, lean_object* v_x_1503_){
_start:
{
size_t v_x_6667__boxed_1504_; size_t v_x_6668__boxed_1505_; lean_object* v_res_1506_; 
v_x_6667__boxed_1504_ = lean_unbox_usize(v_x_1500_);
lean_dec(v_x_1500_);
v_x_6668__boxed_1505_ = lean_unbox_usize(v_x_1501_);
lean_dec(v_x_1501_);
v_res_1506_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1499_, v_x_6667__boxed_1504_, v_x_6668__boxed_1505_, v_x_1502_, v_x_1503_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object* v_x_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_){
_start:
{
size_t v___x_1510_; size_t v___x_1511_; size_t v___x_1512_; uint64_t v___x_1513_; size_t v___x_1514_; size_t v___x_1515_; lean_object* v___x_1516_; 
v___x_1510_ = lean_ptr_addr(v_x_1508_);
v___x_1511_ = ((size_t)3ULL);
v___x_1512_ = lean_usize_shift_right(v___x_1510_, v___x_1511_);
v___x_1513_ = lean_usize_to_uint64(v___x_1512_);
v___x_1514_ = lean_uint64_to_usize(v___x_1513_);
v___x_1515_ = ((size_t)1ULL);
v___x_1516_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1507_, v___x_1514_, v___x_1515_, v_x_1508_, v_x_1509_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object* v_e_1517_, lean_object* v_a_1518_, lean_object* v_s_1519_){
_start:
{
lean_object* v_rings_1520_; lean_object* v_typeIdOf_1521_; lean_object* v_exprToRingId_1522_; lean_object* v_semirings_1523_; lean_object* v_stypeIdOf_1524_; lean_object* v_exprToSemiringId_1525_; lean_object* v_ncRings_1526_; lean_object* v_exprToNCRingId_1527_; lean_object* v_nctypeIdOf_1528_; lean_object* v_ncSemirings_1529_; lean_object* v_exprToNCSemiringId_1530_; lean_object* v_ncstypeIdOf_1531_; lean_object* v_steps_1532_; uint8_t v_reportedMaxDegreeIssue_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1541_; 
v_rings_1520_ = lean_ctor_get(v_s_1519_, 0);
v_typeIdOf_1521_ = lean_ctor_get(v_s_1519_, 1);
v_exprToRingId_1522_ = lean_ctor_get(v_s_1519_, 2);
v_semirings_1523_ = lean_ctor_get(v_s_1519_, 3);
v_stypeIdOf_1524_ = lean_ctor_get(v_s_1519_, 4);
v_exprToSemiringId_1525_ = lean_ctor_get(v_s_1519_, 5);
v_ncRings_1526_ = lean_ctor_get(v_s_1519_, 6);
v_exprToNCRingId_1527_ = lean_ctor_get(v_s_1519_, 7);
v_nctypeIdOf_1528_ = lean_ctor_get(v_s_1519_, 8);
v_ncSemirings_1529_ = lean_ctor_get(v_s_1519_, 9);
v_exprToNCSemiringId_1530_ = lean_ctor_get(v_s_1519_, 10);
v_ncstypeIdOf_1531_ = lean_ctor_get(v_s_1519_, 11);
v_steps_1532_ = lean_ctor_get(v_s_1519_, 12);
v_reportedMaxDegreeIssue_1533_ = lean_ctor_get_uint8(v_s_1519_, sizeof(void*)*13);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_s_1519_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1535_ = v_s_1519_;
v_isShared_1536_ = v_isSharedCheck_1541_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_steps_1532_);
lean_inc(v_ncstypeIdOf_1531_);
lean_inc(v_exprToNCSemiringId_1530_);
lean_inc(v_ncSemirings_1529_);
lean_inc(v_nctypeIdOf_1528_);
lean_inc(v_exprToNCRingId_1527_);
lean_inc(v_ncRings_1526_);
lean_inc(v_exprToSemiringId_1525_);
lean_inc(v_stypeIdOf_1524_);
lean_inc(v_semirings_1523_);
lean_inc(v_exprToRingId_1522_);
lean_inc(v_typeIdOf_1521_);
lean_inc(v_rings_1520_);
lean_dec(v_s_1519_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1541_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
lean_inc(v_a_1518_);
v___x_1537_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_exprToSemiringId_1525_, v_e_1517_, v_a_1518_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 5, v___x_1537_);
v___x_1539_ = v___x_1535_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_rings_1520_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_typeIdOf_1521_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_exprToRingId_1522_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_semirings_1523_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_stypeIdOf_1524_);
lean_ctor_set(v_reuseFailAlloc_1540_, 5, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1540_, 6, v_ncRings_1526_);
lean_ctor_set(v_reuseFailAlloc_1540_, 7, v_exprToNCRingId_1527_);
lean_ctor_set(v_reuseFailAlloc_1540_, 8, v_nctypeIdOf_1528_);
lean_ctor_set(v_reuseFailAlloc_1540_, 9, v_ncSemirings_1529_);
lean_ctor_set(v_reuseFailAlloc_1540_, 10, v_exprToNCSemiringId_1530_);
lean_ctor_set(v_reuseFailAlloc_1540_, 11, v_ncstypeIdOf_1531_);
lean_ctor_set(v_reuseFailAlloc_1540_, 12, v_steps_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1540_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1533_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object* v_e_1542_, lean_object* v_a_1543_, lean_object* v_s_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(v_e_1542_, v_a_1543_, v_s_1544_);
lean_dec(v_a_1543_);
return v_res_1545_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0));
v___x_1548_ = l_Lean_stringToMessageData(v___x_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object* v_e_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1549_, v_a_1551_, v_a_1556_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
if (lean_obj_tag(v_a_1563_) == 1)
{
lean_object* v_val_1564_; uint8_t v___x_1565_; 
v_val_1564_ = lean_ctor_get(v_a_1563_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v_a_1563_, 1);
v___x_1565_ = lean_nat_dec_eq(v_val_1564_, v_a_1550_);
lean_dec(v_val_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1552_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; uint8_t v_verbose_1568_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v_verbose_1568_ = lean_ctor_get_uint8(v_a_1567_, 0);
lean_dec(v_a_1567_);
if (v_verbose_1568_ == 0)
{
lean_dec_ref(v_e_1549_);
goto v___jp_1559_;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1569_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1);
v___x_1570_ = l_Lean_indentExpr(v_e_1549_);
v___x_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = l_Lean_Meta_Sym_reportIssue(v___x_1571_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_dec_ref_known(v___x_1572_, 1);
goto v___jp_1559_;
}
else
{
return v___x_1572_;
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v_e_1549_);
v_a_1573_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1566_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1566_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_dec_ref(v_e_1549_);
goto v___jp_1559_;
}
}
else
{
lean_object* v___f_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec(v_a_1563_);
lean_inc(v_a_1550_);
v___f_1581_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1581_, 0, v_e_1549_);
lean_closure_set(v___f_1581_, 1, v_a_1550_);
v___x_1582_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1583_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1582_, v___f_1581_, v_a_1551_);
return v___x_1583_;
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v_e_1549_);
v_a_1584_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1562_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1562_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
v___jp_1559_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_box(0);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object* v_e_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec(v_a_1593_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object* v_e_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1603_, v_a_1604_, v_a_1605_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object* v_e_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec(v_a_1618_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object* v_00_u03b2_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_1632_, v_x_1633_, v_x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_1636_, lean_object* v_x_1637_, size_t v_x_1638_, size_t v_x_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1637_, v_x_1638_, v_x_1639_, v_x_1640_, v_x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_){
_start:
{
size_t v_x_6953__boxed_1649_; size_t v_x_6954__boxed_1650_; lean_object* v_res_1651_; 
v_x_6953__boxed_1649_ = lean_unbox_usize(v_x_1645_);
lean_dec(v_x_1645_);
v_x_6954__boxed_1650_ = lean_unbox_usize(v_x_1646_);
lean_dec(v_x_1646_);
v_res_1651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_1643_, v_x_1644_, v_x_6953__boxed_1649_, v_x_6954__boxed_1650_, v_x_1647_, v_x_1648_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1652_, lean_object* v_n_1653_, lean_object* v_k_1654_, lean_object* v_v_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_1653_, v_k_1654_, v_v_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1657_, size_t v_depth_1658_, lean_object* v_keys_1659_, lean_object* v_vals_1660_, lean_object* v_heq_1661_, lean_object* v_i_1662_, lean_object* v_entries_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_1658_, v_keys_1659_, v_vals_1660_, v_i_1662_, v_entries_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1665_, lean_object* v_depth_1666_, lean_object* v_keys_1667_, lean_object* v_vals_1668_, lean_object* v_heq_1669_, lean_object* v_i_1670_, lean_object* v_entries_1671_){
_start:
{
size_t v_depth_boxed_1672_; lean_object* v_res_1673_; 
v_depth_boxed_1672_ = lean_unbox_usize(v_depth_1666_);
lean_dec(v_depth_1666_);
v_res_1673_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_1665_, v_depth_boxed_1672_, v_keys_1667_, v_vals_1668_, v_heq_1669_, v_i_1670_, v_entries_1671_);
lean_dec_ref(v_vals_1668_);
lean_dec_ref(v_keys_1667_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_, lean_object* v_x_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1675_, v_x_1676_, v_x_1677_, v_x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object* v_e_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1680_, v___y_1681_, v___y_1682_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object* v_e_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(v_e_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec(v___y_1695_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object* v_e_1710_, lean_object* v___f_1711_, lean_object* v___f_1712_, lean_object* v_size_1713_, lean_object* v_s_1714_){
_start:
{
lean_object* v_id_1715_; lean_object* v_type_1716_; lean_object* v_u_1717_; lean_object* v_semiringInst_1718_; lean_object* v_addFn_x3f_1719_; lean_object* v_mulFn_x3f_1720_; lean_object* v_powFn_x3f_1721_; lean_object* v_natCastFn_x3f_1722_; lean_object* v_denote_1723_; lean_object* v_vars_1724_; lean_object* v_varMap_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1734_; 
v_id_1715_ = lean_ctor_get(v_s_1714_, 0);
v_type_1716_ = lean_ctor_get(v_s_1714_, 1);
v_u_1717_ = lean_ctor_get(v_s_1714_, 2);
v_semiringInst_1718_ = lean_ctor_get(v_s_1714_, 3);
v_addFn_x3f_1719_ = lean_ctor_get(v_s_1714_, 4);
v_mulFn_x3f_1720_ = lean_ctor_get(v_s_1714_, 5);
v_powFn_x3f_1721_ = lean_ctor_get(v_s_1714_, 6);
v_natCastFn_x3f_1722_ = lean_ctor_get(v_s_1714_, 7);
v_denote_1723_ = lean_ctor_get(v_s_1714_, 8);
v_vars_1724_ = lean_ctor_get(v_s_1714_, 9);
v_varMap_1725_ = lean_ctor_get(v_s_1714_, 10);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_s_1714_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1727_ = v_s_1714_;
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_varMap_1725_);
lean_inc(v_vars_1724_);
lean_inc(v_denote_1723_);
lean_inc(v_natCastFn_x3f_1722_);
lean_inc(v_powFn_x3f_1721_);
lean_inc(v_mulFn_x3f_1720_);
lean_inc(v_addFn_x3f_1719_);
lean_inc(v_semiringInst_1718_);
lean_inc(v_u_1717_);
lean_inc(v_type_1716_);
lean_inc(v_id_1715_);
lean_dec(v_s_1714_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
lean_inc_ref(v_e_1710_);
v___x_1729_ = l_Lean_PersistentArray_push___redArg(v_vars_1724_, v_e_1710_);
v___x_1730_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1711_, v___f_1712_, v_varMap_1725_, v_e_1710_, v_size_1713_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 10, v___x_1730_);
lean_ctor_set(v___x_1727_, 9, v___x_1729_);
v___x_1732_ = v___x_1727_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_id_1715_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_type_1716_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_u_1717_);
lean_ctor_set(v_reuseFailAlloc_1733_, 3, v_semiringInst_1718_);
lean_ctor_set(v_reuseFailAlloc_1733_, 4, v_addFn_x3f_1719_);
lean_ctor_set(v_reuseFailAlloc_1733_, 5, v_mulFn_x3f_1720_);
lean_ctor_set(v_reuseFailAlloc_1733_, 6, v_powFn_x3f_1721_);
lean_ctor_set(v_reuseFailAlloc_1733_, 7, v_natCastFn_x3f_1722_);
lean_ctor_set(v_reuseFailAlloc_1733_, 8, v_denote_1723_);
lean_ctor_set(v_reuseFailAlloc_1733_, 9, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1733_, 10, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object* v_toPure_1735_, lean_object* v_size_1736_, lean_object* v_____r_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_apply_2(v_toPure_1735_, lean_box(0), v_size_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object* v_e_1739_, lean_object* v_inst_1740_, lean_object* v_toBind_1741_, lean_object* v___f_1742_, lean_object* v_____r_1743_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1744_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1745_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_1745_, 0, lean_box(0));
lean_closure_set(v___x_1745_, 1, v___x_1744_);
lean_closure_set(v___x_1745_, 2, v_e_1739_);
v___x_1746_ = lean_apply_2(v_inst_1740_, lean_box(0), v___x_1745_);
v___x_1747_ = lean_apply_4(v_toBind_1741_, lean_box(0), lean_box(0), v___x_1746_, v___f_1742_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object* v_inst_1748_, lean_object* v_e_1749_, lean_object* v_toBind_1750_, lean_object* v___f_1751_, lean_object* v_____r_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_apply_1(v_inst_1748_, v_e_1749_);
v___x_1754_ = lean_apply_4(v_toBind_1750_, lean_box(0), lean_box(0), v___x_1753_, v___f_1751_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object* v___f_1755_, lean_object* v___f_1756_, lean_object* v_e_1757_, lean_object* v_toPure_1758_, lean_object* v_inst_1759_, lean_object* v_toBind_1760_, lean_object* v_inst_1761_, lean_object* v_modifySemiring_1762_, lean_object* v_s_1763_){
_start:
{
lean_object* v_vars_1764_; lean_object* v_varMap_1765_; lean_object* v___x_1766_; 
v_vars_1764_ = lean_ctor_get(v_s_1763_, 9);
lean_inc_ref(v_vars_1764_);
v_varMap_1765_ = lean_ctor_get(v_s_1763_, 10);
lean_inc_ref(v_varMap_1765_);
lean_dec_ref(v_s_1763_);
lean_inc_ref(v_e_1757_);
lean_inc_ref(v___f_1756_);
lean_inc_ref(v___f_1755_);
v___x_1766_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_1755_, v___f_1756_, v_varMap_1765_, v_e_1757_);
lean_dec_ref(v_varMap_1765_);
if (lean_obj_tag(v___x_1766_) == 1)
{
lean_object* v_val_1767_; lean_object* v___x_1768_; 
lean_dec_ref(v_vars_1764_);
lean_dec(v_modifySemiring_1762_);
lean_dec(v_inst_1761_);
lean_dec(v_toBind_1760_);
lean_dec(v_inst_1759_);
lean_dec_ref(v_e_1757_);
lean_dec_ref(v___f_1756_);
lean_dec_ref(v___f_1755_);
v_val_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_val_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = lean_apply_2(v_toPure_1758_, lean_box(0), v_val_1767_);
return v___x_1768_;
}
else
{
lean_object* v_size_1769_; lean_object* v___f_1770_; lean_object* v___f_1771_; lean_object* v___f_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec(v___x_1766_);
v_size_1769_ = lean_ctor_get(v_vars_1764_, 2);
lean_inc_n(v_size_1769_, 2);
lean_dec_ref(v_vars_1764_);
lean_inc_ref_n(v_e_1757_, 2);
v___f_1770_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1770_, 0, v_e_1757_);
lean_closure_set(v___f_1770_, 1, v___f_1755_);
lean_closure_set(v___f_1770_, 2, v___f_1756_);
lean_closure_set(v___f_1770_, 3, v_size_1769_);
v___f_1771_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1771_, 0, v_toPure_1758_);
lean_closure_set(v___f_1771_, 1, v_size_1769_);
lean_inc_n(v_toBind_1760_, 2);
v___f_1772_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1772_, 0, v_e_1757_);
lean_closure_set(v___f_1772_, 1, v_inst_1759_);
lean_closure_set(v___f_1772_, 2, v_toBind_1760_);
lean_closure_set(v___f_1772_, 3, v___f_1771_);
v___f_1773_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1773_, 0, v_inst_1761_);
lean_closure_set(v___f_1773_, 1, v_e_1757_);
lean_closure_set(v___f_1773_, 2, v_toBind_1760_);
lean_closure_set(v___f_1773_, 3, v___f_1772_);
v___x_1774_ = lean_apply_1(v_modifySemiring_1762_, v___f_1770_);
v___x_1775_ = lean_apply_4(v_toBind_1760_, lean_box(0), lean_box(0), v___x_1774_, v___f_1773_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_e_1782_){
_start:
{
lean_object* v_toApplicative_1783_; lean_object* v_toBind_1784_; lean_object* v_getSemiring_1785_; lean_object* v_modifySemiring_1786_; lean_object* v_toPure_1787_; lean_object* v___f_1788_; lean_object* v___f_1789_; lean_object* v___f_1790_; lean_object* v___x_1791_; 
v_toApplicative_1783_ = lean_ctor_get(v_inst_1779_, 0);
lean_inc_ref(v_toApplicative_1783_);
v_toBind_1784_ = lean_ctor_get(v_inst_1779_, 1);
lean_inc_n(v_toBind_1784_, 2);
lean_dec_ref(v_inst_1779_);
v_getSemiring_1785_ = lean_ctor_get(v_inst_1780_, 0);
lean_inc(v_getSemiring_1785_);
v_modifySemiring_1786_ = lean_ctor_get(v_inst_1780_, 1);
lean_inc(v_modifySemiring_1786_);
lean_dec_ref(v_inst_1780_);
v_toPure_1787_ = lean_ctor_get(v_toApplicative_1783_, 1);
lean_inc(v_toPure_1787_);
lean_dec_ref(v_toApplicative_1783_);
v___f_1788_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0));
v___f_1789_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1));
v___f_1790_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1790_, 0, v___f_1788_);
lean_closure_set(v___f_1790_, 1, v___f_1789_);
lean_closure_set(v___f_1790_, 2, v_e_1782_);
lean_closure_set(v___f_1790_, 3, v_toPure_1787_);
lean_closure_set(v___f_1790_, 4, v_inst_1778_);
lean_closure_set(v___f_1790_, 5, v_toBind_1784_);
lean_closure_set(v___f_1790_, 6, v_inst_1781_);
lean_closure_set(v___f_1790_, 7, v_modifySemiring_1786_);
v___x_1791_ = lean_apply_4(v_toBind_1784_, lean_box(0), lean_box(0), v_getSemiring_1785_, v___f_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object* v_m_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_e_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v_inst_1793_, v_inst_1794_, v_inst_1795_, v_inst_1796_, v_e_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(lean_object* v___y_1799_, lean_object* v_e_1800_, lean_object* v_size_1801_, lean_object* v_s_1802_){
_start:
{
lean_object* v_rings_1803_; lean_object* v_typeIdOf_1804_; lean_object* v_exprToRingId_1805_; lean_object* v_semirings_1806_; lean_object* v_stypeIdOf_1807_; lean_object* v_exprToSemiringId_1808_; lean_object* v_ncRings_1809_; lean_object* v_exprToNCRingId_1810_; lean_object* v_nctypeIdOf_1811_; lean_object* v_ncSemirings_1812_; lean_object* v_exprToNCSemiringId_1813_; lean_object* v_ncstypeIdOf_1814_; lean_object* v_steps_1815_; uint8_t v_reportedMaxDegreeIssue_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v_rings_1803_ = lean_ctor_get(v_s_1802_, 0);
v_typeIdOf_1804_ = lean_ctor_get(v_s_1802_, 1);
v_exprToRingId_1805_ = lean_ctor_get(v_s_1802_, 2);
v_semirings_1806_ = lean_ctor_get(v_s_1802_, 3);
v_stypeIdOf_1807_ = lean_ctor_get(v_s_1802_, 4);
v_exprToSemiringId_1808_ = lean_ctor_get(v_s_1802_, 5);
v_ncRings_1809_ = lean_ctor_get(v_s_1802_, 6);
v_exprToNCRingId_1810_ = lean_ctor_get(v_s_1802_, 7);
v_nctypeIdOf_1811_ = lean_ctor_get(v_s_1802_, 8);
v_ncSemirings_1812_ = lean_ctor_get(v_s_1802_, 9);
v_exprToNCSemiringId_1813_ = lean_ctor_get(v_s_1802_, 10);
v_ncstypeIdOf_1814_ = lean_ctor_get(v_s_1802_, 11);
v_steps_1815_ = lean_ctor_get(v_s_1802_, 12);
v_reportedMaxDegreeIssue_1816_ = lean_ctor_get_uint8(v_s_1802_, sizeof(void*)*13);
v___x_1817_ = lean_array_get_size(v_semirings_1806_);
v___x_1818_ = lean_nat_dec_lt(v___y_1799_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_dec(v_size_1801_);
lean_dec_ref(v_e_1800_);
return v_s_1802_;
}
else
{
lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1861_; 
lean_inc(v_steps_1815_);
lean_inc_ref(v_ncstypeIdOf_1814_);
lean_inc_ref(v_exprToNCSemiringId_1813_);
lean_inc_ref(v_ncSemirings_1812_);
lean_inc_ref(v_nctypeIdOf_1811_);
lean_inc_ref(v_exprToNCRingId_1810_);
lean_inc_ref(v_ncRings_1809_);
lean_inc_ref(v_exprToSemiringId_1808_);
lean_inc_ref(v_stypeIdOf_1807_);
lean_inc_ref(v_semirings_1806_);
lean_inc_ref(v_exprToRingId_1805_);
lean_inc_ref(v_typeIdOf_1804_);
lean_inc_ref(v_rings_1803_);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_s_1802_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; lean_object* v_unused_1863_; lean_object* v_unused_1864_; lean_object* v_unused_1865_; lean_object* v_unused_1866_; lean_object* v_unused_1867_; lean_object* v_unused_1868_; lean_object* v_unused_1869_; lean_object* v_unused_1870_; lean_object* v_unused_1871_; lean_object* v_unused_1872_; lean_object* v_unused_1873_; lean_object* v_unused_1874_; 
v_unused_1862_ = lean_ctor_get(v_s_1802_, 12);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v_s_1802_, 11);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v_s_1802_, 10);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_s_1802_, 9);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_s_1802_, 8);
lean_dec(v_unused_1866_);
v_unused_1867_ = lean_ctor_get(v_s_1802_, 7);
lean_dec(v_unused_1867_);
v_unused_1868_ = lean_ctor_get(v_s_1802_, 6);
lean_dec(v_unused_1868_);
v_unused_1869_ = lean_ctor_get(v_s_1802_, 5);
lean_dec(v_unused_1869_);
v_unused_1870_ = lean_ctor_get(v_s_1802_, 4);
lean_dec(v_unused_1870_);
v_unused_1871_ = lean_ctor_get(v_s_1802_, 3);
lean_dec(v_unused_1871_);
v_unused_1872_ = lean_ctor_get(v_s_1802_, 2);
lean_dec(v_unused_1872_);
v_unused_1873_ = lean_ctor_get(v_s_1802_, 1);
lean_dec(v_unused_1873_);
v_unused_1874_ = lean_ctor_get(v_s_1802_, 0);
lean_dec(v_unused_1874_);
v___x_1820_ = v_s_1802_;
v_isShared_1821_ = v_isSharedCheck_1861_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v_s_1802_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1861_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_v_1822_; lean_object* v_toSemiring_1823_; lean_object* v_ringId_1824_; lean_object* v_commSemiringInst_1825_; lean_object* v_addRightCancelInst_x3f_1826_; lean_object* v_toQFn_x3f_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1860_; 
v_v_1822_ = lean_array_fget(v_semirings_1806_, v___y_1799_);
v_toSemiring_1823_ = lean_ctor_get(v_v_1822_, 0);
v_ringId_1824_ = lean_ctor_get(v_v_1822_, 1);
v_commSemiringInst_1825_ = lean_ctor_get(v_v_1822_, 2);
v_addRightCancelInst_x3f_1826_ = lean_ctor_get(v_v_1822_, 3);
v_toQFn_x3f_1827_ = lean_ctor_get(v_v_1822_, 4);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_v_1822_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1829_ = v_v_1822_;
v_isShared_1830_ = v_isSharedCheck_1860_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_toQFn_x3f_1827_);
lean_inc(v_addRightCancelInst_x3f_1826_);
lean_inc(v_commSemiringInst_1825_);
lean_inc(v_ringId_1824_);
lean_inc(v_toSemiring_1823_);
lean_dec(v_v_1822_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1860_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_id_1831_; lean_object* v_type_1832_; lean_object* v_u_1833_; lean_object* v_semiringInst_1834_; lean_object* v_addFn_x3f_1835_; lean_object* v_mulFn_x3f_1836_; lean_object* v_powFn_x3f_1837_; lean_object* v_natCastFn_x3f_1838_; lean_object* v_denote_1839_; lean_object* v_vars_1840_; lean_object* v_varMap_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1859_; 
v_id_1831_ = lean_ctor_get(v_toSemiring_1823_, 0);
v_type_1832_ = lean_ctor_get(v_toSemiring_1823_, 1);
v_u_1833_ = lean_ctor_get(v_toSemiring_1823_, 2);
v_semiringInst_1834_ = lean_ctor_get(v_toSemiring_1823_, 3);
v_addFn_x3f_1835_ = lean_ctor_get(v_toSemiring_1823_, 4);
v_mulFn_x3f_1836_ = lean_ctor_get(v_toSemiring_1823_, 5);
v_powFn_x3f_1837_ = lean_ctor_get(v_toSemiring_1823_, 6);
v_natCastFn_x3f_1838_ = lean_ctor_get(v_toSemiring_1823_, 7);
v_denote_1839_ = lean_ctor_get(v_toSemiring_1823_, 8);
v_vars_1840_ = lean_ctor_get(v_toSemiring_1823_, 9);
v_varMap_1841_ = lean_ctor_get(v_toSemiring_1823_, 10);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_toSemiring_1823_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1843_ = v_toSemiring_1823_;
v_isShared_1844_ = v_isSharedCheck_1859_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_varMap_1841_);
lean_inc(v_vars_1840_);
lean_inc(v_denote_1839_);
lean_inc(v_natCastFn_x3f_1838_);
lean_inc(v_powFn_x3f_1837_);
lean_inc(v_mulFn_x3f_1836_);
lean_inc(v_addFn_x3f_1835_);
lean_inc(v_semiringInst_1834_);
lean_inc(v_u_1833_);
lean_inc(v_type_1832_);
lean_inc(v_id_1831_);
lean_dec(v_toSemiring_1823_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1859_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v_xs_x27_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1845_ = lean_box(0);
v_xs_x27_1846_ = lean_array_fset(v_semirings_1806_, v___y_1799_, v___x_1845_);
lean_inc_ref(v_e_1800_);
v___x_1847_ = l_Lean_PersistentArray_push___redArg(v_vars_1840_, v_e_1800_);
v___x_1848_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_varMap_1841_, v_e_1800_, v_size_1801_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 10, v___x_1848_);
lean_ctor_set(v___x_1843_, 9, v___x_1847_);
v___x_1850_ = v___x_1843_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_id_1831_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_type_1832_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_u_1833_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_semiringInst_1834_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_addFn_x3f_1835_);
lean_ctor_set(v_reuseFailAlloc_1858_, 5, v_mulFn_x3f_1836_);
lean_ctor_set(v_reuseFailAlloc_1858_, 6, v_powFn_x3f_1837_);
lean_ctor_set(v_reuseFailAlloc_1858_, 7, v_natCastFn_x3f_1838_);
lean_ctor_set(v_reuseFailAlloc_1858_, 8, v_denote_1839_);
lean_ctor_set(v_reuseFailAlloc_1858_, 9, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1858_, 10, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1852_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1850_);
v___x_1852_ = v___x_1829_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_ringId_1824_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_commSemiringInst_1825_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_addRightCancelInst_x3f_1826_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_toQFn_x3f_1827_);
v___x_1852_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = lean_array_fset(v_xs_x27_1846_, v___y_1799_, v___x_1852_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 3, v___x_1853_);
v___x_1855_ = v___x_1820_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_rings_1803_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_typeIdOf_1804_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_exprToRingId_1805_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v_stypeIdOf_1807_);
lean_ctor_set(v_reuseFailAlloc_1856_, 5, v_exprToSemiringId_1808_);
lean_ctor_set(v_reuseFailAlloc_1856_, 6, v_ncRings_1809_);
lean_ctor_set(v_reuseFailAlloc_1856_, 7, v_exprToNCRingId_1810_);
lean_ctor_set(v_reuseFailAlloc_1856_, 8, v_nctypeIdOf_1811_);
lean_ctor_set(v_reuseFailAlloc_1856_, 9, v_ncSemirings_1812_);
lean_ctor_set(v_reuseFailAlloc_1856_, 10, v_exprToNCSemiringId_1813_);
lean_ctor_set(v_reuseFailAlloc_1856_, 11, v_ncstypeIdOf_1814_);
lean_ctor_set(v_reuseFailAlloc_1856_, 12, v_steps_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1816_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed(lean_object* v___y_1875_, lean_object* v_e_1876_, lean_object* v_size_1877_, lean_object* v_s_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(v___y_1875_, v_e_1876_, v_size_1877_, v_s_1878_);
lean_dec(v___y_1875_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(lean_object* v_e_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1944_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1944_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1944_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_toSemiring_1898_; lean_object* v_vars_1899_; lean_object* v_varMap_1900_; lean_object* v___x_1901_; 
v_toSemiring_1898_ = lean_ctor_get(v_a_1894_, 0);
lean_inc_ref(v_toSemiring_1898_);
lean_dec(v_a_1894_);
v_vars_1899_ = lean_ctor_get(v_toSemiring_1898_, 9);
lean_inc_ref(v_vars_1899_);
v_varMap_1900_ = lean_ctor_get(v_toSemiring_1898_, 10);
lean_inc_ref(v_varMap_1900_);
lean_dec_ref(v_toSemiring_1898_);
v___x_1901_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_varMap_1900_, v_e_1880_);
lean_dec_ref(v_varMap_1900_);
if (lean_obj_tag(v___x_1901_) == 1)
{
lean_object* v_val_1902_; lean_object* v___x_1904_; 
lean_dec_ref(v_vars_1899_);
lean_dec_ref(v_e_1880_);
v_val_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_val_1902_);
lean_dec_ref_known(v___x_1901_, 1);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v_val_1902_);
v___x_1904_ = v___x_1896_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_val_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
else
{
lean_object* v_size_1906_; lean_object* v___f_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec(v___x_1901_);
lean_del_object(v___x_1896_);
v_size_1906_ = lean_ctor_get(v_vars_1899_, 2);
lean_inc_n(v_size_1906_, 2);
lean_dec_ref(v_vars_1899_);
lean_inc_ref(v_e_1880_);
lean_inc(v___y_1881_);
v___f_1907_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1907_, 0, v___y_1881_);
lean_closure_set(v___f_1907_, 1, v_e_1880_);
lean_closure_set(v___f_1907_, 2, v_size_1906_);
v___x_1908_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1909_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1908_, v___f_1907_, v___y_1882_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v___x_1910_; 
lean_dec_ref_known(v___x_1909_, 1);
lean_inc_ref(v_e_1880_);
v___x_1910_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1880_, v___y_1881_, v___y_1882_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v___x_1911_; 
lean_dec_ref_known(v___x_1910_, 1);
v___x_1911_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1908_, v_e_1880_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
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
lean_ctor_set(v___x_1913_, 0, v_size_1906_);
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_size_1906_);
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
lean_dec(v_size_1906_);
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
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_size_1906_);
lean_dec_ref(v_e_1880_);
v_a_1928_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1910_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1910_);
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
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v_size_1906_);
lean_dec_ref(v_e_1880_);
v_a_1936_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1909_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1909_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_e_1880_);
v_a_1945_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1893_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1893_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___boxed(lean_object* v_e_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object* v_e_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar___boxed(lean_object* v_e_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVar(v_e_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec(v_a_1982_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object* v_a_1995_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_nat_to_int(v_a_1995_);
return v___x_1996_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object* v_msg_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v___x_2011_; lean_object* v___f_2012_; lean_object* v___x_40259__overap_2013_; lean_object* v___x_2014_; 
v___x_2011_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0);
v___f_2012_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2012_, 0, v___x_2011_);
v___x_40259__overap_2013_ = lean_panic_fn_borrowed(v___f_2012_, v_msg_1998_);
lean_dec_ref(v___f_2012_);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2008_);
lean_inc(v___y_2007_);
lean_inc_ref(v___y_2006_);
lean_inc(v___y_2005_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
lean_inc(v___y_2001_);
lean_inc(v___y_2000_);
lean_inc(v___y_1999_);
v___x_2014_ = lean_apply_12(v___x_40259__overap_2013_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, lean_box(0));
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object* v_msg_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_msg_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec(v___y_2016_);
return v_res_2028_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0));
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(lean_object* v_type_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; 
lean_inc_ref(v_type_2032_);
v___x_2039_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2052_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2052_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2052_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
if (lean_obj_tag(v_a_2040_) == 1)
{
lean_object* v_val_2044_; lean_object* v___x_2046_; 
lean_dec_ref(v_type_2032_);
v_val_2044_ = lean_ctor_get(v_a_2040_, 0);
lean_inc(v_val_2044_);
lean_dec_ref_known(v_a_2040_, 1);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v_val_2044_);
v___x_2046_ = v___x_2042_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_val_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_del_object(v___x_2042_);
lean_dec(v_a_2040_);
v___x_2048_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1);
v___x_2049_ = l_Lean_indentExpr(v_type_2032_);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2048_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_2050_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
return v___x_2051_;
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref(v_type_2032_);
v_a_2053_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2039_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2039_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_type_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(lean_object* v_type_2069_, lean_object* v_u_2070_, lean_object* v_instDeclName_2071_, lean_object* v_declName_2072_, lean_object* v_expectedInst_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2086_ = lean_box(0);
lean_inc_n(v_u_2070_, 2);
v___x_2087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2087_, 0, v_u_2070_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2088_, 0, v_u_2070_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2089_, 0, v_u_2070_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
lean_inc_ref(v___x_2089_);
v___x_2090_ = l_Lean_mkConst(v_instDeclName_2071_, v___x_2089_);
lean_inc_ref_n(v_type_2069_, 3);
v___x_2091_ = l_Lean_mkApp3(v___x_2090_, v_type_2069_, v_type_2069_, v_type_2069_);
v___x_2092_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2091_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc_n(v_a_2093_, 2);
lean_dec_ref_known(v___x_2092_, 1);
lean_inc(v_declName_2072_);
v___x_2094_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2072_, v_a_2093_, v_expectedInst_2073_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec_ref_known(v___x_2094_, 1);
v___x_2095_ = l_Lean_mkConst(v_declName_2072_, v___x_2089_);
lean_inc_ref_n(v_type_2069_, 2);
v___x_2096_ = l_Lean_mkApp4(v___x_2095_, v_type_2069_, v_type_2069_, v_type_2069_, v_a_2093_);
v___x_2097_ = l_Lean_Meta_Sym_canon(v___x_2096_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v___x_2099_ = l_Lean_Meta_Sym_shareCommon(v_a_2098_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
return v___x_2099_;
}
else
{
return v___x_2097_;
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v_a_2093_);
lean_dec_ref_known(v___x_2089_, 2);
lean_dec(v_declName_2072_);
lean_dec_ref(v_type_2069_);
v_a_2100_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2094_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2094_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2089_, 2);
lean_dec_ref(v_expectedInst_2073_);
lean_dec(v_declName_2072_);
lean_dec_ref(v_type_2069_);
return v___x_2092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_type_2108_ = _args[0];
lean_object* v_u_2109_ = _args[1];
lean_object* v_instDeclName_2110_ = _args[2];
lean_object* v_declName_2111_ = _args[3];
lean_object* v_expectedInst_2112_ = _args[4];
lean_object* v___y_2113_ = _args[5];
lean_object* v___y_2114_ = _args[6];
lean_object* v___y_2115_ = _args[7];
lean_object* v___y_2116_ = _args[8];
lean_object* v___y_2117_ = _args[9];
lean_object* v___y_2118_ = _args[10];
lean_object* v___y_2119_ = _args[11];
lean_object* v___y_2120_ = _args[12];
lean_object* v___y_2121_ = _args[13];
lean_object* v___y_2122_ = _args[14];
lean_object* v___y_2123_ = _args[15];
lean_object* v___y_2124_ = _args[16];
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2108_, v_u_2109_, v_instDeclName_2110_, v_declName_2111_, v_expectedInst_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec(v___y_2113_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object* v_a_2126_, lean_object* v_s_2127_){
_start:
{
lean_object* v_toRing_2128_; lean_object* v_invFn_x3f_2129_; lean_object* v_semiringId_x3f_2130_; lean_object* v_commSemiringInst_2131_; lean_object* v_commRingInst_2132_; lean_object* v_noZeroDivInst_x3f_2133_; lean_object* v_fieldInst_x3f_2134_; lean_object* v_powIdentityInst_x3f_2135_; lean_object* v_denoteEntries_2136_; lean_object* v_nextId_2137_; lean_object* v_steps_2138_; lean_object* v_queue_2139_; lean_object* v_basis_2140_; lean_object* v_diseqs_2141_; uint8_t v_recheck_2142_; lean_object* v_invSet_2143_; lean_object* v_powIdentityVarCount_2144_; lean_object* v_numEq0_x3f_2145_; uint8_t v_numEq0Updated_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2178_; 
v_toRing_2128_ = lean_ctor_get(v_s_2127_, 0);
v_invFn_x3f_2129_ = lean_ctor_get(v_s_2127_, 1);
v_semiringId_x3f_2130_ = lean_ctor_get(v_s_2127_, 2);
v_commSemiringInst_2131_ = lean_ctor_get(v_s_2127_, 3);
v_commRingInst_2132_ = lean_ctor_get(v_s_2127_, 4);
v_noZeroDivInst_x3f_2133_ = lean_ctor_get(v_s_2127_, 5);
v_fieldInst_x3f_2134_ = lean_ctor_get(v_s_2127_, 6);
v_powIdentityInst_x3f_2135_ = lean_ctor_get(v_s_2127_, 7);
v_denoteEntries_2136_ = lean_ctor_get(v_s_2127_, 8);
v_nextId_2137_ = lean_ctor_get(v_s_2127_, 9);
v_steps_2138_ = lean_ctor_get(v_s_2127_, 10);
v_queue_2139_ = lean_ctor_get(v_s_2127_, 11);
v_basis_2140_ = lean_ctor_get(v_s_2127_, 12);
v_diseqs_2141_ = lean_ctor_get(v_s_2127_, 13);
v_recheck_2142_ = lean_ctor_get_uint8(v_s_2127_, sizeof(void*)*17);
v_invSet_2143_ = lean_ctor_get(v_s_2127_, 14);
v_powIdentityVarCount_2144_ = lean_ctor_get(v_s_2127_, 15);
v_numEq0_x3f_2145_ = lean_ctor_get(v_s_2127_, 16);
v_numEq0Updated_2146_ = lean_ctor_get_uint8(v_s_2127_, sizeof(void*)*17 + 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_s_2127_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2148_ = v_s_2127_;
v_isShared_2149_ = v_isSharedCheck_2178_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_numEq0_x3f_2145_);
lean_inc(v_powIdentityVarCount_2144_);
lean_inc(v_invSet_2143_);
lean_inc(v_diseqs_2141_);
lean_inc(v_basis_2140_);
lean_inc(v_queue_2139_);
lean_inc(v_steps_2138_);
lean_inc(v_nextId_2137_);
lean_inc(v_denoteEntries_2136_);
lean_inc(v_powIdentityInst_x3f_2135_);
lean_inc(v_fieldInst_x3f_2134_);
lean_inc(v_noZeroDivInst_x3f_2133_);
lean_inc(v_commRingInst_2132_);
lean_inc(v_commSemiringInst_2131_);
lean_inc(v_semiringId_x3f_2130_);
lean_inc(v_invFn_x3f_2129_);
lean_inc(v_toRing_2128_);
lean_dec(v_s_2127_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2178_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_id_2150_; lean_object* v_type_2151_; lean_object* v_u_2152_; lean_object* v_ringInst_2153_; lean_object* v_semiringInst_2154_; lean_object* v_charInst_x3f_2155_; lean_object* v_addFn_x3f_2156_; lean_object* v_subFn_x3f_2157_; lean_object* v_negFn_x3f_2158_; lean_object* v_powFn_x3f_2159_; lean_object* v_intCastFn_x3f_2160_; lean_object* v_natCastFn_x3f_2161_; lean_object* v_one_x3f_2162_; lean_object* v_vars_2163_; lean_object* v_varMap_2164_; lean_object* v_denote_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2176_; 
v_id_2150_ = lean_ctor_get(v_toRing_2128_, 0);
v_type_2151_ = lean_ctor_get(v_toRing_2128_, 1);
v_u_2152_ = lean_ctor_get(v_toRing_2128_, 2);
v_ringInst_2153_ = lean_ctor_get(v_toRing_2128_, 3);
v_semiringInst_2154_ = lean_ctor_get(v_toRing_2128_, 4);
v_charInst_x3f_2155_ = lean_ctor_get(v_toRing_2128_, 5);
v_addFn_x3f_2156_ = lean_ctor_get(v_toRing_2128_, 6);
v_subFn_x3f_2157_ = lean_ctor_get(v_toRing_2128_, 8);
v_negFn_x3f_2158_ = lean_ctor_get(v_toRing_2128_, 9);
v_powFn_x3f_2159_ = lean_ctor_get(v_toRing_2128_, 10);
v_intCastFn_x3f_2160_ = lean_ctor_get(v_toRing_2128_, 11);
v_natCastFn_x3f_2161_ = lean_ctor_get(v_toRing_2128_, 12);
v_one_x3f_2162_ = lean_ctor_get(v_toRing_2128_, 13);
v_vars_2163_ = lean_ctor_get(v_toRing_2128_, 14);
v_varMap_2164_ = lean_ctor_get(v_toRing_2128_, 15);
v_denote_2165_ = lean_ctor_get(v_toRing_2128_, 16);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_toRing_2128_);
if (v_isSharedCheck_2176_ == 0)
{
lean_object* v_unused_2177_; 
v_unused_2177_ = lean_ctor_get(v_toRing_2128_, 7);
lean_dec(v_unused_2177_);
v___x_2167_ = v_toRing_2128_;
v_isShared_2168_ = v_isSharedCheck_2176_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_denote_2165_);
lean_inc(v_varMap_2164_);
lean_inc(v_vars_2163_);
lean_inc(v_one_x3f_2162_);
lean_inc(v_natCastFn_x3f_2161_);
lean_inc(v_intCastFn_x3f_2160_);
lean_inc(v_powFn_x3f_2159_);
lean_inc(v_negFn_x3f_2158_);
lean_inc(v_subFn_x3f_2157_);
lean_inc(v_addFn_x3f_2156_);
lean_inc(v_charInst_x3f_2155_);
lean_inc(v_semiringInst_2154_);
lean_inc(v_ringInst_2153_);
lean_inc(v_u_2152_);
lean_inc(v_type_2151_);
lean_inc(v_id_2150_);
lean_dec(v_toRing_2128_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2176_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2169_, 0, v_a_2126_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 7, v___x_2169_);
v___x_2171_ = v___x_2167_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_id_2150_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_type_2151_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_u_2152_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_ringInst_2153_);
lean_ctor_set(v_reuseFailAlloc_2175_, 4, v_semiringInst_2154_);
lean_ctor_set(v_reuseFailAlloc_2175_, 5, v_charInst_x3f_2155_);
lean_ctor_set(v_reuseFailAlloc_2175_, 6, v_addFn_x3f_2156_);
lean_ctor_set(v_reuseFailAlloc_2175_, 7, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2175_, 8, v_subFn_x3f_2157_);
lean_ctor_set(v_reuseFailAlloc_2175_, 9, v_negFn_x3f_2158_);
lean_ctor_set(v_reuseFailAlloc_2175_, 10, v_powFn_x3f_2159_);
lean_ctor_set(v_reuseFailAlloc_2175_, 11, v_intCastFn_x3f_2160_);
lean_ctor_set(v_reuseFailAlloc_2175_, 12, v_natCastFn_x3f_2161_);
lean_ctor_set(v_reuseFailAlloc_2175_, 13, v_one_x3f_2162_);
lean_ctor_set(v_reuseFailAlloc_2175_, 14, v_vars_2163_);
lean_ctor_set(v_reuseFailAlloc_2175_, 15, v_varMap_2164_);
lean_ctor_set(v_reuseFailAlloc_2175_, 16, v_denote_2165_);
v___x_2171_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2173_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2171_);
v___x_2173_ = v___x_2148_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_invFn_x3f_2129_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_semiringId_x3f_2130_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v_commSemiringInst_2131_);
lean_ctor_set(v_reuseFailAlloc_2174_, 4, v_commRingInst_2132_);
lean_ctor_set(v_reuseFailAlloc_2174_, 5, v_noZeroDivInst_x3f_2133_);
lean_ctor_set(v_reuseFailAlloc_2174_, 6, v_fieldInst_x3f_2134_);
lean_ctor_set(v_reuseFailAlloc_2174_, 7, v_powIdentityInst_x3f_2135_);
lean_ctor_set(v_reuseFailAlloc_2174_, 8, v_denoteEntries_2136_);
lean_ctor_set(v_reuseFailAlloc_2174_, 9, v_nextId_2137_);
lean_ctor_set(v_reuseFailAlloc_2174_, 10, v_steps_2138_);
lean_ctor_set(v_reuseFailAlloc_2174_, 11, v_queue_2139_);
lean_ctor_set(v_reuseFailAlloc_2174_, 12, v_basis_2140_);
lean_ctor_set(v_reuseFailAlloc_2174_, 13, v_diseqs_2141_);
lean_ctor_set(v_reuseFailAlloc_2174_, 14, v_invSet_2143_);
lean_ctor_set(v_reuseFailAlloc_2174_, 15, v_powIdentityVarCount_2144_);
lean_ctor_set(v_reuseFailAlloc_2174_, 16, v_numEq0_x3f_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*17, v_recheck_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*17 + 1, v_numEq0Updated_2146_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2235_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2235_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2235_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v_toRing_2196_; lean_object* v_mulFn_x3f_2197_; 
v_toRing_2196_ = lean_ctor_get(v_a_2192_, 0);
lean_inc_ref(v_toRing_2196_);
lean_dec(v_a_2192_);
v_mulFn_x3f_2197_ = lean_ctor_get(v_toRing_2196_, 7);
if (lean_obj_tag(v_mulFn_x3f_2197_) == 1)
{
lean_object* v_val_2198_; lean_object* v___x_2200_; 
lean_inc_ref(v_mulFn_x3f_2197_);
lean_dec_ref(v_toRing_2196_);
v_val_2198_ = lean_ctor_get(v_mulFn_x3f_2197_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v_mulFn_x3f_2197_, 1);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v_val_2198_);
v___x_2200_ = v___x_2194_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_val_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
else
{
lean_object* v_type_2202_; lean_object* v_u_2203_; lean_object* v_semiringInst_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_expectedInst_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
lean_del_object(v___x_2194_);
v_type_2202_ = lean_ctor_get(v_toRing_2196_, 1);
lean_inc_ref_n(v_type_2202_, 3);
v_u_2203_ = lean_ctor_get(v_toRing_2196_, 2);
lean_inc_n(v_u_2203_, 2);
v_semiringInst_2204_ = lean_ctor_get(v_toRing_2196_, 4);
lean_inc_ref(v_semiringInst_2204_);
lean_dec_ref(v_toRing_2196_);
v___x_2205_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_2206_ = lean_box(0);
v___x_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_u_2203_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
lean_inc_ref(v___x_2207_);
v___x_2208_ = l_Lean_mkConst(v___x_2205_, v___x_2207_);
v___x_2209_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_2210_ = l_Lean_mkConst(v___x_2209_, v___x_2207_);
v___x_2211_ = l_Lean_mkAppB(v___x_2210_, v_type_2202_, v_semiringInst_2204_);
v_expectedInst_2212_ = l_Lean_mkAppB(v___x_2208_, v_type_2202_, v___x_2211_);
v___x_2213_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_2214_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_2215_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2202_, v_u_2203_, v___x_2213_, v___x_2214_, v_expectedInst_2212_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___f_2217_; lean_object* v___x_2218_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc_n(v_a_2216_, 2);
lean_dec_ref_known(v___x_2215_, 1);
v___f_2217_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2217_, 0, v_a_2216_);
v___x_2218_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2217_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v___x_2218_, 0);
lean_dec(v_unused_2226_);
v___x_2220_ = v___x_2218_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_dec(v___x_2218_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v_a_2216_);
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2216_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_a_2216_);
v_a_2227_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2218_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2218_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
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
else
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
v_a_2236_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2191_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2191_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec(v___y_2244_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object* v_a_2257_, lean_object* v_s_2258_){
_start:
{
lean_object* v_toRing_2259_; lean_object* v_invFn_x3f_2260_; lean_object* v_semiringId_x3f_2261_; lean_object* v_commSemiringInst_2262_; lean_object* v_commRingInst_2263_; lean_object* v_noZeroDivInst_x3f_2264_; lean_object* v_fieldInst_x3f_2265_; lean_object* v_powIdentityInst_x3f_2266_; lean_object* v_denoteEntries_2267_; lean_object* v_nextId_2268_; lean_object* v_steps_2269_; lean_object* v_queue_2270_; lean_object* v_basis_2271_; lean_object* v_diseqs_2272_; uint8_t v_recheck_2273_; lean_object* v_invSet_2274_; lean_object* v_powIdentityVarCount_2275_; lean_object* v_numEq0_x3f_2276_; uint8_t v_numEq0Updated_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2309_; 
v_toRing_2259_ = lean_ctor_get(v_s_2258_, 0);
v_invFn_x3f_2260_ = lean_ctor_get(v_s_2258_, 1);
v_semiringId_x3f_2261_ = lean_ctor_get(v_s_2258_, 2);
v_commSemiringInst_2262_ = lean_ctor_get(v_s_2258_, 3);
v_commRingInst_2263_ = lean_ctor_get(v_s_2258_, 4);
v_noZeroDivInst_x3f_2264_ = lean_ctor_get(v_s_2258_, 5);
v_fieldInst_x3f_2265_ = lean_ctor_get(v_s_2258_, 6);
v_powIdentityInst_x3f_2266_ = lean_ctor_get(v_s_2258_, 7);
v_denoteEntries_2267_ = lean_ctor_get(v_s_2258_, 8);
v_nextId_2268_ = lean_ctor_get(v_s_2258_, 9);
v_steps_2269_ = lean_ctor_get(v_s_2258_, 10);
v_queue_2270_ = lean_ctor_get(v_s_2258_, 11);
v_basis_2271_ = lean_ctor_get(v_s_2258_, 12);
v_diseqs_2272_ = lean_ctor_get(v_s_2258_, 13);
v_recheck_2273_ = lean_ctor_get_uint8(v_s_2258_, sizeof(void*)*17);
v_invSet_2274_ = lean_ctor_get(v_s_2258_, 14);
v_powIdentityVarCount_2275_ = lean_ctor_get(v_s_2258_, 15);
v_numEq0_x3f_2276_ = lean_ctor_get(v_s_2258_, 16);
v_numEq0Updated_2277_ = lean_ctor_get_uint8(v_s_2258_, sizeof(void*)*17 + 1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_s_2258_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2279_ = v_s_2258_;
v_isShared_2280_ = v_isSharedCheck_2309_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_numEq0_x3f_2276_);
lean_inc(v_powIdentityVarCount_2275_);
lean_inc(v_invSet_2274_);
lean_inc(v_diseqs_2272_);
lean_inc(v_basis_2271_);
lean_inc(v_queue_2270_);
lean_inc(v_steps_2269_);
lean_inc(v_nextId_2268_);
lean_inc(v_denoteEntries_2267_);
lean_inc(v_powIdentityInst_x3f_2266_);
lean_inc(v_fieldInst_x3f_2265_);
lean_inc(v_noZeroDivInst_x3f_2264_);
lean_inc(v_commRingInst_2263_);
lean_inc(v_commSemiringInst_2262_);
lean_inc(v_semiringId_x3f_2261_);
lean_inc(v_invFn_x3f_2260_);
lean_inc(v_toRing_2259_);
lean_dec(v_s_2258_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2309_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v_id_2281_; lean_object* v_type_2282_; lean_object* v_u_2283_; lean_object* v_ringInst_2284_; lean_object* v_semiringInst_2285_; lean_object* v_charInst_x3f_2286_; lean_object* v_mulFn_x3f_2287_; lean_object* v_subFn_x3f_2288_; lean_object* v_negFn_x3f_2289_; lean_object* v_powFn_x3f_2290_; lean_object* v_intCastFn_x3f_2291_; lean_object* v_natCastFn_x3f_2292_; lean_object* v_one_x3f_2293_; lean_object* v_vars_2294_; lean_object* v_varMap_2295_; lean_object* v_denote_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2307_; 
v_id_2281_ = lean_ctor_get(v_toRing_2259_, 0);
v_type_2282_ = lean_ctor_get(v_toRing_2259_, 1);
v_u_2283_ = lean_ctor_get(v_toRing_2259_, 2);
v_ringInst_2284_ = lean_ctor_get(v_toRing_2259_, 3);
v_semiringInst_2285_ = lean_ctor_get(v_toRing_2259_, 4);
v_charInst_x3f_2286_ = lean_ctor_get(v_toRing_2259_, 5);
v_mulFn_x3f_2287_ = lean_ctor_get(v_toRing_2259_, 7);
v_subFn_x3f_2288_ = lean_ctor_get(v_toRing_2259_, 8);
v_negFn_x3f_2289_ = lean_ctor_get(v_toRing_2259_, 9);
v_powFn_x3f_2290_ = lean_ctor_get(v_toRing_2259_, 10);
v_intCastFn_x3f_2291_ = lean_ctor_get(v_toRing_2259_, 11);
v_natCastFn_x3f_2292_ = lean_ctor_get(v_toRing_2259_, 12);
v_one_x3f_2293_ = lean_ctor_get(v_toRing_2259_, 13);
v_vars_2294_ = lean_ctor_get(v_toRing_2259_, 14);
v_varMap_2295_ = lean_ctor_get(v_toRing_2259_, 15);
v_denote_2296_ = lean_ctor_get(v_toRing_2259_, 16);
v_isSharedCheck_2307_ = !lean_is_exclusive(v_toRing_2259_);
if (v_isSharedCheck_2307_ == 0)
{
lean_object* v_unused_2308_; 
v_unused_2308_ = lean_ctor_get(v_toRing_2259_, 6);
lean_dec(v_unused_2308_);
v___x_2298_ = v_toRing_2259_;
v_isShared_2299_ = v_isSharedCheck_2307_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_denote_2296_);
lean_inc(v_varMap_2295_);
lean_inc(v_vars_2294_);
lean_inc(v_one_x3f_2293_);
lean_inc(v_natCastFn_x3f_2292_);
lean_inc(v_intCastFn_x3f_2291_);
lean_inc(v_powFn_x3f_2290_);
lean_inc(v_negFn_x3f_2289_);
lean_inc(v_subFn_x3f_2288_);
lean_inc(v_mulFn_x3f_2287_);
lean_inc(v_charInst_x3f_2286_);
lean_inc(v_semiringInst_2285_);
lean_inc(v_ringInst_2284_);
lean_inc(v_u_2283_);
lean_inc(v_type_2282_);
lean_inc(v_id_2281_);
lean_dec(v_toRing_2259_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2307_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v_a_2257_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 6, v___x_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_id_2281_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_type_2282_);
lean_ctor_set(v_reuseFailAlloc_2306_, 2, v_u_2283_);
lean_ctor_set(v_reuseFailAlloc_2306_, 3, v_ringInst_2284_);
lean_ctor_set(v_reuseFailAlloc_2306_, 4, v_semiringInst_2285_);
lean_ctor_set(v_reuseFailAlloc_2306_, 5, v_charInst_x3f_2286_);
lean_ctor_set(v_reuseFailAlloc_2306_, 6, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2306_, 7, v_mulFn_x3f_2287_);
lean_ctor_set(v_reuseFailAlloc_2306_, 8, v_subFn_x3f_2288_);
lean_ctor_set(v_reuseFailAlloc_2306_, 9, v_negFn_x3f_2289_);
lean_ctor_set(v_reuseFailAlloc_2306_, 10, v_powFn_x3f_2290_);
lean_ctor_set(v_reuseFailAlloc_2306_, 11, v_intCastFn_x3f_2291_);
lean_ctor_set(v_reuseFailAlloc_2306_, 12, v_natCastFn_x3f_2292_);
lean_ctor_set(v_reuseFailAlloc_2306_, 13, v_one_x3f_2293_);
lean_ctor_set(v_reuseFailAlloc_2306_, 14, v_vars_2294_);
lean_ctor_set(v_reuseFailAlloc_2306_, 15, v_varMap_2295_);
lean_ctor_set(v_reuseFailAlloc_2306_, 16, v_denote_2296_);
v___x_2302_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2304_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2302_);
v___x_2304_ = v___x_2279_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_invFn_x3f_2260_);
lean_ctor_set(v_reuseFailAlloc_2305_, 2, v_semiringId_x3f_2261_);
lean_ctor_set(v_reuseFailAlloc_2305_, 3, v_commSemiringInst_2262_);
lean_ctor_set(v_reuseFailAlloc_2305_, 4, v_commRingInst_2263_);
lean_ctor_set(v_reuseFailAlloc_2305_, 5, v_noZeroDivInst_x3f_2264_);
lean_ctor_set(v_reuseFailAlloc_2305_, 6, v_fieldInst_x3f_2265_);
lean_ctor_set(v_reuseFailAlloc_2305_, 7, v_powIdentityInst_x3f_2266_);
lean_ctor_set(v_reuseFailAlloc_2305_, 8, v_denoteEntries_2267_);
lean_ctor_set(v_reuseFailAlloc_2305_, 9, v_nextId_2268_);
lean_ctor_set(v_reuseFailAlloc_2305_, 10, v_steps_2269_);
lean_ctor_set(v_reuseFailAlloc_2305_, 11, v_queue_2270_);
lean_ctor_set(v_reuseFailAlloc_2305_, 12, v_basis_2271_);
lean_ctor_set(v_reuseFailAlloc_2305_, 13, v_diseqs_2272_);
lean_ctor_set(v_reuseFailAlloc_2305_, 14, v_invSet_2274_);
lean_ctor_set(v_reuseFailAlloc_2305_, 15, v_powIdentityVarCount_2275_);
lean_ctor_set(v_reuseFailAlloc_2305_, 16, v_numEq0_x3f_2276_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, sizeof(void*)*17, v_recheck_2273_);
lean_ctor_set_uint8(v_reuseFailAlloc_2305_, sizeof(void*)*17 + 1, v_numEq0Updated_2277_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2366_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2366_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2366_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v_toRing_2327_; lean_object* v_addFn_x3f_2328_; 
v_toRing_2327_ = lean_ctor_get(v_a_2323_, 0);
lean_inc_ref(v_toRing_2327_);
lean_dec(v_a_2323_);
v_addFn_x3f_2328_ = lean_ctor_get(v_toRing_2327_, 6);
if (lean_obj_tag(v_addFn_x3f_2328_) == 1)
{
lean_object* v_val_2329_; lean_object* v___x_2331_; 
lean_inc_ref(v_addFn_x3f_2328_);
lean_dec_ref(v_toRing_2327_);
v_val_2329_ = lean_ctor_get(v_addFn_x3f_2328_, 0);
lean_inc(v_val_2329_);
lean_dec_ref_known(v_addFn_x3f_2328_, 1);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v_val_2329_);
v___x_2331_ = v___x_2325_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_val_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
else
{
lean_object* v_type_2333_; lean_object* v_u_2334_; lean_object* v_semiringInst_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v_expectedInst_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_del_object(v___x_2325_);
v_type_2333_ = lean_ctor_get(v_toRing_2327_, 1);
lean_inc_ref_n(v_type_2333_, 3);
v_u_2334_ = lean_ctor_get(v_toRing_2327_, 2);
lean_inc_n(v_u_2334_, 2);
v_semiringInst_2335_ = lean_ctor_get(v_toRing_2327_, 4);
lean_inc_ref(v_semiringInst_2335_);
lean_dec_ref(v_toRing_2327_);
v___x_2336_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_2337_ = lean_box(0);
v___x_2338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2338_, 0, v_u_2334_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
lean_inc_ref(v___x_2338_);
v___x_2339_ = l_Lean_mkConst(v___x_2336_, v___x_2338_);
v___x_2340_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_2341_ = l_Lean_mkConst(v___x_2340_, v___x_2338_);
v___x_2342_ = l_Lean_mkAppB(v___x_2341_, v_type_2333_, v_semiringInst_2335_);
v_expectedInst_2343_ = l_Lean_mkAppB(v___x_2339_, v_type_2333_, v___x_2342_);
v___x_2344_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_2345_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_2346_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2333_, v_u_2334_, v___x_2344_, v___x_2345_, v_expectedInst_2343_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___f_2348_; lean_object* v___x_2349_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc_n(v_a_2347_, 2);
lean_dec_ref_known(v___x_2346_, 1);
v___f_2348_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_2348_, 0, v_a_2347_);
v___x_2349_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2348_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2356_ == 0)
{
lean_object* v_unused_2357_; 
v_unused_2357_ = lean_ctor_get(v___x_2349_, 0);
lean_dec(v_unused_2357_);
v___x_2351_ = v___x_2349_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_dec(v___x_2349_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v_a_2347_);
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2347_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v_a_2347_);
v_a_2358_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2349_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2349_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
else
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
v_a_2367_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2322_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2322_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(lean_object* v_type_2388_, lean_object* v_u_2389_, lean_object* v_instDeclName_2390_, lean_object* v_declName_2391_, lean_object* v_expectedInst_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2405_ = lean_box(0);
v___x_2406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2406_, 0, v_u_2389_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
lean_inc_ref(v___x_2406_);
v___x_2407_ = l_Lean_mkConst(v_instDeclName_2390_, v___x_2406_);
lean_inc_ref(v_type_2388_);
v___x_2408_ = l_Lean_Expr_app___override(v___x_2407_, v_type_2388_);
v___x_2409_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2408_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2411_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc_n(v_a_2410_, 2);
lean_dec_ref_known(v___x_2409_, 1);
lean_inc(v_declName_2391_);
v___x_2411_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2391_, v_a_2410_, v_expectedInst_2392_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
lean_dec_ref_known(v___x_2411_, 1);
v___x_2412_ = l_Lean_mkConst(v_declName_2391_, v___x_2406_);
v___x_2413_ = l_Lean_mkAppB(v___x_2412_, v_type_2388_, v_a_2410_);
v___x_2414_ = l_Lean_Meta_Sym_canon(v___x_2413_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2416_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
v___x_2416_ = l_Lean_Meta_Sym_shareCommon(v_a_2415_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
return v___x_2416_;
}
else
{
return v___x_2414_;
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v_a_2410_);
lean_dec_ref_known(v___x_2406_, 2);
lean_dec(v_declName_2391_);
lean_dec_ref(v_type_2388_);
v_a_2417_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2411_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2411_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2406_, 2);
lean_dec_ref(v_expectedInst_2392_);
lean_dec(v_declName_2391_);
lean_dec_ref(v_type_2388_);
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_type_2425_ = _args[0];
lean_object* v_u_2426_ = _args[1];
lean_object* v_instDeclName_2427_ = _args[2];
lean_object* v_declName_2428_ = _args[3];
lean_object* v_expectedInst_2429_ = _args[4];
lean_object* v___y_2430_ = _args[5];
lean_object* v___y_2431_ = _args[6];
lean_object* v___y_2432_ = _args[7];
lean_object* v___y_2433_ = _args[8];
lean_object* v___y_2434_ = _args[9];
lean_object* v___y_2435_ = _args[10];
lean_object* v___y_2436_ = _args[11];
lean_object* v___y_2437_ = _args[12];
lean_object* v___y_2438_ = _args[13];
lean_object* v___y_2439_ = _args[14];
lean_object* v___y_2440_ = _args[15];
lean_object* v___y_2441_ = _args[16];
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2425_, v_u_2426_, v_instDeclName_2427_, v_declName_2428_, v_expectedInst_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec(v___y_2430_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object* v_a_2443_, lean_object* v_s_2444_){
_start:
{
lean_object* v_toRing_2445_; lean_object* v_invFn_x3f_2446_; lean_object* v_semiringId_x3f_2447_; lean_object* v_commSemiringInst_2448_; lean_object* v_commRingInst_2449_; lean_object* v_noZeroDivInst_x3f_2450_; lean_object* v_fieldInst_x3f_2451_; lean_object* v_powIdentityInst_x3f_2452_; lean_object* v_denoteEntries_2453_; lean_object* v_nextId_2454_; lean_object* v_steps_2455_; lean_object* v_queue_2456_; lean_object* v_basis_2457_; lean_object* v_diseqs_2458_; uint8_t v_recheck_2459_; lean_object* v_invSet_2460_; lean_object* v_powIdentityVarCount_2461_; lean_object* v_numEq0_x3f_2462_; uint8_t v_numEq0Updated_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2495_; 
v_toRing_2445_ = lean_ctor_get(v_s_2444_, 0);
v_invFn_x3f_2446_ = lean_ctor_get(v_s_2444_, 1);
v_semiringId_x3f_2447_ = lean_ctor_get(v_s_2444_, 2);
v_commSemiringInst_2448_ = lean_ctor_get(v_s_2444_, 3);
v_commRingInst_2449_ = lean_ctor_get(v_s_2444_, 4);
v_noZeroDivInst_x3f_2450_ = lean_ctor_get(v_s_2444_, 5);
v_fieldInst_x3f_2451_ = lean_ctor_get(v_s_2444_, 6);
v_powIdentityInst_x3f_2452_ = lean_ctor_get(v_s_2444_, 7);
v_denoteEntries_2453_ = lean_ctor_get(v_s_2444_, 8);
v_nextId_2454_ = lean_ctor_get(v_s_2444_, 9);
v_steps_2455_ = lean_ctor_get(v_s_2444_, 10);
v_queue_2456_ = lean_ctor_get(v_s_2444_, 11);
v_basis_2457_ = lean_ctor_get(v_s_2444_, 12);
v_diseqs_2458_ = lean_ctor_get(v_s_2444_, 13);
v_recheck_2459_ = lean_ctor_get_uint8(v_s_2444_, sizeof(void*)*17);
v_invSet_2460_ = lean_ctor_get(v_s_2444_, 14);
v_powIdentityVarCount_2461_ = lean_ctor_get(v_s_2444_, 15);
v_numEq0_x3f_2462_ = lean_ctor_get(v_s_2444_, 16);
v_numEq0Updated_2463_ = lean_ctor_get_uint8(v_s_2444_, sizeof(void*)*17 + 1);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_s_2444_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2465_ = v_s_2444_;
v_isShared_2466_ = v_isSharedCheck_2495_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_numEq0_x3f_2462_);
lean_inc(v_powIdentityVarCount_2461_);
lean_inc(v_invSet_2460_);
lean_inc(v_diseqs_2458_);
lean_inc(v_basis_2457_);
lean_inc(v_queue_2456_);
lean_inc(v_steps_2455_);
lean_inc(v_nextId_2454_);
lean_inc(v_denoteEntries_2453_);
lean_inc(v_powIdentityInst_x3f_2452_);
lean_inc(v_fieldInst_x3f_2451_);
lean_inc(v_noZeroDivInst_x3f_2450_);
lean_inc(v_commRingInst_2449_);
lean_inc(v_commSemiringInst_2448_);
lean_inc(v_semiringId_x3f_2447_);
lean_inc(v_invFn_x3f_2446_);
lean_inc(v_toRing_2445_);
lean_dec(v_s_2444_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2495_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v_id_2467_; lean_object* v_type_2468_; lean_object* v_u_2469_; lean_object* v_ringInst_2470_; lean_object* v_semiringInst_2471_; lean_object* v_charInst_x3f_2472_; lean_object* v_addFn_x3f_2473_; lean_object* v_mulFn_x3f_2474_; lean_object* v_subFn_x3f_2475_; lean_object* v_powFn_x3f_2476_; lean_object* v_intCastFn_x3f_2477_; lean_object* v_natCastFn_x3f_2478_; lean_object* v_one_x3f_2479_; lean_object* v_vars_2480_; lean_object* v_varMap_2481_; lean_object* v_denote_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2493_; 
v_id_2467_ = lean_ctor_get(v_toRing_2445_, 0);
v_type_2468_ = lean_ctor_get(v_toRing_2445_, 1);
v_u_2469_ = lean_ctor_get(v_toRing_2445_, 2);
v_ringInst_2470_ = lean_ctor_get(v_toRing_2445_, 3);
v_semiringInst_2471_ = lean_ctor_get(v_toRing_2445_, 4);
v_charInst_x3f_2472_ = lean_ctor_get(v_toRing_2445_, 5);
v_addFn_x3f_2473_ = lean_ctor_get(v_toRing_2445_, 6);
v_mulFn_x3f_2474_ = lean_ctor_get(v_toRing_2445_, 7);
v_subFn_x3f_2475_ = lean_ctor_get(v_toRing_2445_, 8);
v_powFn_x3f_2476_ = lean_ctor_get(v_toRing_2445_, 10);
v_intCastFn_x3f_2477_ = lean_ctor_get(v_toRing_2445_, 11);
v_natCastFn_x3f_2478_ = lean_ctor_get(v_toRing_2445_, 12);
v_one_x3f_2479_ = lean_ctor_get(v_toRing_2445_, 13);
v_vars_2480_ = lean_ctor_get(v_toRing_2445_, 14);
v_varMap_2481_ = lean_ctor_get(v_toRing_2445_, 15);
v_denote_2482_ = lean_ctor_get(v_toRing_2445_, 16);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_toRing_2445_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v_toRing_2445_, 9);
lean_dec(v_unused_2494_);
v___x_2484_ = v_toRing_2445_;
v_isShared_2485_ = v_isSharedCheck_2493_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_denote_2482_);
lean_inc(v_varMap_2481_);
lean_inc(v_vars_2480_);
lean_inc(v_one_x3f_2479_);
lean_inc(v_natCastFn_x3f_2478_);
lean_inc(v_intCastFn_x3f_2477_);
lean_inc(v_powFn_x3f_2476_);
lean_inc(v_subFn_x3f_2475_);
lean_inc(v_mulFn_x3f_2474_);
lean_inc(v_addFn_x3f_2473_);
lean_inc(v_charInst_x3f_2472_);
lean_inc(v_semiringInst_2471_);
lean_inc(v_ringInst_2470_);
lean_inc(v_u_2469_);
lean_inc(v_type_2468_);
lean_inc(v_id_2467_);
lean_dec(v_toRing_2445_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2493_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2486_, 0, v_a_2443_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 9, v___x_2486_);
v___x_2488_ = v___x_2484_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_id_2467_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_type_2468_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_u_2469_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_ringInst_2470_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_semiringInst_2471_);
lean_ctor_set(v_reuseFailAlloc_2492_, 5, v_charInst_x3f_2472_);
lean_ctor_set(v_reuseFailAlloc_2492_, 6, v_addFn_x3f_2473_);
lean_ctor_set(v_reuseFailAlloc_2492_, 7, v_mulFn_x3f_2474_);
lean_ctor_set(v_reuseFailAlloc_2492_, 8, v_subFn_x3f_2475_);
lean_ctor_set(v_reuseFailAlloc_2492_, 9, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2492_, 10, v_powFn_x3f_2476_);
lean_ctor_set(v_reuseFailAlloc_2492_, 11, v_intCastFn_x3f_2477_);
lean_ctor_set(v_reuseFailAlloc_2492_, 12, v_natCastFn_x3f_2478_);
lean_ctor_set(v_reuseFailAlloc_2492_, 13, v_one_x3f_2479_);
lean_ctor_set(v_reuseFailAlloc_2492_, 14, v_vars_2480_);
lean_ctor_set(v_reuseFailAlloc_2492_, 15, v_varMap_2481_);
lean_ctor_set(v_reuseFailAlloc_2492_, 16, v_denote_2482_);
v___x_2488_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2490_; 
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2488_);
v___x_2490_ = v___x_2465_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_invFn_x3f_2446_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_semiringId_x3f_2447_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_commSemiringInst_2448_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_commRingInst_2449_);
lean_ctor_set(v_reuseFailAlloc_2491_, 5, v_noZeroDivInst_x3f_2450_);
lean_ctor_set(v_reuseFailAlloc_2491_, 6, v_fieldInst_x3f_2451_);
lean_ctor_set(v_reuseFailAlloc_2491_, 7, v_powIdentityInst_x3f_2452_);
lean_ctor_set(v_reuseFailAlloc_2491_, 8, v_denoteEntries_2453_);
lean_ctor_set(v_reuseFailAlloc_2491_, 9, v_nextId_2454_);
lean_ctor_set(v_reuseFailAlloc_2491_, 10, v_steps_2455_);
lean_ctor_set(v_reuseFailAlloc_2491_, 11, v_queue_2456_);
lean_ctor_set(v_reuseFailAlloc_2491_, 12, v_basis_2457_);
lean_ctor_set(v_reuseFailAlloc_2491_, 13, v_diseqs_2458_);
lean_ctor_set(v_reuseFailAlloc_2491_, 14, v_invSet_2460_);
lean_ctor_set(v_reuseFailAlloc_2491_, 15, v_powIdentityVarCount_2461_);
lean_ctor_set(v_reuseFailAlloc_2491_, 16, v_numEq0_x3f_2462_);
lean_ctor_set_uint8(v_reuseFailAlloc_2491_, sizeof(void*)*17, v_recheck_2459_);
lean_ctor_set_uint8(v_reuseFailAlloc_2491_, sizeof(void*)*17 + 1, v_numEq0Updated_2463_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2562_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2562_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2562_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v_toRing_2526_; lean_object* v_negFn_x3f_2527_; 
v_toRing_2526_ = lean_ctor_get(v_a_2522_, 0);
lean_inc_ref(v_toRing_2526_);
lean_dec(v_a_2522_);
v_negFn_x3f_2527_ = lean_ctor_get(v_toRing_2526_, 9);
if (lean_obj_tag(v_negFn_x3f_2527_) == 1)
{
lean_object* v_val_2528_; lean_object* v___x_2530_; 
lean_inc_ref(v_negFn_x3f_2527_);
lean_dec_ref(v_toRing_2526_);
v_val_2528_ = lean_ctor_get(v_negFn_x3f_2527_, 0);
lean_inc(v_val_2528_);
lean_dec_ref_known(v_negFn_x3f_2527_, 1);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v_val_2528_);
v___x_2530_ = v___x_2524_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_val_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
else
{
lean_object* v_type_2532_; lean_object* v_u_2533_; lean_object* v_ringInst_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v_expectedInst_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_del_object(v___x_2524_);
v_type_2532_ = lean_ctor_get(v_toRing_2526_, 1);
lean_inc_ref_n(v_type_2532_, 2);
v_u_2533_ = lean_ctor_get(v_toRing_2526_, 2);
lean_inc_n(v_u_2533_, 2);
v_ringInst_2534_ = lean_ctor_get(v_toRing_2526_, 3);
lean_inc_ref(v_ringInst_2534_);
lean_dec_ref(v_toRing_2526_);
v___x_2535_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1));
v___x_2536_ = lean_box(0);
v___x_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2537_, 0, v_u_2533_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = l_Lean_mkConst(v___x_2535_, v___x_2537_);
v_expectedInst_2539_ = l_Lean_mkAppB(v___x_2538_, v_type_2532_, v_ringInst_2534_);
v___x_2540_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3));
v___x_2541_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5));
v___x_2542_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2532_, v_u_2533_, v___x_2540_, v___x_2541_, v_expectedInst_2539_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___f_2544_; lean_object* v___x_2545_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc_n(v_a_2543_, 2);
lean_dec_ref_known(v___x_2542_, 1);
v___f_2544_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_2544_, 0, v_a_2543_);
v___x_2545_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2544_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; 
v_unused_2553_ = lean_ctor_get(v___x_2545_, 0);
lean_dec(v_unused_2553_);
v___x_2547_ = v___x_2545_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_dec(v___x_2545_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v_a_2543_);
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2543_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec(v_a_2543_);
v_a_2554_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2545_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2545_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
else
{
return v___x_2542_;
}
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v_a_2563_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2521_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2521_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec(v___y_2571_);
return v_res_2583_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = lean_nat_to_int(v___x_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object* v_k_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v_toRing_2613_; lean_object* v_type_2614_; lean_object* v_u_2615_; lean_object* v_semiringInst_2616_; lean_object* v___x_2617_; lean_object* v_n_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v_toRing_2613_ = lean_ctor_get(v_a_2612_, 0);
lean_inc_ref(v_toRing_2613_);
lean_dec(v_a_2612_);
v_type_2614_ = lean_ctor_get(v_toRing_2613_, 1);
lean_inc_ref_n(v_type_2614_, 2);
v_u_2615_ = lean_ctor_get(v_toRing_2613_, 2);
lean_inc(v_u_2615_);
v_semiringInst_2616_ = lean_ctor_get(v_toRing_2613_, 4);
lean_inc_ref(v_semiringInst_2616_);
lean_dec_ref(v_toRing_2613_);
v___x_2617_ = lean_nat_abs(v_k_2598_);
v_n_2618_ = l_Lean_mkRawNatLit(v___x_2617_);
v___x_2619_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1));
v___x_2620_ = lean_box(0);
v___x_2621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2621_, 0, v_u_2615_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
lean_inc_ref(v___x_2621_);
v___x_2622_ = l_Lean_mkConst(v___x_2619_, v___x_2621_);
lean_inc_ref(v_n_2618_);
v___x_2623_ = l_Lean_mkAppB(v___x_2622_, v_type_2614_, v_n_2618_);
v___x_2624_ = lean_box(0);
v___x_2625_ = l_Lean_Meta_synthInstance_x3f(v___x_2623_, v___x_2624_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2665_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2665_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2665_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v_ofNatInst_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; 
if (lean_obj_tag(v_a_2626_) == 1)
{
lean_object* v_val_2661_; 
lean_dec_ref(v_semiringInst_2616_);
v_val_2661_ = lean_ctor_get(v_a_2626_, 0);
lean_inc(v_val_2661_);
lean_dec_ref_known(v_a_2626_, 1);
v_ofNatInst_2631_ = v_val_2661_;
v___y_2632_ = v___y_2599_;
v___y_2633_ = v___y_2600_;
v___y_2634_ = v___y_2601_;
v___y_2635_ = v___y_2602_;
v___y_2636_ = v___y_2603_;
v___y_2637_ = v___y_2604_;
v___y_2638_ = v___y_2605_;
v___y_2639_ = v___y_2606_;
v___y_2640_ = v___y_2607_;
v___y_2641_ = v___y_2608_;
v___y_2642_ = v___y_2609_;
goto v___jp_2630_;
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
lean_dec(v_a_2626_);
v___x_2662_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5));
lean_inc_ref(v___x_2621_);
v___x_2663_ = l_Lean_mkConst(v___x_2662_, v___x_2621_);
lean_inc_ref(v_n_2618_);
lean_inc_ref(v_type_2614_);
v___x_2664_ = l_Lean_mkApp3(v___x_2663_, v_type_2614_, v_semiringInst_2616_, v_n_2618_);
v_ofNatInst_2631_ = v___x_2664_;
v___y_2632_ = v___y_2599_;
v___y_2633_ = v___y_2600_;
v___y_2634_ = v___y_2601_;
v___y_2635_ = v___y_2602_;
v___y_2636_ = v___y_2603_;
v___y_2637_ = v___y_2604_;
v___y_2638_ = v___y_2605_;
v___y_2639_ = v___y_2606_;
v___y_2640_ = v___y_2607_;
v___y_2641_ = v___y_2608_;
v___y_2642_ = v___y_2609_;
goto v___jp_2630_;
}
v___jp_2630_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v_n_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2643_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3));
v___x_2644_ = l_Lean_mkConst(v___x_2643_, v___x_2621_);
v_n_2645_ = l_Lean_mkApp3(v___x_2644_, v_type_2614_, v_n_2618_, v_ofNatInst_2631_);
v___x_2646_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4);
v___x_2647_ = lean_int_dec_lt(v_k_2598_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2649_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v_n_2645_);
v___x_2649_ = v___x_2628_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_n_2645_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
else
{
lean_object* v___x_2651_; 
lean_del_object(v___x_2628_);
v___x_2651_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2660_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2654_ = v___x_2651_;
v_isShared_2655_ = v_isSharedCheck_2660_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2651_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2660_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2656_ = l_Lean_Expr_app___override(v_a_2652_, v_n_2645_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2656_);
v___x_2658_ = v___x_2654_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
else
{
lean_dec_ref(v_n_2645_);
return v___x_2651_;
}
}
}
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec_ref_known(v___x_2621_, 2);
lean_dec_ref(v_n_2618_);
lean_dec_ref(v_semiringInst_2616_);
lean_dec_ref(v_type_2614_);
v_a_2666_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2625_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2625_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
v_a_2674_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2611_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2611_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object* v_k_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec(v_k_2682_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object* v_a_2696_, lean_object* v_s_2697_){
_start:
{
lean_object* v_toRing_2698_; lean_object* v_invFn_x3f_2699_; lean_object* v_semiringId_x3f_2700_; lean_object* v_commSemiringInst_2701_; lean_object* v_commRingInst_2702_; lean_object* v_noZeroDivInst_x3f_2703_; lean_object* v_fieldInst_x3f_2704_; lean_object* v_powIdentityInst_x3f_2705_; lean_object* v_denoteEntries_2706_; lean_object* v_nextId_2707_; lean_object* v_steps_2708_; lean_object* v_queue_2709_; lean_object* v_basis_2710_; lean_object* v_diseqs_2711_; uint8_t v_recheck_2712_; lean_object* v_invSet_2713_; lean_object* v_powIdentityVarCount_2714_; lean_object* v_numEq0_x3f_2715_; uint8_t v_numEq0Updated_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2748_; 
v_toRing_2698_ = lean_ctor_get(v_s_2697_, 0);
v_invFn_x3f_2699_ = lean_ctor_get(v_s_2697_, 1);
v_semiringId_x3f_2700_ = lean_ctor_get(v_s_2697_, 2);
v_commSemiringInst_2701_ = lean_ctor_get(v_s_2697_, 3);
v_commRingInst_2702_ = lean_ctor_get(v_s_2697_, 4);
v_noZeroDivInst_x3f_2703_ = lean_ctor_get(v_s_2697_, 5);
v_fieldInst_x3f_2704_ = lean_ctor_get(v_s_2697_, 6);
v_powIdentityInst_x3f_2705_ = lean_ctor_get(v_s_2697_, 7);
v_denoteEntries_2706_ = lean_ctor_get(v_s_2697_, 8);
v_nextId_2707_ = lean_ctor_get(v_s_2697_, 9);
v_steps_2708_ = lean_ctor_get(v_s_2697_, 10);
v_queue_2709_ = lean_ctor_get(v_s_2697_, 11);
v_basis_2710_ = lean_ctor_get(v_s_2697_, 12);
v_diseqs_2711_ = lean_ctor_get(v_s_2697_, 13);
v_recheck_2712_ = lean_ctor_get_uint8(v_s_2697_, sizeof(void*)*17);
v_invSet_2713_ = lean_ctor_get(v_s_2697_, 14);
v_powIdentityVarCount_2714_ = lean_ctor_get(v_s_2697_, 15);
v_numEq0_x3f_2715_ = lean_ctor_get(v_s_2697_, 16);
v_numEq0Updated_2716_ = lean_ctor_get_uint8(v_s_2697_, sizeof(void*)*17 + 1);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_s_2697_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2718_ = v_s_2697_;
v_isShared_2719_ = v_isSharedCheck_2748_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_numEq0_x3f_2715_);
lean_inc(v_powIdentityVarCount_2714_);
lean_inc(v_invSet_2713_);
lean_inc(v_diseqs_2711_);
lean_inc(v_basis_2710_);
lean_inc(v_queue_2709_);
lean_inc(v_steps_2708_);
lean_inc(v_nextId_2707_);
lean_inc(v_denoteEntries_2706_);
lean_inc(v_powIdentityInst_x3f_2705_);
lean_inc(v_fieldInst_x3f_2704_);
lean_inc(v_noZeroDivInst_x3f_2703_);
lean_inc(v_commRingInst_2702_);
lean_inc(v_commSemiringInst_2701_);
lean_inc(v_semiringId_x3f_2700_);
lean_inc(v_invFn_x3f_2699_);
lean_inc(v_toRing_2698_);
lean_dec(v_s_2697_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2748_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v_id_2720_; lean_object* v_type_2721_; lean_object* v_u_2722_; lean_object* v_ringInst_2723_; lean_object* v_semiringInst_2724_; lean_object* v_charInst_x3f_2725_; lean_object* v_addFn_x3f_2726_; lean_object* v_mulFn_x3f_2727_; lean_object* v_subFn_x3f_2728_; lean_object* v_negFn_x3f_2729_; lean_object* v_intCastFn_x3f_2730_; lean_object* v_natCastFn_x3f_2731_; lean_object* v_one_x3f_2732_; lean_object* v_vars_2733_; lean_object* v_varMap_2734_; lean_object* v_denote_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2746_; 
v_id_2720_ = lean_ctor_get(v_toRing_2698_, 0);
v_type_2721_ = lean_ctor_get(v_toRing_2698_, 1);
v_u_2722_ = lean_ctor_get(v_toRing_2698_, 2);
v_ringInst_2723_ = lean_ctor_get(v_toRing_2698_, 3);
v_semiringInst_2724_ = lean_ctor_get(v_toRing_2698_, 4);
v_charInst_x3f_2725_ = lean_ctor_get(v_toRing_2698_, 5);
v_addFn_x3f_2726_ = lean_ctor_get(v_toRing_2698_, 6);
v_mulFn_x3f_2727_ = lean_ctor_get(v_toRing_2698_, 7);
v_subFn_x3f_2728_ = lean_ctor_get(v_toRing_2698_, 8);
v_negFn_x3f_2729_ = lean_ctor_get(v_toRing_2698_, 9);
v_intCastFn_x3f_2730_ = lean_ctor_get(v_toRing_2698_, 11);
v_natCastFn_x3f_2731_ = lean_ctor_get(v_toRing_2698_, 12);
v_one_x3f_2732_ = lean_ctor_get(v_toRing_2698_, 13);
v_vars_2733_ = lean_ctor_get(v_toRing_2698_, 14);
v_varMap_2734_ = lean_ctor_get(v_toRing_2698_, 15);
v_denote_2735_ = lean_ctor_get(v_toRing_2698_, 16);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_toRing_2698_);
if (v_isSharedCheck_2746_ == 0)
{
lean_object* v_unused_2747_; 
v_unused_2747_ = lean_ctor_get(v_toRing_2698_, 10);
lean_dec(v_unused_2747_);
v___x_2737_ = v_toRing_2698_;
v_isShared_2738_ = v_isSharedCheck_2746_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_denote_2735_);
lean_inc(v_varMap_2734_);
lean_inc(v_vars_2733_);
lean_inc(v_one_x3f_2732_);
lean_inc(v_natCastFn_x3f_2731_);
lean_inc(v_intCastFn_x3f_2730_);
lean_inc(v_negFn_x3f_2729_);
lean_inc(v_subFn_x3f_2728_);
lean_inc(v_mulFn_x3f_2727_);
lean_inc(v_addFn_x3f_2726_);
lean_inc(v_charInst_x3f_2725_);
lean_inc(v_semiringInst_2724_);
lean_inc(v_ringInst_2723_);
lean_inc(v_u_2722_);
lean_inc(v_type_2721_);
lean_inc(v_id_2720_);
lean_dec(v_toRing_2698_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2746_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2739_, 0, v_a_2696_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 10, v___x_2739_);
v___x_2741_ = v___x_2737_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_id_2720_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_type_2721_);
lean_ctor_set(v_reuseFailAlloc_2745_, 2, v_u_2722_);
lean_ctor_set(v_reuseFailAlloc_2745_, 3, v_ringInst_2723_);
lean_ctor_set(v_reuseFailAlloc_2745_, 4, v_semiringInst_2724_);
lean_ctor_set(v_reuseFailAlloc_2745_, 5, v_charInst_x3f_2725_);
lean_ctor_set(v_reuseFailAlloc_2745_, 6, v_addFn_x3f_2726_);
lean_ctor_set(v_reuseFailAlloc_2745_, 7, v_mulFn_x3f_2727_);
lean_ctor_set(v_reuseFailAlloc_2745_, 8, v_subFn_x3f_2728_);
lean_ctor_set(v_reuseFailAlloc_2745_, 9, v_negFn_x3f_2729_);
lean_ctor_set(v_reuseFailAlloc_2745_, 10, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2745_, 11, v_intCastFn_x3f_2730_);
lean_ctor_set(v_reuseFailAlloc_2745_, 12, v_natCastFn_x3f_2731_);
lean_ctor_set(v_reuseFailAlloc_2745_, 13, v_one_x3f_2732_);
lean_ctor_set(v_reuseFailAlloc_2745_, 14, v_vars_2733_);
lean_ctor_set(v_reuseFailAlloc_2745_, 15, v_varMap_2734_);
lean_ctor_set(v_reuseFailAlloc_2745_, 16, v_denote_2735_);
v___x_2741_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
lean_object* v___x_2743_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2741_);
v___x_2743_ = v___x_2718_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_invFn_x3f_2699_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_semiringId_x3f_2700_);
lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_commSemiringInst_2701_);
lean_ctor_set(v_reuseFailAlloc_2744_, 4, v_commRingInst_2702_);
lean_ctor_set(v_reuseFailAlloc_2744_, 5, v_noZeroDivInst_x3f_2703_);
lean_ctor_set(v_reuseFailAlloc_2744_, 6, v_fieldInst_x3f_2704_);
lean_ctor_set(v_reuseFailAlloc_2744_, 7, v_powIdentityInst_x3f_2705_);
lean_ctor_set(v_reuseFailAlloc_2744_, 8, v_denoteEntries_2706_);
lean_ctor_set(v_reuseFailAlloc_2744_, 9, v_nextId_2707_);
lean_ctor_set(v_reuseFailAlloc_2744_, 10, v_steps_2708_);
lean_ctor_set(v_reuseFailAlloc_2744_, 11, v_queue_2709_);
lean_ctor_set(v_reuseFailAlloc_2744_, 12, v_basis_2710_);
lean_ctor_set(v_reuseFailAlloc_2744_, 13, v_diseqs_2711_);
lean_ctor_set(v_reuseFailAlloc_2744_, 14, v_invSet_2713_);
lean_ctor_set(v_reuseFailAlloc_2744_, 15, v_powIdentityVarCount_2714_);
lean_ctor_set(v_reuseFailAlloc_2744_, 16, v_numEq0_x3f_2715_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*17, v_recheck_2712_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*17 + 1, v_numEq0Updated_2716_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = l_Lean_Level_ofNat(v___x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(lean_object* v_u_2764_, lean_object* v_type_2765_, lean_object* v_semiringInst_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2779_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1));
v___x_2780_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2);
v___x_2781_ = lean_box(0);
lean_inc(v_u_2764_);
v___x_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2782_, 0, v_u_2764_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
lean_inc_ref(v___x_2782_);
v___x_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2780_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2784_, 0, v_u_2764_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
lean_inc_ref(v___x_2784_);
v___x_2785_ = l_Lean_mkConst(v___x_2779_, v___x_2784_);
v___x_2786_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2765_, 2);
v___x_2787_ = l_Lean_mkApp3(v___x_2785_, v_type_2765_, v___x_2786_, v_type_2765_);
v___x_2788_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2787_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v_inst_x27_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc_n(v_a_2789_, 2);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2790_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4));
v___x_2791_ = l_Lean_mkConst(v___x_2790_, v___x_2782_);
lean_inc_ref(v_type_2765_);
v_inst_x27_2792_ = l_Lean_mkAppB(v___x_2791_, v_type_2765_, v_semiringInst_2766_);
v___x_2793_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6));
v___x_2794_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_2793_, v_a_2789_, v_inst_x27_2792_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
lean_dec_ref_known(v___x_2794_, 1);
v___x_2795_ = l_Lean_mkConst(v___x_2793_, v___x_2784_);
lean_inc_ref(v_type_2765_);
v___x_2796_ = l_Lean_mkApp4(v___x_2795_, v_type_2765_, v___x_2786_, v_type_2765_, v_a_2789_);
v___x_2797_ = l_Lean_Meta_Sym_canon(v___x_2796_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = l_Lean_Meta_Sym_shareCommon(v_a_2798_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
return v___x_2799_;
}
else
{
return v___x_2797_;
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_a_2789_);
lean_dec_ref_known(v___x_2784_, 2);
lean_dec_ref(v_type_2765_);
v_a_2800_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2794_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2794_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2784_, 2);
lean_dec_ref_known(v___x_2782_, 2);
lean_dec_ref(v_semiringInst_2766_);
lean_dec_ref(v_type_2765_);
return v___x_2788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___boxed(lean_object* v_u_2808_, lean_object* v_type_2809_, lean_object* v_semiringInst_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2808_, v_type_2809_, v_semiringInst_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec(v___y_2811_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2870_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2839_ = v___x_2836_;
v_isShared_2840_ = v_isSharedCheck_2870_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2870_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v_toRing_2841_; lean_object* v_powFn_x3f_2842_; 
v_toRing_2841_ = lean_ctor_get(v_a_2837_, 0);
lean_inc_ref(v_toRing_2841_);
lean_dec(v_a_2837_);
v_powFn_x3f_2842_ = lean_ctor_get(v_toRing_2841_, 10);
if (lean_obj_tag(v_powFn_x3f_2842_) == 1)
{
lean_object* v_val_2843_; lean_object* v___x_2845_; 
lean_inc_ref(v_powFn_x3f_2842_);
lean_dec_ref(v_toRing_2841_);
v_val_2843_ = lean_ctor_get(v_powFn_x3f_2842_, 0);
lean_inc(v_val_2843_);
lean_dec_ref_known(v_powFn_x3f_2842_, 1);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v_val_2843_);
v___x_2845_ = v___x_2839_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_val_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
else
{
lean_object* v_type_2847_; lean_object* v_u_2848_; lean_object* v_semiringInst_2849_; lean_object* v___x_2850_; 
lean_del_object(v___x_2839_);
v_type_2847_ = lean_ctor_get(v_toRing_2841_, 1);
lean_inc_ref(v_type_2847_);
v_u_2848_ = lean_ctor_get(v_toRing_2841_, 2);
lean_inc(v_u_2848_);
v_semiringInst_2849_ = lean_ctor_get(v_toRing_2841_, 4);
lean_inc_ref(v_semiringInst_2849_);
lean_dec_ref(v_toRing_2841_);
v___x_2850_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2848_, v_type_2847_, v_semiringInst_2849_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___f_2852_; lean_object* v___x_2853_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc_n(v_a_2851_, 2);
lean_dec_ref_known(v___x_2850_, 1);
v___f_2852_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_2852_, 0, v_a_2851_);
v___x_2853_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2852_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2860_ == 0)
{
lean_object* v_unused_2861_; 
v_unused_2861_ = lean_ctor_get(v___x_2853_, 0);
lean_dec(v_unused_2861_);
v___x_2855_ = v___x_2853_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_dec(v___x_2853_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v_a_2851_);
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2851_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec(v_a_2851_);
v_a_2862_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2853_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2853_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
else
{
return v___x_2850_;
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
v_a_2871_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2836_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2836_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec(v___y_2879_);
return v_res_2891_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2));
v___x_2896_ = lean_unsigned_to_nat(39u);
v___x_2897_ = lean_unsigned_to_nat(159u);
v___x_2898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1));
v___x_2899_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0));
v___x_2900_ = l_mkPanicMessageWithDecl(v___x_2899_, v___x_2898_, v___x_2897_, v___x_2896_, v___x_2895_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
switch(lean_obj_tag(v_a_2901_))
{
case 0:
{
lean_object* v_k_2914_; lean_object* v___x_2915_; 
v_k_2914_ = lean_ctor_get(v_a_2901_, 0);
lean_inc(v_k_2914_);
lean_dec_ref_known(v_a_2901_, 1);
v___x_2915_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2914_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
lean_dec(v_k_2914_);
return v___x_2915_;
}
case 1:
{
lean_object* v_k_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_k_2916_ = lean_ctor_get(v_a_2901_, 0);
lean_inc(v_k_2916_);
lean_dec_ref_known(v_a_2901_, 1);
v___x_2917_ = lean_nat_to_int(v_k_2916_);
v___x_2918_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_2917_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
lean_dec(v___x_2917_);
return v___x_2918_;
}
case 3:
{
lean_object* v_i_2919_; lean_object* v___x_2920_; 
v_i_2919_ = lean_ctor_get(v_a_2901_, 0);
lean_inc(v_i_2919_);
lean_dec_ref_known(v_a_2901_, 1);
v___x_2920_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
v___x_2922_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2940_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2925_ = v___x_2922_;
v_isShared_2926_ = v_isSharedCheck_2940_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2922_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2940_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___y_2928_; lean_object* v_toSemiring_2933_; lean_object* v_vars_2934_; lean_object* v_size_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v_toSemiring_2933_ = lean_ctor_get(v_a_2923_, 0);
lean_inc_ref(v_toSemiring_2933_);
lean_dec(v_a_2923_);
v_vars_2934_ = lean_ctor_get(v_toSemiring_2933_, 9);
lean_inc_ref(v_vars_2934_);
lean_dec_ref(v_toSemiring_2933_);
v_size_2935_ = lean_ctor_get(v_vars_2934_, 2);
v___x_2936_ = l_Lean_instInhabitedExpr;
v___x_2937_ = lean_nat_dec_lt(v_i_2919_, v_size_2935_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; 
lean_dec_ref(v_vars_2934_);
lean_dec(v_i_2919_);
v___x_2938_ = l_outOfBounds___redArg(v___x_2936_);
v___y_2928_ = v___x_2938_;
goto v___jp_2927_;
}
else
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2936_, v_vars_2934_, v_i_2919_);
lean_dec(v_i_2919_);
lean_dec_ref(v_vars_2934_);
v___y_2928_ = v___x_2939_;
goto v___jp_2927_;
}
v___jp_2927_:
{
lean_object* v___x_2929_; lean_object* v___x_2931_; 
v___x_2929_ = l_Lean_Expr_app___override(v_a_2921_, v___y_2928_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2929_);
v___x_2931_ = v___x_2925_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2929_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v_a_2921_);
lean_dec(v_i_2919_);
v_a_2941_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2922_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2922_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
else
{
lean_dec(v_i_2919_);
return v___x_2920_;
}
}
case 5:
{
lean_object* v_a_2949_; lean_object* v_b_2950_; lean_object* v___x_2951_; 
v_a_2949_ = lean_ctor_get(v_a_2901_, 0);
lean_inc_ref(v_a_2949_);
v_b_2950_ = lean_ctor_get(v_a_2901_, 1);
lean_inc_ref(v_b_2950_);
lean_dec_ref_known(v_a_2901_, 2);
v___x_2951_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2949_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2950_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2964_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2964_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2964_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2960_ = l_Lean_mkAppB(v_a_2952_, v_a_2954_, v_a_2956_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2960_);
v___x_2962_ = v___x_2958_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
else
{
lean_dec(v_a_2954_);
lean_dec(v_a_2952_);
return v___x_2955_;
}
}
else
{
lean_dec(v_a_2952_);
lean_dec_ref(v_b_2950_);
return v___x_2953_;
}
}
else
{
lean_dec_ref(v_b_2950_);
lean_dec_ref(v_a_2949_);
return v___x_2951_;
}
}
case 7:
{
lean_object* v_a_2965_; lean_object* v_b_2966_; lean_object* v___x_2967_; 
v_a_2965_ = lean_ctor_get(v_a_2901_, 0);
lean_inc_ref(v_a_2965_);
v_b_2966_ = lean_ctor_get(v_a_2901_, 1);
lean_inc_ref(v_b_2966_);
lean_dec_ref_known(v_a_2901_, 2);
v___x_2967_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
v___x_2969_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2965_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2971_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2971_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2966_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2980_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = l_Lean_mkAppB(v_a_2968_, v_a_2970_, v_a_2972_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2976_);
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
else
{
lean_dec(v_a_2970_);
lean_dec(v_a_2968_);
return v___x_2971_;
}
}
else
{
lean_dec(v_a_2968_);
lean_dec_ref(v_b_2966_);
return v___x_2969_;
}
}
else
{
lean_dec_ref(v_b_2966_);
lean_dec_ref(v_a_2965_);
return v___x_2967_;
}
}
case 8:
{
lean_object* v_a_2981_; lean_object* v_k_2982_; lean_object* v___x_2983_; 
v_a_2981_ = lean_ctor_get(v_a_2901_, 0);
lean_inc_ref(v_a_2981_);
v_k_2982_ = lean_ctor_get(v_a_2901_, 1);
lean_inc(v_k_2982_);
lean_dec_ref_known(v_a_2901_, 2);
v___x_2983_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2985_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2985_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2981_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2995_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2988_ = v___x_2985_;
v_isShared_2989_ = v_isSharedCheck_2995_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2995_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2990_ = l_Lean_mkNatLit(v_k_2982_);
v___x_2991_ = l_Lean_mkAppB(v_a_2984_, v_a_2986_, v___x_2990_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v___x_2991_);
v___x_2993_ = v___x_2988_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
else
{
lean_dec(v_a_2984_);
lean_dec(v_k_2982_);
return v___x_2985_;
}
}
else
{
lean_dec(v_k_2982_);
lean_dec_ref(v_a_2981_);
return v___x_2983_;
}
}
default: 
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
lean_dec_ref(v_a_2901_);
v___x_2996_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
v___x_2997_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___x_2996_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
return v___x_2997_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
lean_dec(v_a_3005_);
lean_dec_ref(v_a_3004_);
lean_dec(v_a_3003_);
lean_dec_ref(v_a_3002_);
lean_dec(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec(v_a_2999_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(lean_object* v_type_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_3012_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(lean_object* v_type_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(v_type_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec(v___y_3027_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object* v_e_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_e_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3053_, 1);
v___x_3055_ = l_Lean_Meta_Sym_shareCommon(v_a_3054_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
return v___x_3055_;
}
else
{
return v___x_3053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object* v_e_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(v_e_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec(v_a_3057_);
return v_res_3069_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
