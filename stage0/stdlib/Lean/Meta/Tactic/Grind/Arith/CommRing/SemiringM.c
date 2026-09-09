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
lean_object* v___x_161_; lean_object* v_env_162_; lean_object* v___x_163_; lean_object* v_toCold_164_; lean_object* v_mctx_165_; lean_object* v_lctx_166_; lean_object* v_options_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_161_ = lean_st_ref_get(v___y_159_);
v_env_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc_ref(v_env_162_);
lean_dec(v___x_161_);
v___x_163_ = lean_st_ref_get(v___y_157_);
v_toCold_164_ = lean_ctor_get(v___y_158_, 0);
v_mctx_165_ = lean_ctor_get(v___x_163_, 0);
lean_inc_ref(v_mctx_165_);
lean_dec(v___x_163_);
v_lctx_166_ = lean_ctor_get(v___y_156_, 2);
v_options_167_ = lean_ctor_get(v_toCold_164_, 2);
lean_inc_ref(v_options_167_);
lean_inc_ref(v_lctx_166_);
v___x_168_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_168_, 0, v_env_162_);
lean_ctor_set(v___x_168_, 1, v_mctx_165_);
lean_ctor_set(v___x_168_, 2, v_lctx_166_);
lean_ctor_set(v___x_168_, 3, v_options_167_);
v___x_169_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_msgData_155_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0___boxed(lean_object* v_msgData_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msgData_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(lean_object* v_msg_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_ref_184_; lean_object* v___x_185_; lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_194_; 
v_ref_184_ = lean_ctor_get(v___y_181_, 2);
v___x_185_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msg_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_194_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
lean_inc(v_ref_184_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_ref_184_);
lean_ctor_set(v___x_190_, 1, v_a_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 1);
lean_ctor_set(v___x_188_, 0, v___x_190_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg___boxed(lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_201_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0));
v___x_204_ = l_Lean_stringToMessageData(v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_206_, v_a_214_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_231_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_231_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_231_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_231_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_semirings_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_semirings_222_ = lean_ctor_get(v_a_218_, 3);
lean_inc_ref(v_semirings_222_);
lean_dec(v_a_218_);
v___x_223_ = lean_array_get_size(v_semirings_222_);
v___x_224_ = lean_nat_dec_lt(v_a_205_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v_semirings_222_);
lean_del_object(v___x_220_);
v___x_225_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1);
v___x_226_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_225_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_array_fget(v_semirings_222_, v_a_205_);
lean_dec_ref(v_semirings_222_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_227_);
v___x_229_ = v___x_220_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
v_a_232_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_217_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_217_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed(lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec(v_a_241_);
lean_dec(v_a_240_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(lean_object* v_00_u03b1_253_, lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_254_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___boxed(lean_object* v_00_u03b1_268_, lean_object* v_msg_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(v_00_u03b1_268_, v_msg_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec(v___y_271_);
lean_dec(v___y_270_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(lean_object* v_a_283_, lean_object* v_f_284_, lean_object* v_s_285_){
_start:
{
lean_object* v_rings_286_; lean_object* v_typeIdOf_287_; lean_object* v_exprToRingId_288_; lean_object* v_semirings_289_; lean_object* v_stypeIdOf_290_; lean_object* v_exprToSemiringId_291_; lean_object* v_ncRings_292_; lean_object* v_exprToNCRingId_293_; lean_object* v_nctypeIdOf_294_; lean_object* v_ncSemirings_295_; lean_object* v_exprToNCSemiringId_296_; lean_object* v_ncstypeIdOf_297_; lean_object* v_steps_298_; uint8_t v_reportedMaxDegreeIssue_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_rings_286_ = lean_ctor_get(v_s_285_, 0);
v_typeIdOf_287_ = lean_ctor_get(v_s_285_, 1);
v_exprToRingId_288_ = lean_ctor_get(v_s_285_, 2);
v_semirings_289_ = lean_ctor_get(v_s_285_, 3);
v_stypeIdOf_290_ = lean_ctor_get(v_s_285_, 4);
v_exprToSemiringId_291_ = lean_ctor_get(v_s_285_, 5);
v_ncRings_292_ = lean_ctor_get(v_s_285_, 6);
v_exprToNCRingId_293_ = lean_ctor_get(v_s_285_, 7);
v_nctypeIdOf_294_ = lean_ctor_get(v_s_285_, 8);
v_ncSemirings_295_ = lean_ctor_get(v_s_285_, 9);
v_exprToNCSemiringId_296_ = lean_ctor_get(v_s_285_, 10);
v_ncstypeIdOf_297_ = lean_ctor_get(v_s_285_, 11);
v_steps_298_ = lean_ctor_get(v_s_285_, 12);
v_reportedMaxDegreeIssue_299_ = lean_ctor_get_uint8(v_s_285_, sizeof(void*)*13);
v___x_300_ = lean_array_get_size(v_semirings_289_);
v___x_301_ = lean_nat_dec_lt(v_a_283_, v___x_300_);
if (v___x_301_ == 0)
{
lean_dec_ref(v_f_284_);
return v_s_285_;
}
else
{
lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_313_; 
lean_inc(v_steps_298_);
lean_inc_ref(v_ncstypeIdOf_297_);
lean_inc_ref(v_exprToNCSemiringId_296_);
lean_inc_ref(v_ncSemirings_295_);
lean_inc_ref(v_nctypeIdOf_294_);
lean_inc_ref(v_exprToNCRingId_293_);
lean_inc_ref(v_ncRings_292_);
lean_inc_ref(v_exprToSemiringId_291_);
lean_inc_ref(v_stypeIdOf_290_);
lean_inc_ref(v_semirings_289_);
lean_inc_ref(v_exprToRingId_288_);
lean_inc_ref(v_typeIdOf_287_);
lean_inc_ref(v_rings_286_);
v_isSharedCheck_313_ = !lean_is_exclusive(v_s_285_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; lean_object* v_unused_319_; lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; lean_object* v_unused_324_; lean_object* v_unused_325_; lean_object* v_unused_326_; 
v_unused_314_ = lean_ctor_get(v_s_285_, 12);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_s_285_, 11);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_s_285_, 10);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_s_285_, 9);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_s_285_, 8);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_s_285_, 7);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_s_285_, 6);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_s_285_, 5);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_s_285_, 4);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_s_285_, 3);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_s_285_, 2);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_s_285_, 1);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_s_285_, 0);
lean_dec(v_unused_326_);
v___x_303_ = v_s_285_;
v_isShared_304_ = v_isSharedCheck_313_;
goto v_resetjp_302_;
}
else
{
lean_dec(v_s_285_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_313_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_v_305_; lean_object* v___x_306_; lean_object* v_xs_x27_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v_v_305_ = lean_array_fget(v_semirings_289_, v_a_283_);
v___x_306_ = lean_box(0);
v_xs_x27_307_ = lean_array_fset(v_semirings_289_, v_a_283_, v___x_306_);
v___x_308_ = lean_apply_1(v_f_284_, v_v_305_);
v___x_309_ = lean_array_fset(v_xs_x27_307_, v_a_283_, v___x_308_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 3, v___x_309_);
v___x_311_ = v___x_303_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_rings_286_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_typeIdOf_287_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_exprToRingId_288_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v_stypeIdOf_290_);
lean_ctor_set(v_reuseFailAlloc_312_, 5, v_exprToSemiringId_291_);
lean_ctor_set(v_reuseFailAlloc_312_, 6, v_ncRings_292_);
lean_ctor_set(v_reuseFailAlloc_312_, 7, v_exprToNCRingId_293_);
lean_ctor_set(v_reuseFailAlloc_312_, 8, v_nctypeIdOf_294_);
lean_ctor_set(v_reuseFailAlloc_312_, 9, v_ncSemirings_295_);
lean_ctor_set(v_reuseFailAlloc_312_, 10, v_exprToNCSemiringId_296_);
lean_ctor_set(v_reuseFailAlloc_312_, 11, v_ncstypeIdOf_297_);
lean_ctor_set(v_reuseFailAlloc_312_, 12, v_steps_298_);
lean_ctor_set_uint8(v_reuseFailAlloc_312_, sizeof(void*)*13, v_reportedMaxDegreeIssue_299_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed(lean_object* v_a_327_, lean_object* v_f_328_, lean_object* v_s_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(v_a_327_, v_f_328_, v_s_329_);
lean_dec(v_a_327_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(lean_object* v_f_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___f_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_inc(v_a_332_);
v___f_335_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_335_, 0, v_a_332_);
lean_closure_set(v___f_335_, 1, v_f_331_);
v___x_336_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_337_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_336_, v___f_335_, v_a_333_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___boxed(lean_object* v_f_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(v_f_338_, v_a_339_, v_a_340_);
lean_dec(v_a_340_);
lean_dec(v_a_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(lean_object* v_f_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___f_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
lean_inc(v_a_344_);
v___f_356_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_356_, 0, v_a_344_);
lean_closure_set(v___f_356_, 1, v_f_343_);
v___x_357_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_358_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_357_, v___f_356_, v_a_345_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed(lean_object* v_f_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(v_f_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec(v_a_361_);
lean_dec(v_a_360_);
return v_res_372_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0));
v___x_375_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed), 12, 0);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM(void){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_382_, v_a_390_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_395_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_393_, 1);
v___x_395_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_410_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_410_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_410_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_410_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_ringId_400_; lean_object* v_rings_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v_ringId_400_ = lean_ctor_get(v_a_396_, 1);
lean_inc(v_ringId_400_);
lean_dec(v_a_396_);
v_rings_401_ = lean_ctor_get(v_a_394_, 0);
lean_inc_ref(v_rings_401_);
lean_dec(v_a_394_);
v___x_402_ = lean_array_get_size(v_rings_401_);
v___x_403_ = lean_nat_dec_lt(v_ringId_400_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec_ref(v_rings_401_);
lean_dec(v_ringId_400_);
lean_del_object(v___x_398_);
v___x_404_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1);
v___x_405_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_404_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
return v___x_405_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_array_fget(v_rings_401_, v_ringId_400_);
lean_dec(v_ringId_400_);
lean_dec_ref(v_rings_401_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_406_);
v___x_408_ = v___x_398_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_a_394_);
v_a_411_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_395_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_395_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
v_a_419_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_393_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_393_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed(lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec(v_a_428_);
lean_dec(v_a_427_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(lean_object* v_ringId_440_, lean_object* v_f_441_, lean_object* v_s_442_){
_start:
{
lean_object* v_rings_443_; lean_object* v_typeIdOf_444_; lean_object* v_exprToRingId_445_; lean_object* v_semirings_446_; lean_object* v_stypeIdOf_447_; lean_object* v_exprToSemiringId_448_; lean_object* v_ncRings_449_; lean_object* v_exprToNCRingId_450_; lean_object* v_nctypeIdOf_451_; lean_object* v_ncSemirings_452_; lean_object* v_exprToNCSemiringId_453_; lean_object* v_ncstypeIdOf_454_; lean_object* v_steps_455_; uint8_t v_reportedMaxDegreeIssue_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_rings_443_ = lean_ctor_get(v_s_442_, 0);
v_typeIdOf_444_ = lean_ctor_get(v_s_442_, 1);
v_exprToRingId_445_ = lean_ctor_get(v_s_442_, 2);
v_semirings_446_ = lean_ctor_get(v_s_442_, 3);
v_stypeIdOf_447_ = lean_ctor_get(v_s_442_, 4);
v_exprToSemiringId_448_ = lean_ctor_get(v_s_442_, 5);
v_ncRings_449_ = lean_ctor_get(v_s_442_, 6);
v_exprToNCRingId_450_ = lean_ctor_get(v_s_442_, 7);
v_nctypeIdOf_451_ = lean_ctor_get(v_s_442_, 8);
v_ncSemirings_452_ = lean_ctor_get(v_s_442_, 9);
v_exprToNCSemiringId_453_ = lean_ctor_get(v_s_442_, 10);
v_ncstypeIdOf_454_ = lean_ctor_get(v_s_442_, 11);
v_steps_455_ = lean_ctor_get(v_s_442_, 12);
v_reportedMaxDegreeIssue_456_ = lean_ctor_get_uint8(v_s_442_, sizeof(void*)*13);
v___x_457_ = lean_array_get_size(v_rings_443_);
v___x_458_ = lean_nat_dec_lt(v_ringId_440_, v___x_457_);
if (v___x_458_ == 0)
{
lean_dec_ref(v_f_441_);
return v_s_442_;
}
else
{
lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_470_; 
lean_inc(v_steps_455_);
lean_inc_ref(v_ncstypeIdOf_454_);
lean_inc_ref(v_exprToNCSemiringId_453_);
lean_inc_ref(v_ncSemirings_452_);
lean_inc_ref(v_nctypeIdOf_451_);
lean_inc_ref(v_exprToNCRingId_450_);
lean_inc_ref(v_ncRings_449_);
lean_inc_ref(v_exprToSemiringId_448_);
lean_inc_ref(v_stypeIdOf_447_);
lean_inc_ref(v_semirings_446_);
lean_inc_ref(v_exprToRingId_445_);
lean_inc_ref(v_typeIdOf_444_);
lean_inc_ref(v_rings_443_);
v_isSharedCheck_470_ = !lean_is_exclusive(v_s_442_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; lean_object* v_unused_479_; lean_object* v_unused_480_; lean_object* v_unused_481_; lean_object* v_unused_482_; lean_object* v_unused_483_; 
v_unused_471_ = lean_ctor_get(v_s_442_, 12);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_s_442_, 11);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_s_442_, 10);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_s_442_, 9);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_s_442_, 8);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_s_442_, 7);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_s_442_, 6);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_s_442_, 5);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_s_442_, 4);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_s_442_, 3);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_s_442_, 2);
lean_dec(v_unused_481_);
v_unused_482_ = lean_ctor_get(v_s_442_, 1);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v_s_442_, 0);
lean_dec(v_unused_483_);
v___x_460_ = v_s_442_;
v_isShared_461_ = v_isSharedCheck_470_;
goto v_resetjp_459_;
}
else
{
lean_dec(v_s_442_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_470_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v_v_462_; lean_object* v___x_463_; lean_object* v_xs_x27_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v_v_462_ = lean_array_fget(v_rings_443_, v_ringId_440_);
v___x_463_ = lean_box(0);
v_xs_x27_464_ = lean_array_fset(v_rings_443_, v_ringId_440_, v___x_463_);
v___x_465_ = lean_apply_1(v_f_441_, v_v_462_);
v___x_466_ = lean_array_fset(v_xs_x27_464_, v_ringId_440_, v___x_465_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_466_);
v___x_468_ = v___x_460_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_typeIdOf_444_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_exprToRingId_445_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_semirings_446_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v_stypeIdOf_447_);
lean_ctor_set(v_reuseFailAlloc_469_, 5, v_exprToSemiringId_448_);
lean_ctor_set(v_reuseFailAlloc_469_, 6, v_ncRings_449_);
lean_ctor_set(v_reuseFailAlloc_469_, 7, v_exprToNCRingId_450_);
lean_ctor_set(v_reuseFailAlloc_469_, 8, v_nctypeIdOf_451_);
lean_ctor_set(v_reuseFailAlloc_469_, 9, v_ncSemirings_452_);
lean_ctor_set(v_reuseFailAlloc_469_, 10, v_exprToNCSemiringId_453_);
lean_ctor_set(v_reuseFailAlloc_469_, 11, v_ncstypeIdOf_454_);
lean_ctor_set(v_reuseFailAlloc_469_, 12, v_steps_455_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, sizeof(void*)*13, v_reportedMaxDegreeIssue_456_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed(lean_object* v_ringId_484_, lean_object* v_f_485_, lean_object* v_s_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(v_ringId_484_, v_f_485_, v_s_486_);
lean_dec(v_ringId_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(lean_object* v_f_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v_ringId_503_; lean_object* v___f_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v_ringId_503_ = lean_ctor_get(v_a_502_, 1);
lean_inc(v_ringId_503_);
lean_dec(v_a_502_);
v___f_504_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed), 3, 2);
lean_closure_set(v___f_504_, 0, v_ringId_503_);
lean_closure_set(v___f_504_, 1, v_f_488_);
v___x_505_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_506_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_505_, v___f_504_, v_a_490_);
return v___x_506_;
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec_ref(v_f_488_);
v_a_507_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_501_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_501_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed(lean_object* v_f_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v_f_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec(v_a_517_);
lean_dec(v_a_516_);
return v_res_528_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0));
v___x_531_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed), 12, 0);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM(void){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_s_536_){
_start:
{
lean_object* v_rings_537_; lean_object* v_typeIdOf_538_; lean_object* v_exprToRingId_539_; lean_object* v_semirings_540_; lean_object* v_stypeIdOf_541_; lean_object* v_exprToSemiringId_542_; lean_object* v_ncRings_543_; lean_object* v_exprToNCRingId_544_; lean_object* v_nctypeIdOf_545_; lean_object* v_ncSemirings_546_; lean_object* v_exprToNCSemiringId_547_; lean_object* v_ncstypeIdOf_548_; lean_object* v_steps_549_; uint8_t v_reportedMaxDegreeIssue_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v_rings_537_ = lean_ctor_get(v_s_536_, 0);
v_typeIdOf_538_ = lean_ctor_get(v_s_536_, 1);
v_exprToRingId_539_ = lean_ctor_get(v_s_536_, 2);
v_semirings_540_ = lean_ctor_get(v_s_536_, 3);
v_stypeIdOf_541_ = lean_ctor_get(v_s_536_, 4);
v_exprToSemiringId_542_ = lean_ctor_get(v_s_536_, 5);
v_ncRings_543_ = lean_ctor_get(v_s_536_, 6);
v_exprToNCRingId_544_ = lean_ctor_get(v_s_536_, 7);
v_nctypeIdOf_545_ = lean_ctor_get(v_s_536_, 8);
v_ncSemirings_546_ = lean_ctor_get(v_s_536_, 9);
v_exprToNCSemiringId_547_ = lean_ctor_get(v_s_536_, 10);
v_ncstypeIdOf_548_ = lean_ctor_get(v_s_536_, 11);
v_steps_549_ = lean_ctor_get(v_s_536_, 12);
v_reportedMaxDegreeIssue_550_ = lean_ctor_get_uint8(v_s_536_, sizeof(void*)*13);
v___x_551_ = lean_array_get_size(v_semirings_540_);
v___x_552_ = lean_nat_dec_lt(v_a_534_, v___x_551_);
if (v___x_552_ == 0)
{
lean_dec_ref(v_a_535_);
return v_s_536_;
}
else
{
lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_576_; 
lean_inc(v_steps_549_);
lean_inc_ref(v_ncstypeIdOf_548_);
lean_inc_ref(v_exprToNCSemiringId_547_);
lean_inc_ref(v_ncSemirings_546_);
lean_inc_ref(v_nctypeIdOf_545_);
lean_inc_ref(v_exprToNCRingId_544_);
lean_inc_ref(v_ncRings_543_);
lean_inc_ref(v_exprToSemiringId_542_);
lean_inc_ref(v_stypeIdOf_541_);
lean_inc_ref(v_semirings_540_);
lean_inc_ref(v_exprToRingId_539_);
lean_inc_ref(v_typeIdOf_538_);
lean_inc_ref(v_rings_537_);
v_isSharedCheck_576_ = !lean_is_exclusive(v_s_536_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; lean_object* v_unused_578_; lean_object* v_unused_579_; lean_object* v_unused_580_; lean_object* v_unused_581_; lean_object* v_unused_582_; lean_object* v_unused_583_; lean_object* v_unused_584_; lean_object* v_unused_585_; lean_object* v_unused_586_; lean_object* v_unused_587_; lean_object* v_unused_588_; lean_object* v_unused_589_; 
v_unused_577_ = lean_ctor_get(v_s_536_, 12);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_s_536_, 11);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_s_536_, 10);
lean_dec(v_unused_579_);
v_unused_580_ = lean_ctor_get(v_s_536_, 9);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_s_536_, 8);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_s_536_, 7);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_s_536_, 6);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_s_536_, 5);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_s_536_, 4);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_s_536_, 3);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_s_536_, 2);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_s_536_, 1);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_s_536_, 0);
lean_dec(v_unused_589_);
v___x_554_ = v_s_536_;
v_isShared_555_ = v_isSharedCheck_576_;
goto v_resetjp_553_;
}
else
{
lean_dec(v_s_536_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_576_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_v_556_; lean_object* v_toSemiring_557_; lean_object* v_ringId_558_; lean_object* v_commSemiringInst_559_; lean_object* v_addRightCancelInst_x3f_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_574_; 
v_v_556_ = lean_array_fget(v_semirings_540_, v_a_534_);
v_toSemiring_557_ = lean_ctor_get(v_v_556_, 0);
v_ringId_558_ = lean_ctor_get(v_v_556_, 1);
v_commSemiringInst_559_ = lean_ctor_get(v_v_556_, 2);
v_addRightCancelInst_x3f_560_ = lean_ctor_get(v_v_556_, 3);
v_isSharedCheck_574_ = !lean_is_exclusive(v_v_556_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v_v_556_, 4);
lean_dec(v_unused_575_);
v___x_562_ = v_v_556_;
v_isShared_563_ = v_isSharedCheck_574_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_addRightCancelInst_x3f_560_);
lean_inc(v_commSemiringInst_559_);
lean_inc(v_ringId_558_);
lean_inc(v_toSemiring_557_);
lean_dec(v_v_556_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_574_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v_xs_x27_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_564_ = lean_box(0);
v_xs_x27_565_ = lean_array_fset(v_semirings_540_, v_a_534_, v___x_564_);
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v_a_535_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 4, v___x_566_);
v___x_568_ = v___x_562_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_toSemiring_557_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_ringId_558_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_commSemiringInst_559_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_addRightCancelInst_x3f_560_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v___x_566_);
v___x_568_ = v_reuseFailAlloc_573_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_array_fset(v_xs_x27_565_, v_a_534_, v___x_568_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 3, v___x_569_);
v___x_571_ = v___x_554_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_rings_537_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_typeIdOf_538_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_exprToRingId_539_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_stypeIdOf_541_);
lean_ctor_set(v_reuseFailAlloc_572_, 5, v_exprToSemiringId_542_);
lean_ctor_set(v_reuseFailAlloc_572_, 6, v_ncRings_543_);
lean_ctor_set(v_reuseFailAlloc_572_, 7, v_exprToNCRingId_544_);
lean_ctor_set(v_reuseFailAlloc_572_, 8, v_nctypeIdOf_545_);
lean_ctor_set(v_reuseFailAlloc_572_, 9, v_ncSemirings_546_);
lean_ctor_set(v_reuseFailAlloc_572_, 10, v_exprToNCSemiringId_547_);
lean_ctor_set(v_reuseFailAlloc_572_, 11, v_ncstypeIdOf_548_);
lean_ctor_set(v_reuseFailAlloc_572_, 12, v_steps_549_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*13, v_reportedMaxDegreeIssue_550_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed(lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_s_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(v_a_590_, v_a_591_, v_s_592_);
lean_dec(v_a_590_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn(lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___y_618_; lean_object* v___x_639_; 
v___x_639_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_661_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_661_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_661_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_661_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_toQFn_x3f_644_; 
v_toQFn_x3f_644_ = lean_ctor_get(v_a_640_, 4);
if (lean_obj_tag(v_toQFn_x3f_644_) == 1)
{
lean_object* v_val_645_; lean_object* v___x_647_; 
lean_inc_ref(v_toQFn_x3f_644_);
lean_dec(v_a_640_);
v_val_645_ = lean_ctor_get(v_toQFn_x3f_644_, 0);
lean_inc(v_val_645_);
lean_dec_ref_known(v_toQFn_x3f_644_, 1);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_val_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_val_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
lean_object* v_toSemiring_649_; lean_object* v_type_650_; lean_object* v_u_651_; lean_object* v_semiringInst_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
lean_del_object(v___x_642_);
v_toSemiring_649_ = lean_ctor_get(v_a_640_, 0);
lean_inc_ref(v_toSemiring_649_);
lean_dec(v_a_640_);
v_type_650_ = lean_ctor_get(v_toSemiring_649_, 1);
lean_inc_ref(v_type_650_);
v_u_651_ = lean_ctor_get(v_toSemiring_649_, 2);
lean_inc(v_u_651_);
v_semiringInst_652_ = lean_ctor_get(v_toSemiring_649_, 3);
lean_inc_ref(v_semiringInst_652_);
lean_dec_ref(v_toSemiring_649_);
v___x_653_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5));
v___x_654_ = lean_box(0);
v___x_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_655_, 0, v_u_651_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Lean_mkConst(v___x_653_, v___x_655_);
v___x_657_ = l_Lean_mkAppB(v___x_656_, v_type_650_, v_semiringInst_652_);
v___x_658_ = l_Lean_Meta_Sym_canon(v___x_657_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = l_Lean_Meta_Sym_shareCommon(v_a_659_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
v___y_618_ = v___x_660_;
goto v___jp_617_;
}
else
{
v___y_618_ = v___x_658_;
goto v___jp_617_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_639_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_639_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
v___jp_617_:
{
if (lean_obj_tag(v___y_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_a_619_ = lean_ctor_get(v___y_618_, 0);
lean_inc_n(v_a_619_, 2);
lean_dec_ref_known(v___y_618_, 1);
lean_inc(v_a_605_);
v___f_620_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed), 3, 2);
lean_closure_set(v___f_620_, 0, v_a_605_);
lean_closure_set(v___f_620_, 1, v_a_619_);
v___x_621_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_622_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_621_, v___f_620_, v_a_606_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v___x_622_, 0);
lean_dec(v_unused_630_);
v___x_624_ = v___x_622_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_dec(v___x_622_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v_a_619_);
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_619_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_a_619_);
v_a_631_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_622_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_622_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
return v___y_618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___boxed(lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec(v_a_671_);
lean_dec(v_a_670_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(lean_object* v_u_691_, lean_object* v_type_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_add_703_; lean_object* v___x_704_; 
v___x_699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1));
v___x_700_ = lean_box(0);
v___x_701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_701_, 0, v_u_691_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
lean_inc_ref(v___x_701_);
v___x_702_ = l_Lean_mkConst(v___x_699_, v___x_701_);
lean_inc_ref(v_type_692_);
v_add_703_ = l_Lean_Expr_app___override(v___x_702_, v_type_692_);
v___x_704_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_add_703_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_718_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_718_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_718_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_718_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
if (lean_obj_tag(v_a_705_) == 1)
{
lean_object* v_val_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_del_object(v___x_707_);
v_val_709_ = lean_ctor_get(v_a_705_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v_a_705_, 1);
v___x_710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3));
v___x_711_ = l_Lean_mkConst(v___x_710_, v___x_701_);
v___x_712_ = l_Lean_mkAppB(v___x_711_, v_type_692_, v_val_709_);
v___x_713_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_712_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_716_; 
lean_dec(v_a_705_);
lean_dec_ref_known(v___x_701_, 2);
lean_dec_ref(v_type_692_);
v___x_714_ = lean_box(0);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_714_);
v___x_716_ = v___x_707_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_701_, 2);
lean_dec_ref(v_type_692_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___boxed(lean_object* v_u_719_, lean_object* v_type_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_719_, v_type_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(lean_object* v_u_728_, lean_object* v_type_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_728_, v_type_729_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___boxed(lean_object* v_u_742_, lean_object* v_type_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(v_u_742_, v_type_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec(v_a_744_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_s_758_){
_start:
{
lean_object* v_rings_759_; lean_object* v_typeIdOf_760_; lean_object* v_exprToRingId_761_; lean_object* v_semirings_762_; lean_object* v_stypeIdOf_763_; lean_object* v_exprToSemiringId_764_; lean_object* v_ncRings_765_; lean_object* v_exprToNCRingId_766_; lean_object* v_nctypeIdOf_767_; lean_object* v_ncSemirings_768_; lean_object* v_exprToNCSemiringId_769_; lean_object* v_ncstypeIdOf_770_; lean_object* v_steps_771_; uint8_t v_reportedMaxDegreeIssue_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_rings_759_ = lean_ctor_get(v_s_758_, 0);
v_typeIdOf_760_ = lean_ctor_get(v_s_758_, 1);
v_exprToRingId_761_ = lean_ctor_get(v_s_758_, 2);
v_semirings_762_ = lean_ctor_get(v_s_758_, 3);
v_stypeIdOf_763_ = lean_ctor_get(v_s_758_, 4);
v_exprToSemiringId_764_ = lean_ctor_get(v_s_758_, 5);
v_ncRings_765_ = lean_ctor_get(v_s_758_, 6);
v_exprToNCRingId_766_ = lean_ctor_get(v_s_758_, 7);
v_nctypeIdOf_767_ = lean_ctor_get(v_s_758_, 8);
v_ncSemirings_768_ = lean_ctor_get(v_s_758_, 9);
v_exprToNCSemiringId_769_ = lean_ctor_get(v_s_758_, 10);
v_ncstypeIdOf_770_ = lean_ctor_get(v_s_758_, 11);
v_steps_771_ = lean_ctor_get(v_s_758_, 12);
v_reportedMaxDegreeIssue_772_ = lean_ctor_get_uint8(v_s_758_, sizeof(void*)*13);
v___x_773_ = lean_array_get_size(v_semirings_762_);
v___x_774_ = lean_nat_dec_lt(v_a_756_, v___x_773_);
if (v___x_774_ == 0)
{
lean_dec(v_a_757_);
return v_s_758_;
}
else
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_798_; 
lean_inc(v_steps_771_);
lean_inc_ref(v_ncstypeIdOf_770_);
lean_inc_ref(v_exprToNCSemiringId_769_);
lean_inc_ref(v_ncSemirings_768_);
lean_inc_ref(v_nctypeIdOf_767_);
lean_inc_ref(v_exprToNCRingId_766_);
lean_inc_ref(v_ncRings_765_);
lean_inc_ref(v_exprToSemiringId_764_);
lean_inc_ref(v_stypeIdOf_763_);
lean_inc_ref(v_semirings_762_);
lean_inc_ref(v_exprToRingId_761_);
lean_inc_ref(v_typeIdOf_760_);
lean_inc_ref(v_rings_759_);
v_isSharedCheck_798_ = !lean_is_exclusive(v_s_758_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; lean_object* v_unused_804_; lean_object* v_unused_805_; lean_object* v_unused_806_; lean_object* v_unused_807_; lean_object* v_unused_808_; lean_object* v_unused_809_; lean_object* v_unused_810_; lean_object* v_unused_811_; 
v_unused_799_ = lean_ctor_get(v_s_758_, 12);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_s_758_, 11);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_s_758_, 10);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_s_758_, 9);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_s_758_, 8);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_s_758_, 7);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_s_758_, 6);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_s_758_, 5);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_s_758_, 4);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_s_758_, 3);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_s_758_, 2);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_s_758_, 1);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_s_758_, 0);
lean_dec(v_unused_811_);
v___x_776_ = v_s_758_;
v_isShared_777_ = v_isSharedCheck_798_;
goto v_resetjp_775_;
}
else
{
lean_dec(v_s_758_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_798_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_v_778_; lean_object* v_toSemiring_779_; lean_object* v_ringId_780_; lean_object* v_commSemiringInst_781_; lean_object* v_toQFn_x3f_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_796_; 
v_v_778_ = lean_array_fget(v_semirings_762_, v_a_756_);
v_toSemiring_779_ = lean_ctor_get(v_v_778_, 0);
v_ringId_780_ = lean_ctor_get(v_v_778_, 1);
v_commSemiringInst_781_ = lean_ctor_get(v_v_778_, 2);
v_toQFn_x3f_782_ = lean_ctor_get(v_v_778_, 4);
v_isSharedCheck_796_ = !lean_is_exclusive(v_v_778_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_v_778_, 3);
lean_dec(v_unused_797_);
v___x_784_ = v_v_778_;
v_isShared_785_ = v_isSharedCheck_796_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_toQFn_x3f_782_);
lean_inc(v_commSemiringInst_781_);
lean_inc(v_ringId_780_);
lean_inc(v_toSemiring_779_);
lean_dec(v_v_778_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_796_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v_xs_x27_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_786_ = lean_box(0);
v_xs_x27_787_ = lean_array_fset(v_semirings_762_, v_a_756_, v___x_786_);
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_a_757_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 3, v___x_788_);
v___x_790_ = v___x_784_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_toSemiring_779_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_ringId_780_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_commSemiringInst_781_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_toQFn_x3f_782_);
v___x_790_ = v_reuseFailAlloc_795_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_array_fset(v_xs_x27_787_, v_a_756_, v___x_790_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 3, v___x_791_);
v___x_793_ = v___x_776_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_rings_759_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_typeIdOf_760_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_exprToRingId_761_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_stypeIdOf_763_);
lean_ctor_set(v_reuseFailAlloc_794_, 5, v_exprToSemiringId_764_);
lean_ctor_set(v_reuseFailAlloc_794_, 6, v_ncRings_765_);
lean_ctor_set(v_reuseFailAlloc_794_, 7, v_exprToNCRingId_766_);
lean_ctor_set(v_reuseFailAlloc_794_, 8, v_nctypeIdOf_767_);
lean_ctor_set(v_reuseFailAlloc_794_, 9, v_ncSemirings_768_);
lean_ctor_set(v_reuseFailAlloc_794_, 10, v_exprToNCSemiringId_769_);
lean_ctor_set(v_reuseFailAlloc_794_, 11, v_ncstypeIdOf_770_);
lean_ctor_set(v_reuseFailAlloc_794_, 12, v_steps_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_794_, sizeof(void*)*13, v_reportedMaxDegreeIssue_772_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed(lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_s_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(v_a_812_, v_a_813_, v_s_814_);
lean_dec(v_a_812_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_862_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_862_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_862_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_862_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_addRightCancelInst_x3f_833_; 
v_addRightCancelInst_x3f_833_ = lean_ctor_get(v_a_829_, 3);
if (lean_obj_tag(v_addRightCancelInst_x3f_833_) == 1)
{
lean_object* v_val_834_; lean_object* v___x_836_; 
lean_inc_ref(v_addRightCancelInst_x3f_833_);
lean_dec(v_a_829_);
v_val_834_ = lean_ctor_get(v_addRightCancelInst_x3f_833_, 0);
lean_inc(v_val_834_);
lean_dec_ref_known(v_addRightCancelInst_x3f_833_, 1);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v_val_834_);
v___x_836_ = v___x_831_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_val_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
lean_object* v_toSemiring_838_; lean_object* v_type_839_; lean_object* v_u_840_; lean_object* v___x_841_; 
lean_del_object(v___x_831_);
v_toSemiring_838_ = lean_ctor_get(v_a_829_, 0);
lean_inc_ref(v_toSemiring_838_);
lean_dec(v_a_829_);
v_type_839_ = lean_ctor_get(v_toSemiring_838_, 1);
lean_inc_ref(v_type_839_);
v_u_840_ = lean_ctor_get(v_toSemiring_838_, 2);
lean_inc(v_u_840_);
lean_dec_ref(v_toSemiring_838_);
v___x_841_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_840_, v_type_839_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___f_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc_n(v_a_842_, 2);
lean_dec_ref_known(v___x_841_, 1);
lean_inc(v_a_816_);
v___f_843_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_843_, 0, v_a_816_);
lean_closure_set(v___f_843_, 1, v_a_842_);
v___x_844_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_845_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_844_, v___f_843_, v_a_817_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v___x_845_, 0);
lean_dec(v_unused_853_);
v___x_847_ = v___x_845_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_dec(v___x_845_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v_a_842_);
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_842_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_a_842_);
v_a_854_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_845_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_845_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
return v___x_841_;
}
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_a_863_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_828_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_828_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___boxed(lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec(v_a_872_);
lean_dec(v_a_871_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_884_, lean_object* v_s_885_){
_start:
{
lean_object* v_id_886_; lean_object* v_type_887_; lean_object* v_u_888_; lean_object* v_semiringInst_889_; lean_object* v_mulFn_x3f_890_; lean_object* v_powFn_x3f_891_; lean_object* v_natCastFn_x3f_892_; lean_object* v_denote_893_; lean_object* v_vars_894_; lean_object* v_varMap_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_903_; 
v_id_886_ = lean_ctor_get(v_s_885_, 0);
v_type_887_ = lean_ctor_get(v_s_885_, 1);
v_u_888_ = lean_ctor_get(v_s_885_, 2);
v_semiringInst_889_ = lean_ctor_get(v_s_885_, 3);
v_mulFn_x3f_890_ = lean_ctor_get(v_s_885_, 5);
v_powFn_x3f_891_ = lean_ctor_get(v_s_885_, 6);
v_natCastFn_x3f_892_ = lean_ctor_get(v_s_885_, 7);
v_denote_893_ = lean_ctor_get(v_s_885_, 8);
v_vars_894_ = lean_ctor_get(v_s_885_, 9);
v_varMap_895_ = lean_ctor_get(v_s_885_, 10);
v_isSharedCheck_903_ = !lean_is_exclusive(v_s_885_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v_s_885_, 4);
lean_dec(v_unused_904_);
v___x_897_ = v_s_885_;
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_varMap_895_);
lean_inc(v_vars_894_);
lean_inc(v_denote_893_);
lean_inc(v_natCastFn_x3f_892_);
lean_inc(v_powFn_x3f_891_);
lean_inc(v_mulFn_x3f_890_);
lean_inc(v_semiringInst_889_);
lean_inc(v_u_888_);
lean_inc(v_type_887_);
lean_inc(v_id_886_);
lean_dec(v_s_885_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v_addFn_884_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 4, v___x_899_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_id_886_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_type_887_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_u_888_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_semiringInst_889_);
lean_ctor_set(v_reuseFailAlloc_902_, 4, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_902_, 5, v_mulFn_x3f_890_);
lean_ctor_set(v_reuseFailAlloc_902_, 6, v_powFn_x3f_891_);
lean_ctor_set(v_reuseFailAlloc_902_, 7, v_natCastFn_x3f_892_);
lean_ctor_set(v_reuseFailAlloc_902_, 8, v_denote_893_);
lean_ctor_set(v_reuseFailAlloc_902_, 9, v_vars_894_);
lean_ctor_set(v_reuseFailAlloc_902_, 10, v_varMap_895_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_905_, lean_object* v_addFn_906_, lean_object* v_____r_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_apply_2(v_toPure_905_, lean_box(0), v_addFn_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_909_, lean_object* v_modifySemiring_910_, lean_object* v_toBind_911_, lean_object* v_addFn_912_){
_start:
{
lean_object* v___f_913_; lean_object* v___f_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_inc_ref(v_addFn_912_);
v___f_913_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_913_, 0, v_addFn_912_);
v___f_914_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_914_, 0, v_toPure_909_);
lean_closure_set(v___f_914_, 1, v_addFn_912_);
v___x_915_ = lean_apply_1(v_modifySemiring_910_, v___f_913_);
v___x_916_ = lean_apply_4(v_toBind_911_, lean_box(0), lean_box(0), v___x_915_, v___f_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3(lean_object* v_toPure_934_, lean_object* v_inst_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_toBind_939_, lean_object* v___f_940_, lean_object* v_s_941_){
_start:
{
lean_object* v_addFn_x3f_942_; 
v_addFn_x3f_942_ = lean_ctor_get(v_s_941_, 4);
if (lean_obj_tag(v_addFn_x3f_942_) == 1)
{
lean_object* v_val_943_; lean_object* v___x_944_; 
lean_inc_ref(v_addFn_x3f_942_);
lean_dec_ref(v_s_941_);
lean_dec(v___f_940_);
lean_dec(v_toBind_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
lean_dec(v_inst_935_);
v_val_943_ = lean_ctor_get(v_addFn_x3f_942_, 0);
lean_inc(v_val_943_);
lean_dec_ref_known(v_addFn_x3f_942_, 1);
v___x_944_ = lean_apply_2(v_toPure_934_, lean_box(0), v_val_943_);
return v___x_944_;
}
else
{
lean_object* v_type_945_; lean_object* v_u_946_; lean_object* v_semiringInst_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v_expectedInst_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v_toPure_934_);
v_type_945_ = lean_ctor_get(v_s_941_, 1);
lean_inc_ref_n(v_type_945_, 3);
v_u_946_ = lean_ctor_get(v_s_941_, 2);
lean_inc_n(v_u_946_, 2);
v_semiringInst_947_ = lean_ctor_get(v_s_941_, 3);
lean_inc_ref(v_semiringInst_947_);
lean_dec_ref(v_s_941_);
v___x_948_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_949_ = lean_box(0);
v___x_950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_950_, 0, v_u_946_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
lean_inc_ref(v___x_950_);
v___x_951_ = l_Lean_mkConst(v___x_948_, v___x_950_);
v___x_952_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_953_ = l_Lean_mkConst(v___x_952_, v___x_950_);
v___x_954_ = l_Lean_mkAppB(v___x_953_, v_type_945_, v_semiringInst_947_);
v_expectedInst_955_ = l_Lean_mkAppB(v___x_951_, v_type_945_, v___x_954_);
v___x_956_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_957_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_958_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_935_, v_inst_936_, v_inst_937_, v_inst_938_, v_type_945_, v_u_946_, v___x_956_, v___x_957_, v_expectedInst_955_);
v___x_959_ = lean_apply_4(v_toBind_939_, lean_box(0), lean_box(0), v___x_958_, v___f_940_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_inst_963_, lean_object* v_inst_964_){
_start:
{
lean_object* v_toApplicative_965_; lean_object* v_toBind_966_; lean_object* v_getSemiring_967_; lean_object* v_modifySemiring_968_; lean_object* v_toPure_969_; lean_object* v___f_970_; lean_object* v___f_971_; lean_object* v___x_972_; 
v_toApplicative_965_ = lean_ctor_get(v_inst_962_, 0);
v_toBind_966_ = lean_ctor_get(v_inst_962_, 1);
lean_inc_n(v_toBind_966_, 3);
v_getSemiring_967_ = lean_ctor_get(v_inst_964_, 0);
lean_inc(v_getSemiring_967_);
v_modifySemiring_968_ = lean_ctor_get(v_inst_964_, 1);
lean_inc(v_modifySemiring_968_);
lean_dec_ref(v_inst_964_);
v_toPure_969_ = lean_ctor_get(v_toApplicative_965_, 1);
lean_inc_n(v_toPure_969_, 2);
v___f_970_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_970_, 0, v_toPure_969_);
lean_closure_set(v___f_970_, 1, v_modifySemiring_968_);
lean_closure_set(v___f_970_, 2, v_toBind_966_);
v___f_971_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_971_, 0, v_toPure_969_);
lean_closure_set(v___f_971_, 1, v_inst_960_);
lean_closure_set(v___f_971_, 2, v_inst_961_);
lean_closure_set(v___f_971_, 3, v_inst_962_);
lean_closure_set(v___f_971_, 4, v_inst_963_);
lean_closure_set(v___f_971_, 5, v_toBind_966_);
lean_closure_set(v___f_971_, 6, v___f_970_);
v___x_972_ = lean_apply_4(v_toBind_966_, lean_box(0), lean_box(0), v_getSemiring_967_, v___f_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27(lean_object* v_m_973_, lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_inst_977_, lean_object* v_inst_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(v_inst_974_, v_inst_975_, v_inst_976_, v_inst_977_, v_inst_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_980_, lean_object* v_s_981_){
_start:
{
lean_object* v_id_982_; lean_object* v_type_983_; lean_object* v_u_984_; lean_object* v_semiringInst_985_; lean_object* v_addFn_x3f_986_; lean_object* v_powFn_x3f_987_; lean_object* v_natCastFn_x3f_988_; lean_object* v_denote_989_; lean_object* v_vars_990_; lean_object* v_varMap_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_999_; 
v_id_982_ = lean_ctor_get(v_s_981_, 0);
v_type_983_ = lean_ctor_get(v_s_981_, 1);
v_u_984_ = lean_ctor_get(v_s_981_, 2);
v_semiringInst_985_ = lean_ctor_get(v_s_981_, 3);
v_addFn_x3f_986_ = lean_ctor_get(v_s_981_, 4);
v_powFn_x3f_987_ = lean_ctor_get(v_s_981_, 6);
v_natCastFn_x3f_988_ = lean_ctor_get(v_s_981_, 7);
v_denote_989_ = lean_ctor_get(v_s_981_, 8);
v_vars_990_ = lean_ctor_get(v_s_981_, 9);
v_varMap_991_ = lean_ctor_get(v_s_981_, 10);
v_isSharedCheck_999_ = !lean_is_exclusive(v_s_981_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v_s_981_, 5);
lean_dec(v_unused_1000_);
v___x_993_ = v_s_981_;
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_varMap_991_);
lean_inc(v_vars_990_);
lean_inc(v_denote_989_);
lean_inc(v_natCastFn_x3f_988_);
lean_inc(v_powFn_x3f_987_);
lean_inc(v_addFn_x3f_986_);
lean_inc(v_semiringInst_985_);
lean_inc(v_u_984_);
lean_inc(v_type_983_);
lean_inc(v_id_982_);
lean_dec(v_s_981_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_995_, 0, v_mulFn_980_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 5, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_id_982_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_type_983_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_u_984_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_semiringInst_985_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v_addFn_x3f_986_);
lean_ctor_set(v_reuseFailAlloc_998_, 5, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_998_, 6, v_powFn_x3f_987_);
lean_ctor_set(v_reuseFailAlloc_998_, 7, v_natCastFn_x3f_988_);
lean_ctor_set(v_reuseFailAlloc_998_, 8, v_denote_989_);
lean_ctor_set(v_reuseFailAlloc_998_, 9, v_vars_990_);
lean_ctor_set(v_reuseFailAlloc_998_, 10, v_varMap_991_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_1001_, lean_object* v_mulFn_1002_, lean_object* v_____r_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_apply_2(v_toPure_1001_, lean_box(0), v_mulFn_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_1005_, lean_object* v_modifySemiring_1006_, lean_object* v_toBind_1007_, lean_object* v_mulFn_1008_){
_start:
{
lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_inc_ref(v_mulFn_1008_);
v___f_1009_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1009_, 0, v_mulFn_1008_);
v___f_1010_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1010_, 0, v_toPure_1005_);
lean_closure_set(v___f_1010_, 1, v_mulFn_1008_);
v___x_1011_ = lean_apply_1(v_modifySemiring_1006_, v___f_1009_);
v___x_1012_ = lean_apply_4(v_toBind_1007_, lean_box(0), lean_box(0), v___x_1011_, v___f_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3(lean_object* v_toPure_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_inst_1033_, lean_object* v_toBind_1034_, lean_object* v___f_1035_, lean_object* v_s_1036_){
_start:
{
lean_object* v_mulFn_x3f_1037_; 
v_mulFn_x3f_1037_ = lean_ctor_get(v_s_1036_, 5);
if (lean_obj_tag(v_mulFn_x3f_1037_) == 1)
{
lean_object* v_val_1038_; lean_object* v___x_1039_; 
lean_inc_ref(v_mulFn_x3f_1037_);
lean_dec_ref(v_s_1036_);
lean_dec(v___f_1035_);
lean_dec(v_toBind_1034_);
lean_dec_ref(v_inst_1033_);
lean_dec_ref(v_inst_1032_);
lean_dec_ref(v_inst_1031_);
lean_dec(v_inst_1030_);
v_val_1038_ = lean_ctor_get(v_mulFn_x3f_1037_, 0);
lean_inc(v_val_1038_);
lean_dec_ref_known(v_mulFn_x3f_1037_, 1);
v___x_1039_ = lean_apply_2(v_toPure_1029_, lean_box(0), v_val_1038_);
return v___x_1039_;
}
else
{
lean_object* v_type_1040_; lean_object* v_u_1041_; lean_object* v_semiringInst_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_expectedInst_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v_toPure_1029_);
v_type_1040_ = lean_ctor_get(v_s_1036_, 1);
lean_inc_ref_n(v_type_1040_, 3);
v_u_1041_ = lean_ctor_get(v_s_1036_, 2);
lean_inc_n(v_u_1041_, 2);
v_semiringInst_1042_ = lean_ctor_get(v_s_1036_, 3);
lean_inc_ref(v_semiringInst_1042_);
lean_dec_ref(v_s_1036_);
v___x_1043_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_u_1041_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
lean_inc_ref(v___x_1045_);
v___x_1046_ = l_Lean_mkConst(v___x_1043_, v___x_1045_);
v___x_1047_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_1048_ = l_Lean_mkConst(v___x_1047_, v___x_1045_);
v___x_1049_ = l_Lean_mkAppB(v___x_1048_, v_type_1040_, v_semiringInst_1042_);
v_expectedInst_1050_ = l_Lean_mkAppB(v___x_1046_, v_type_1040_, v___x_1049_);
v___x_1051_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_1052_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_1053_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_1030_, v_inst_1031_, v_inst_1032_, v_inst_1033_, v_type_1040_, v_u_1041_, v___x_1051_, v___x_1052_, v_expectedInst_1050_);
v___x_1054_ = lean_apply_4(v_toBind_1034_, lean_box(0), lean_box(0), v___x_1053_, v___f_1035_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_){
_start:
{
lean_object* v_toApplicative_1060_; lean_object* v_toBind_1061_; lean_object* v_getSemiring_1062_; lean_object* v_modifySemiring_1063_; lean_object* v_toPure_1064_; lean_object* v___f_1065_; lean_object* v___f_1066_; lean_object* v___x_1067_; 
v_toApplicative_1060_ = lean_ctor_get(v_inst_1057_, 0);
v_toBind_1061_ = lean_ctor_get(v_inst_1057_, 1);
lean_inc_n(v_toBind_1061_, 3);
v_getSemiring_1062_ = lean_ctor_get(v_inst_1059_, 0);
lean_inc(v_getSemiring_1062_);
v_modifySemiring_1063_ = lean_ctor_get(v_inst_1059_, 1);
lean_inc(v_modifySemiring_1063_);
lean_dec_ref(v_inst_1059_);
v_toPure_1064_ = lean_ctor_get(v_toApplicative_1060_, 1);
lean_inc_n(v_toPure_1064_, 2);
v___f_1065_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1065_, 0, v_toPure_1064_);
lean_closure_set(v___f_1065_, 1, v_modifySemiring_1063_);
lean_closure_set(v___f_1065_, 2, v_toBind_1061_);
v___f_1066_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1066_, 0, v_toPure_1064_);
lean_closure_set(v___f_1066_, 1, v_inst_1055_);
lean_closure_set(v___f_1066_, 2, v_inst_1056_);
lean_closure_set(v___f_1066_, 3, v_inst_1057_);
lean_closure_set(v___f_1066_, 4, v_inst_1058_);
lean_closure_set(v___f_1066_, 5, v_toBind_1061_);
lean_closure_set(v___f_1066_, 6, v___f_1065_);
v___x_1067_ = lean_apply_4(v_toBind_1061_, lean_box(0), lean_box(0), v_getSemiring_1062_, v___f_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27(lean_object* v_m_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(v_inst_1069_, v_inst_1070_, v_inst_1071_, v_inst_1072_, v_inst_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1075_, lean_object* v_s_1076_){
_start:
{
lean_object* v_id_1077_; lean_object* v_type_1078_; lean_object* v_u_1079_; lean_object* v_semiringInst_1080_; lean_object* v_addFn_x3f_1081_; lean_object* v_mulFn_x3f_1082_; lean_object* v_natCastFn_x3f_1083_; lean_object* v_denote_1084_; lean_object* v_vars_1085_; lean_object* v_varMap_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1094_; 
v_id_1077_ = lean_ctor_get(v_s_1076_, 0);
v_type_1078_ = lean_ctor_get(v_s_1076_, 1);
v_u_1079_ = lean_ctor_get(v_s_1076_, 2);
v_semiringInst_1080_ = lean_ctor_get(v_s_1076_, 3);
v_addFn_x3f_1081_ = lean_ctor_get(v_s_1076_, 4);
v_mulFn_x3f_1082_ = lean_ctor_get(v_s_1076_, 5);
v_natCastFn_x3f_1083_ = lean_ctor_get(v_s_1076_, 7);
v_denote_1084_ = lean_ctor_get(v_s_1076_, 8);
v_vars_1085_ = lean_ctor_get(v_s_1076_, 9);
v_varMap_1086_ = lean_ctor_get(v_s_1076_, 10);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_s_1076_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v_s_1076_, 6);
lean_dec(v_unused_1095_);
v___x_1088_ = v_s_1076_;
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_varMap_1086_);
lean_inc(v_vars_1085_);
lean_inc(v_denote_1084_);
lean_inc(v_natCastFn_x3f_1083_);
lean_inc(v_mulFn_x3f_1082_);
lean_inc(v_addFn_x3f_1081_);
lean_inc(v_semiringInst_1080_);
lean_inc(v_u_1079_);
lean_inc(v_type_1078_);
lean_inc(v_id_1077_);
lean_dec(v_s_1076_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_powFn_1075_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 6, v___x_1090_);
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_id_1077_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_type_1078_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_u_1079_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v_semiringInst_1080_);
lean_ctor_set(v_reuseFailAlloc_1093_, 4, v_addFn_x3f_1081_);
lean_ctor_set(v_reuseFailAlloc_1093_, 5, v_mulFn_x3f_1082_);
lean_ctor_set(v_reuseFailAlloc_1093_, 6, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1093_, 7, v_natCastFn_x3f_1083_);
lean_ctor_set(v_reuseFailAlloc_1093_, 8, v_denote_1084_);
lean_ctor_set(v_reuseFailAlloc_1093_, 9, v_vars_1085_);
lean_ctor_set(v_reuseFailAlloc_1093_, 10, v_varMap_1086_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1096_, lean_object* v_powFn_1097_, lean_object* v_____r_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_apply_2(v_toPure_1096_, lean_box(0), v_powFn_1097_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1100_, lean_object* v_modifySemiring_1101_, lean_object* v_toBind_1102_, lean_object* v_powFn_1103_){
_start:
{
lean_object* v___f_1104_; lean_object* v___f_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_inc_ref(v_powFn_1103_);
v___f_1104_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1104_, 0, v_powFn_1103_);
v___f_1105_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1105_, 0, v_toPure_1100_);
lean_closure_set(v___f_1105_, 1, v_powFn_1103_);
v___x_1106_ = lean_apply_1(v_modifySemiring_1101_, v___f_1104_);
v___x_1107_ = lean_apply_4(v_toBind_1102_, lean_box(0), lean_box(0), v___x_1106_, v___f_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3(lean_object* v_toPure_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_inst_1111_, lean_object* v_inst_1112_, lean_object* v_toBind_1113_, lean_object* v___f_1114_, lean_object* v_s_1115_){
_start:
{
lean_object* v_powFn_x3f_1116_; 
v_powFn_x3f_1116_ = lean_ctor_get(v_s_1115_, 6);
if (lean_obj_tag(v_powFn_x3f_1116_) == 1)
{
lean_object* v_val_1117_; lean_object* v___x_1118_; 
lean_inc_ref(v_powFn_x3f_1116_);
lean_dec_ref(v_s_1115_);
lean_dec(v___f_1114_);
lean_dec(v_toBind_1113_);
lean_dec_ref(v_inst_1112_);
lean_dec_ref(v_inst_1111_);
lean_dec_ref(v_inst_1110_);
lean_dec(v_inst_1109_);
v_val_1117_ = lean_ctor_get(v_powFn_x3f_1116_, 0);
lean_inc(v_val_1117_);
lean_dec_ref_known(v_powFn_x3f_1116_, 1);
v___x_1118_ = lean_apply_2(v_toPure_1108_, lean_box(0), v_val_1117_);
return v___x_1118_;
}
else
{
lean_object* v_type_1119_; lean_object* v_u_1120_; lean_object* v_semiringInst_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec(v_toPure_1108_);
v_type_1119_ = lean_ctor_get(v_s_1115_, 1);
lean_inc_ref(v_type_1119_);
v_u_1120_ = lean_ctor_get(v_s_1115_, 2);
lean_inc(v_u_1120_);
v_semiringInst_1121_ = lean_ctor_get(v_s_1115_, 3);
lean_inc_ref(v_semiringInst_1121_);
lean_dec_ref(v_s_1115_);
v___x_1122_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(v_inst_1109_, v_inst_1110_, v_inst_1111_, v_inst_1112_, v_u_1120_, v_type_1119_, v_semiringInst_1121_);
v___x_1123_ = lean_apply_4(v_toBind_1113_, lean_box(0), lean_box(0), v___x_1122_, v___f_1114_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_){
_start:
{
lean_object* v_toApplicative_1129_; lean_object* v_toBind_1130_; lean_object* v_getSemiring_1131_; lean_object* v_modifySemiring_1132_; lean_object* v_toPure_1133_; lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; 
v_toApplicative_1129_ = lean_ctor_get(v_inst_1126_, 0);
v_toBind_1130_ = lean_ctor_get(v_inst_1126_, 1);
lean_inc_n(v_toBind_1130_, 3);
v_getSemiring_1131_ = lean_ctor_get(v_inst_1128_, 0);
lean_inc(v_getSemiring_1131_);
v_modifySemiring_1132_ = lean_ctor_get(v_inst_1128_, 1);
lean_inc(v_modifySemiring_1132_);
lean_dec_ref(v_inst_1128_);
v_toPure_1133_ = lean_ctor_get(v_toApplicative_1129_, 1);
lean_inc_n(v_toPure_1133_, 2);
v___f_1134_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1134_, 0, v_toPure_1133_);
lean_closure_set(v___f_1134_, 1, v_modifySemiring_1132_);
lean_closure_set(v___f_1134_, 2, v_toBind_1130_);
v___f_1135_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1135_, 0, v_toPure_1133_);
lean_closure_set(v___f_1135_, 1, v_inst_1124_);
lean_closure_set(v___f_1135_, 2, v_inst_1125_);
lean_closure_set(v___f_1135_, 3, v_inst_1126_);
lean_closure_set(v___f_1135_, 4, v_inst_1127_);
lean_closure_set(v___f_1135_, 5, v_toBind_1130_);
lean_closure_set(v___f_1135_, 6, v___f_1134_);
v___x_1136_ = lean_apply_4(v_toBind_1130_, lean_box(0), lean_box(0), v_getSemiring_1131_, v___f_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27(lean_object* v_m_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(v_inst_1138_, v_inst_1139_, v_inst_1140_, v_inst_1141_, v_inst_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1144_, lean_object* v_s_1145_){
_start:
{
lean_object* v_id_1146_; lean_object* v_type_1147_; lean_object* v_u_1148_; lean_object* v_semiringInst_1149_; lean_object* v_addFn_x3f_1150_; lean_object* v_mulFn_x3f_1151_; lean_object* v_powFn_x3f_1152_; lean_object* v_denote_1153_; lean_object* v_vars_1154_; lean_object* v_varMap_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1163_; 
v_id_1146_ = lean_ctor_get(v_s_1145_, 0);
v_type_1147_ = lean_ctor_get(v_s_1145_, 1);
v_u_1148_ = lean_ctor_get(v_s_1145_, 2);
v_semiringInst_1149_ = lean_ctor_get(v_s_1145_, 3);
v_addFn_x3f_1150_ = lean_ctor_get(v_s_1145_, 4);
v_mulFn_x3f_1151_ = lean_ctor_get(v_s_1145_, 5);
v_powFn_x3f_1152_ = lean_ctor_get(v_s_1145_, 6);
v_denote_1153_ = lean_ctor_get(v_s_1145_, 8);
v_vars_1154_ = lean_ctor_get(v_s_1145_, 9);
v_varMap_1155_ = lean_ctor_get(v_s_1145_, 10);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_s_1145_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v_s_1145_, 7);
lean_dec(v_unused_1164_);
v___x_1157_ = v_s_1145_;
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_varMap_1155_);
lean_inc(v_vars_1154_);
lean_inc(v_denote_1153_);
lean_inc(v_powFn_x3f_1152_);
lean_inc(v_mulFn_x3f_1151_);
lean_inc(v_addFn_x3f_1150_);
lean_inc(v_semiringInst_1149_);
lean_inc(v_u_1148_);
lean_inc(v_type_1147_);
lean_inc(v_id_1146_);
lean_dec(v_s_1145_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_natCastFn_1144_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 7, v___x_1159_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_id_1146_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_type_1147_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_u_1148_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_semiringInst_1149_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_addFn_x3f_1150_);
lean_ctor_set(v_reuseFailAlloc_1162_, 5, v_mulFn_x3f_1151_);
lean_ctor_set(v_reuseFailAlloc_1162_, 6, v_powFn_x3f_1152_);
lean_ctor_set(v_reuseFailAlloc_1162_, 7, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1162_, 8, v_denote_1153_);
lean_ctor_set(v_reuseFailAlloc_1162_, 9, v_vars_1154_);
lean_ctor_set(v_reuseFailAlloc_1162_, 10, v_varMap_1155_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1165_, lean_object* v_natCastFn_1166_, lean_object* v_____r_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_apply_2(v_toPure_1165_, lean_box(0), v_natCastFn_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1169_, lean_object* v_modifySemiring_1170_, lean_object* v_toBind_1171_, lean_object* v_natCastFn_1172_){
_start:
{
lean_object* v___f_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_inc_ref(v_natCastFn_1172_);
v___f_1173_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1173_, 0, v_natCastFn_1172_);
v___f_1174_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1174_, 0, v_toPure_1169_);
lean_closure_set(v___f_1174_, 1, v_natCastFn_1172_);
v___x_1175_ = lean_apply_1(v_modifySemiring_1170_, v___f_1173_);
v___x_1176_ = lean_apply_4(v_toBind_1171_, lean_box(0), lean_box(0), v___x_1175_, v___f_1174_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3(lean_object* v_toPure_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_toBind_1181_, lean_object* v___f_1182_, lean_object* v_s_1183_){
_start:
{
lean_object* v_natCastFn_x3f_1184_; 
v_natCastFn_x3f_1184_ = lean_ctor_get(v_s_1183_, 7);
if (lean_obj_tag(v_natCastFn_x3f_1184_) == 1)
{
lean_object* v_val_1185_; lean_object* v___x_1186_; 
lean_inc_ref(v_natCastFn_x3f_1184_);
lean_dec_ref(v_s_1183_);
lean_dec(v___f_1182_);
lean_dec(v_toBind_1181_);
lean_dec_ref(v_inst_1180_);
lean_dec_ref(v_inst_1179_);
lean_dec(v_inst_1178_);
v_val_1185_ = lean_ctor_get(v_natCastFn_x3f_1184_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v_natCastFn_x3f_1184_, 1);
v___x_1186_ = lean_apply_2(v_toPure_1177_, lean_box(0), v_val_1185_);
return v___x_1186_;
}
else
{
lean_object* v_type_1187_; lean_object* v_u_1188_; lean_object* v_semiringInst_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec(v_toPure_1177_);
v_type_1187_ = lean_ctor_get(v_s_1183_, 1);
lean_inc_ref(v_type_1187_);
v_u_1188_ = lean_ctor_get(v_s_1183_, 2);
lean_inc(v_u_1188_);
v_semiringInst_1189_ = lean_ctor_get(v_s_1183_, 3);
lean_inc_ref(v_semiringInst_1189_);
lean_dec_ref(v_s_1183_);
v___x_1190_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(v_inst_1178_, v_inst_1179_, v_inst_1180_, v_u_1188_, v_type_1187_, v_semiringInst_1189_);
v___x_1191_ = lean_apply_4(v_toBind_1181_, lean_box(0), lean_box(0), v___x_1190_, v___f_1182_);
return v___x_1191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_){
_start:
{
lean_object* v_toApplicative_1196_; lean_object* v_toBind_1197_; lean_object* v_getSemiring_1198_; lean_object* v_modifySemiring_1199_; lean_object* v_toPure_1200_; lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; 
v_toApplicative_1196_ = lean_ctor_get(v_inst_1193_, 0);
v_toBind_1197_ = lean_ctor_get(v_inst_1193_, 1);
lean_inc_n(v_toBind_1197_, 3);
v_getSemiring_1198_ = lean_ctor_get(v_inst_1195_, 0);
lean_inc(v_getSemiring_1198_);
v_modifySemiring_1199_ = lean_ctor_get(v_inst_1195_, 1);
lean_inc(v_modifySemiring_1199_);
lean_dec_ref(v_inst_1195_);
v_toPure_1200_ = lean_ctor_get(v_toApplicative_1196_, 1);
lean_inc_n(v_toPure_1200_, 2);
v___f_1201_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1201_, 0, v_toPure_1200_);
lean_closure_set(v___f_1201_, 1, v_modifySemiring_1199_);
lean_closure_set(v___f_1201_, 2, v_toBind_1197_);
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1202_, 0, v_toPure_1200_);
lean_closure_set(v___f_1202_, 1, v_inst_1192_);
lean_closure_set(v___f_1202_, 2, v_inst_1193_);
lean_closure_set(v___f_1202_, 3, v_inst_1194_);
lean_closure_set(v___f_1202_, 4, v_toBind_1197_);
lean_closure_set(v___f_1202_, 5, v___f_1201_);
v___x_1203_ = lean_apply_4(v_toBind_1197_, lean_box(0), lean_box(0), v_getSemiring_1198_, v___f_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27(lean_object* v_m_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_inst_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(v_inst_1205_, v_inst_1206_, v_inst_1207_, v_inst_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1210_, lean_object* v_vals_1211_, lean_object* v_i_1212_, lean_object* v_k_1213_){
_start:
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = lean_array_get_size(v_keys_1210_);
v___x_1215_ = lean_nat_dec_lt(v_i_1212_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
lean_dec(v_i_1212_);
v___x_1216_ = lean_box(0);
return v___x_1216_;
}
else
{
lean_object* v_k_x27_1217_; size_t v___x_1218_; size_t v___x_1219_; uint8_t v___x_1220_; 
v_k_x27_1217_ = lean_array_fget_borrowed(v_keys_1210_, v_i_1212_);
v___x_1218_ = lean_ptr_addr(v_k_1213_);
v___x_1219_ = lean_ptr_addr(v_k_x27_1217_);
v___x_1220_ = lean_usize_dec_eq(v___x_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = lean_nat_add(v_i_1212_, v___x_1221_);
lean_dec(v_i_1212_);
v_i_1212_ = v___x_1222_;
goto _start;
}
else
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = lean_array_fget_borrowed(v_vals_1211_, v_i_1212_);
lean_dec(v_i_1212_);
lean_inc(v___x_1224_);
v___x_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1226_, lean_object* v_vals_1227_, lean_object* v_i_1228_, lean_object* v_k_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1226_, v_vals_1227_, v_i_1228_, v_k_1229_);
lean_dec_ref(v_k_1229_);
lean_dec_ref(v_vals_1227_);
lean_dec_ref(v_keys_1226_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_1231_, size_t v_x_1232_, lean_object* v_x_1233_){
_start:
{
if (lean_obj_tag(v_x_1231_) == 0)
{
lean_object* v_es_1234_; lean_object* v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; lean_object* v_j_1238_; lean_object* v___x_1239_; 
v_es_1234_ = lean_ctor_get(v_x_1231_, 0);
v___x_1235_ = lean_box(2);
v___x_1236_ = ((size_t)31ULL);
v___x_1237_ = lean_usize_land(v_x_1232_, v___x_1236_);
v_j_1238_ = lean_usize_to_nat(v___x_1237_);
v___x_1239_ = lean_array_get_borrowed(v___x_1235_, v_es_1234_, v_j_1238_);
lean_dec(v_j_1238_);
switch(lean_obj_tag(v___x_1239_))
{
case 0:
{
lean_object* v_key_1240_; lean_object* v_val_1241_; size_t v___x_1242_; size_t v___x_1243_; uint8_t v___x_1244_; 
v_key_1240_ = lean_ctor_get(v___x_1239_, 0);
v_val_1241_ = lean_ctor_get(v___x_1239_, 1);
v___x_1242_ = lean_ptr_addr(v_x_1233_);
v___x_1243_ = lean_ptr_addr(v_key_1240_);
v___x_1244_ = lean_usize_dec_eq(v___x_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_box(0);
return v___x_1245_;
}
else
{
lean_object* v___x_1246_; 
lean_inc(v_val_1241_);
v___x_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1246_, 0, v_val_1241_);
return v___x_1246_;
}
}
case 1:
{
lean_object* v_node_1247_; size_t v___x_1248_; size_t v___x_1249_; 
v_node_1247_ = lean_ctor_get(v___x_1239_, 0);
v___x_1248_ = ((size_t)5ULL);
v___x_1249_ = lean_usize_shift_right(v_x_1232_, v___x_1248_);
v_x_1231_ = v_node_1247_;
v_x_1232_ = v___x_1249_;
goto _start;
}
default: 
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_box(0);
return v___x_1251_;
}
}
}
else
{
lean_object* v_ks_1252_; lean_object* v_vs_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_ks_1252_ = lean_ctor_get(v_x_1231_, 0);
v_vs_1253_ = lean_ctor_get(v_x_1231_, 1);
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1252_, v_vs_1253_, v___x_1254_, v_x_1233_);
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
size_t v_x_904__boxed_1259_; lean_object* v_res_1260_; 
v_x_904__boxed_1259_ = lean_unbox_usize(v_x_1257_);
lean_dec(v_x_1257_);
v_res_1260_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1256_, v_x_904__boxed_1259_, v_x_1258_);
lean_dec_ref(v_x_1258_);
lean_dec_ref(v_x_1256_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
size_t v___x_1263_; size_t v___x_1264_; size_t v___x_1265_; uint64_t v___x_1266_; size_t v___x_1267_; lean_object* v___x_1268_; 
v___x_1263_ = lean_ptr_addr(v_x_1262_);
v___x_1264_ = ((size_t)3ULL);
v___x_1265_ = lean_usize_shift_right(v___x_1263_, v___x_1264_);
v___x_1266_ = lean_usize_to_uint64(v___x_1265_);
v___x_1267_ = lean_uint64_to_usize(v___x_1266_);
v___x_1268_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1261_, v___x_1267_, v_x_1262_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_1269_, v_x_1270_);
lean_dec_ref(v_x_1270_);
lean_dec_ref(v_x_1269_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(lean_object* v_e_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1273_, v_a_1274_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1286_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1286_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1286_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_exprToSemiringId_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v_exprToSemiringId_1281_ = lean_ctor_get(v_a_1277_, 5);
lean_inc_ref(v_exprToSemiringId_1281_);
lean_dec(v_a_1277_);
v___x_1282_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_exprToSemiringId_1281_, v_e_1272_);
lean_dec_ref(v_exprToSemiringId_1281_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1282_);
v___x_1284_ = v___x_1279_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_a_1287_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1276_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1276_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(lean_object* v_e_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1295_, v_a_1296_, v_a_1297_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_e_1295_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(lean_object* v_e_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1300_, v_a_1301_, v_a_1309_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(lean_object* v_e_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(v_e_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_e_1313_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(lean_object* v_00_u03b2_1326_, lean_object* v_x_1327_, lean_object* v_x_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_1327_, v_x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(v_00_u03b2_1330_, v_x_1331_, v_x_1332_);
lean_dec_ref(v_x_1332_);
lean_dec_ref(v_x_1331_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1334_, lean_object* v_x_1335_, size_t v_x_1336_, lean_object* v_x_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1335_, v_x_1336_, v_x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_){
_start:
{
size_t v_x_1025__boxed_1343_; lean_object* v_res_1344_; 
v_x_1025__boxed_1343_ = lean_unbox_usize(v_x_1341_);
lean_dec(v_x_1341_);
v_res_1344_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(v_00_u03b2_1339_, v_x_1340_, v_x_1025__boxed_1343_, v_x_1342_);
lean_dec_ref(v_x_1342_);
lean_dec_ref(v_x_1340_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1345_, lean_object* v_keys_1346_, lean_object* v_vals_1347_, lean_object* v_heq_1348_, lean_object* v_i_1349_, lean_object* v_k_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1346_, v_vals_1347_, v_i_1349_, v_k_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1352_, lean_object* v_keys_1353_, lean_object* v_vals_1354_, lean_object* v_heq_1355_, lean_object* v_i_1356_, lean_object* v_k_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1352_, v_keys_1353_, v_vals_1354_, v_heq_1355_, v_i_1356_, v_k_1357_);
lean_dec_ref(v_k_1357_);
lean_dec_ref(v_vals_1354_);
lean_dec_ref(v_keys_1353_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_){
_start:
{
lean_object* v_ks_1363_; lean_object* v_vs_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1390_; 
v_ks_1363_ = lean_ctor_get(v_x_1359_, 0);
v_vs_1364_ = lean_ctor_get(v_x_1359_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_x_1359_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1366_ = v_x_1359_;
v_isShared_1367_ = v_isSharedCheck_1390_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_vs_1364_);
lean_inc(v_ks_1363_);
lean_dec(v_x_1359_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1390_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = lean_array_get_size(v_ks_1363_);
v___x_1369_ = lean_nat_dec_lt(v_x_1360_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
lean_dec(v_x_1360_);
v___x_1370_ = lean_array_push(v_ks_1363_, v_x_1361_);
v___x_1371_ = lean_array_push(v_vs_1364_, v_x_1362_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v___x_1371_);
lean_ctor_set(v___x_1366_, 0, v___x_1370_);
v___x_1373_ = v___x_1366_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
lean_object* v_k_x27_1375_; size_t v___x_1376_; size_t v___x_1377_; uint8_t v___x_1378_; 
v_k_x27_1375_ = lean_array_fget_borrowed(v_ks_1363_, v_x_1360_);
v___x_1376_ = lean_ptr_addr(v_x_1361_);
v___x_1377_ = lean_ptr_addr(v_k_x27_1375_);
v___x_1378_ = lean_usize_dec_eq(v___x_1376_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1380_; 
if (v_isShared_1367_ == 0)
{
v___x_1380_ = v___x_1366_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_ks_1363_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_vs_1364_);
v___x_1380_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_nat_add(v_x_1360_, v___x_1381_);
lean_dec(v_x_1360_);
v_x_1359_ = v___x_1380_;
v_x_1360_ = v___x_1382_;
goto _start;
}
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1385_ = lean_array_fset(v_ks_1363_, v_x_1360_, v_x_1361_);
v___x_1386_ = lean_array_fset(v_vs_1364_, v_x_1360_, v_x_1362_);
lean_dec(v_x_1360_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v___x_1386_);
lean_ctor_set(v___x_1366_, 0, v___x_1385_);
v___x_1388_ = v___x_1366_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1391_, lean_object* v_k_1392_, lean_object* v_v_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1391_, v___x_1394_, v_k_1392_, v_v_1393_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(lean_object* v_x_1397_, size_t v_x_1398_, size_t v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
if (lean_obj_tag(v_x_1397_) == 0)
{
lean_object* v_es_1402_; size_t v___x_1403_; size_t v___x_1404_; lean_object* v_j_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v_es_1402_ = lean_ctor_get(v_x_1397_, 0);
v___x_1403_ = ((size_t)31ULL);
v___x_1404_ = lean_usize_land(v_x_1398_, v___x_1403_);
v_j_1405_ = lean_usize_to_nat(v___x_1404_);
v___x_1406_ = lean_array_get_size(v_es_1402_);
v___x_1407_ = lean_nat_dec_lt(v_j_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_dec(v_j_1405_);
lean_dec(v_x_1401_);
lean_dec_ref(v_x_1400_);
return v_x_1397_;
}
else
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1448_; 
lean_inc_ref(v_es_1402_);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_x_1397_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v_x_1397_, 0);
lean_dec(v_unused_1449_);
v___x_1409_ = v_x_1397_;
v_isShared_1410_ = v_isSharedCheck_1448_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_x_1397_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1448_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_v_1411_; lean_object* v___x_1412_; lean_object* v_xs_x27_1413_; lean_object* v___y_1415_; 
v_v_1411_ = lean_array_fget(v_es_1402_, v_j_1405_);
v___x_1412_ = lean_box(0);
v_xs_x27_1413_ = lean_array_fset(v_es_1402_, v_j_1405_, v___x_1412_);
switch(lean_obj_tag(v_v_1411_))
{
case 0:
{
lean_object* v_key_1420_; lean_object* v_val_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1433_; 
v_key_1420_ = lean_ctor_get(v_v_1411_, 0);
v_val_1421_ = lean_ctor_get(v_v_1411_, 1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_v_1411_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1423_ = v_v_1411_;
v_isShared_1424_ = v_isSharedCheck_1433_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_val_1421_);
lean_inc(v_key_1420_);
lean_dec(v_v_1411_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1433_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
size_t v___x_1425_; size_t v___x_1426_; uint8_t v___x_1427_; 
v___x_1425_ = lean_ptr_addr(v_x_1400_);
v___x_1426_ = lean_ptr_addr(v_key_1420_);
v___x_1427_ = lean_usize_dec_eq(v___x_1425_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_del_object(v___x_1423_);
v___x_1428_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1420_, v_val_1421_, v_x_1400_, v_x_1401_);
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
v___y_1415_ = v___x_1429_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1431_; 
lean_dec(v_val_1421_);
lean_dec(v_key_1420_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_x_1401_);
lean_ctor_set(v___x_1423_, 0, v_x_1400_);
v___x_1431_ = v___x_1423_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_x_1400_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_x_1401_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
v___y_1415_ = v___x_1431_;
goto v___jp_1414_;
}
}
}
}
case 1:
{
lean_object* v_node_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1446_; 
v_node_1434_ = lean_ctor_get(v_v_1411_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_v_1411_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1436_ = v_v_1411_;
v_isShared_1437_ = v_isSharedCheck_1446_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_node_1434_);
lean_dec(v_v_1411_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1446_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
size_t v___x_1438_; size_t v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1438_ = ((size_t)5ULL);
v___x_1439_ = lean_usize_shift_right(v_x_1398_, v___x_1438_);
v___x_1440_ = ((size_t)1ULL);
v___x_1441_ = lean_usize_add(v_x_1399_, v___x_1440_);
v___x_1442_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_node_1434_, v___x_1439_, v___x_1441_, v_x_1400_, v_x_1401_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1442_);
v___x_1444_ = v___x_1436_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
v___y_1415_ = v___x_1444_;
goto v___jp_1414_;
}
}
}
default: 
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v_x_1400_);
lean_ctor_set(v___x_1447_, 1, v_x_1401_);
v___y_1415_ = v___x_1447_;
goto v___jp_1414_;
}
}
v___jp_1414_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_array_fset(v_xs_x27_1413_, v_j_1405_, v___y_1415_);
lean_dec(v_j_1405_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1416_);
v___x_1418_ = v___x_1409_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
else
{
lean_object* v_ks_1450_; lean_object* v_vs_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1469_; 
v_ks_1450_ = lean_ctor_get(v_x_1397_, 0);
v_vs_1451_ = lean_ctor_get(v_x_1397_, 1);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_x_1397_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1453_ = v_x_1397_;
v_isShared_1454_ = v_isSharedCheck_1469_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_vs_1451_);
lean_inc(v_ks_1450_);
lean_dec(v_x_1397_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1469_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_ks_1450_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_vs_1451_);
v___x_1456_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v_newNode_1457_; size_t v___x_1458_; uint8_t v___x_1459_; 
v_newNode_1457_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v___x_1456_, v_x_1400_, v_x_1401_);
v___x_1458_ = ((size_t)7ULL);
v___x_1459_ = lean_usize_dec_le(v___x_1458_, v_x_1399_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1460_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1457_);
v___x_1461_ = lean_unsigned_to_nat(4u);
v___x_1462_ = lean_nat_dec_lt(v___x_1460_, v___x_1461_);
lean_dec(v___x_1460_);
if (v___x_1462_ == 0)
{
lean_object* v_ks_1463_; lean_object* v_vs_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v_ks_1463_ = lean_ctor_get(v_newNode_1457_, 0);
lean_inc_ref(v_ks_1463_);
v_vs_1464_ = lean_ctor_get(v_newNode_1457_, 1);
lean_inc_ref(v_vs_1464_);
lean_dec_ref(v_newNode_1457_);
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_1467_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_x_1399_, v_ks_1463_, v_vs_1464_, v___x_1465_, v___x_1466_);
lean_dec_ref(v_vs_1464_);
lean_dec_ref(v_ks_1463_);
return v___x_1467_;
}
else
{
return v_newNode_1457_;
}
}
else
{
return v_newNode_1457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1470_, lean_object* v_keys_1471_, lean_object* v_vals_1472_, lean_object* v_i_1473_, lean_object* v_entries_1474_){
_start:
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = lean_array_get_size(v_keys_1471_);
v___x_1476_ = lean_nat_dec_lt(v_i_1473_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_dec(v_i_1473_);
return v_entries_1474_;
}
else
{
lean_object* v_k_1477_; lean_object* v_v_1478_; size_t v___x_1479_; size_t v___x_1480_; size_t v___x_1481_; uint64_t v___x_1482_; size_t v_h_1483_; size_t v___x_1484_; lean_object* v___x_1485_; size_t v___x_1486_; size_t v___x_1487_; size_t v___x_1488_; size_t v_h_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_k_1477_ = lean_array_fget_borrowed(v_keys_1471_, v_i_1473_);
v_v_1478_ = lean_array_fget_borrowed(v_vals_1472_, v_i_1473_);
v___x_1479_ = lean_ptr_addr(v_k_1477_);
v___x_1480_ = ((size_t)3ULL);
v___x_1481_ = lean_usize_shift_right(v___x_1479_, v___x_1480_);
v___x_1482_ = lean_usize_to_uint64(v___x_1481_);
v_h_1483_ = lean_uint64_to_usize(v___x_1482_);
v___x_1484_ = ((size_t)5ULL);
v___x_1485_ = lean_unsigned_to_nat(1u);
v___x_1486_ = ((size_t)1ULL);
v___x_1487_ = lean_usize_sub(v_depth_1470_, v___x_1486_);
v___x_1488_ = lean_usize_mul(v___x_1484_, v___x_1487_);
v_h_1489_ = lean_usize_shift_right(v_h_1483_, v___x_1488_);
v___x_1490_ = lean_nat_add(v_i_1473_, v___x_1485_);
lean_dec(v_i_1473_);
lean_inc(v_v_1478_);
lean_inc(v_k_1477_);
v___x_1491_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_entries_1474_, v_h_1489_, v_depth_1470_, v_k_1477_, v_v_1478_);
v_i_1473_ = v___x_1490_;
v_entries_1474_ = v___x_1491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1493_, lean_object* v_keys_1494_, lean_object* v_vals_1495_, lean_object* v_i_1496_, lean_object* v_entries_1497_){
_start:
{
size_t v_depth_boxed_1498_; lean_object* v_res_1499_; 
v_depth_boxed_1498_ = lean_unbox_usize(v_depth_1493_);
lean_dec(v_depth_1493_);
v_res_1499_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1498_, v_keys_1494_, v_vals_1495_, v_i_1496_, v_entries_1497_);
lean_dec_ref(v_vals_1495_);
lean_dec_ref(v_keys_1494_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_){
_start:
{
size_t v_x_6667__boxed_1505_; size_t v_x_6668__boxed_1506_; lean_object* v_res_1507_; 
v_x_6667__boxed_1505_ = lean_unbox_usize(v_x_1501_);
lean_dec(v_x_1501_);
v_x_6668__boxed_1506_ = lean_unbox_usize(v_x_1502_);
lean_dec(v_x_1502_);
v_res_1507_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1500_, v_x_6667__boxed_1505_, v_x_6668__boxed_1506_, v_x_1503_, v_x_1504_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object* v_x_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_){
_start:
{
size_t v___x_1511_; size_t v___x_1512_; size_t v___x_1513_; uint64_t v___x_1514_; size_t v___x_1515_; size_t v___x_1516_; lean_object* v___x_1517_; 
v___x_1511_ = lean_ptr_addr(v_x_1509_);
v___x_1512_ = ((size_t)3ULL);
v___x_1513_ = lean_usize_shift_right(v___x_1511_, v___x_1512_);
v___x_1514_ = lean_usize_to_uint64(v___x_1513_);
v___x_1515_ = lean_uint64_to_usize(v___x_1514_);
v___x_1516_ = ((size_t)1ULL);
v___x_1517_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1508_, v___x_1515_, v___x_1516_, v_x_1509_, v_x_1510_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object* v_e_1518_, lean_object* v_a_1519_, lean_object* v_s_1520_){
_start:
{
lean_object* v_rings_1521_; lean_object* v_typeIdOf_1522_; lean_object* v_exprToRingId_1523_; lean_object* v_semirings_1524_; lean_object* v_stypeIdOf_1525_; lean_object* v_exprToSemiringId_1526_; lean_object* v_ncRings_1527_; lean_object* v_exprToNCRingId_1528_; lean_object* v_nctypeIdOf_1529_; lean_object* v_ncSemirings_1530_; lean_object* v_exprToNCSemiringId_1531_; lean_object* v_ncstypeIdOf_1532_; lean_object* v_steps_1533_; uint8_t v_reportedMaxDegreeIssue_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1542_; 
v_rings_1521_ = lean_ctor_get(v_s_1520_, 0);
v_typeIdOf_1522_ = lean_ctor_get(v_s_1520_, 1);
v_exprToRingId_1523_ = lean_ctor_get(v_s_1520_, 2);
v_semirings_1524_ = lean_ctor_get(v_s_1520_, 3);
v_stypeIdOf_1525_ = lean_ctor_get(v_s_1520_, 4);
v_exprToSemiringId_1526_ = lean_ctor_get(v_s_1520_, 5);
v_ncRings_1527_ = lean_ctor_get(v_s_1520_, 6);
v_exprToNCRingId_1528_ = lean_ctor_get(v_s_1520_, 7);
v_nctypeIdOf_1529_ = lean_ctor_get(v_s_1520_, 8);
v_ncSemirings_1530_ = lean_ctor_get(v_s_1520_, 9);
v_exprToNCSemiringId_1531_ = lean_ctor_get(v_s_1520_, 10);
v_ncstypeIdOf_1532_ = lean_ctor_get(v_s_1520_, 11);
v_steps_1533_ = lean_ctor_get(v_s_1520_, 12);
v_reportedMaxDegreeIssue_1534_ = lean_ctor_get_uint8(v_s_1520_, sizeof(void*)*13);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_s_1520_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1536_ = v_s_1520_;
v_isShared_1537_ = v_isSharedCheck_1542_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_steps_1533_);
lean_inc(v_ncstypeIdOf_1532_);
lean_inc(v_exprToNCSemiringId_1531_);
lean_inc(v_ncSemirings_1530_);
lean_inc(v_nctypeIdOf_1529_);
lean_inc(v_exprToNCRingId_1528_);
lean_inc(v_ncRings_1527_);
lean_inc(v_exprToSemiringId_1526_);
lean_inc(v_stypeIdOf_1525_);
lean_inc(v_semirings_1524_);
lean_inc(v_exprToRingId_1523_);
lean_inc(v_typeIdOf_1522_);
lean_inc(v_rings_1521_);
lean_dec(v_s_1520_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1542_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; lean_object* v___x_1540_; 
lean_inc(v_a_1519_);
v___x_1538_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_exprToSemiringId_1526_, v_e_1518_, v_a_1519_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 5, v___x_1538_);
v___x_1540_ = v___x_1536_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_rings_1521_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_typeIdOf_1522_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_exprToRingId_1523_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_semirings_1524_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v_stypeIdOf_1525_);
lean_ctor_set(v_reuseFailAlloc_1541_, 5, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1541_, 6, v_ncRings_1527_);
lean_ctor_set(v_reuseFailAlloc_1541_, 7, v_exprToNCRingId_1528_);
lean_ctor_set(v_reuseFailAlloc_1541_, 8, v_nctypeIdOf_1529_);
lean_ctor_set(v_reuseFailAlloc_1541_, 9, v_ncSemirings_1530_);
lean_ctor_set(v_reuseFailAlloc_1541_, 10, v_exprToNCSemiringId_1531_);
lean_ctor_set(v_reuseFailAlloc_1541_, 11, v_ncstypeIdOf_1532_);
lean_ctor_set(v_reuseFailAlloc_1541_, 12, v_steps_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1541_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1534_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object* v_e_1543_, lean_object* v_a_1544_, lean_object* v_s_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(v_e_1543_, v_a_1544_, v_s_1545_);
lean_dec(v_a_1544_);
return v_res_1546_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0));
v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object* v_e_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1550_, v_a_1552_, v_a_1557_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
if (lean_obj_tag(v_a_1564_) == 1)
{
lean_object* v_val_1565_; uint8_t v___x_1566_; 
v_val_1565_ = lean_ctor_get(v_a_1564_, 0);
lean_inc(v_val_1565_);
lean_dec_ref_known(v_a_1564_, 1);
v___x_1566_ = lean_nat_dec_eq(v_val_1565_, v_a_1551_);
lean_dec(v_val_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1553_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; uint8_t v_verbose_1569_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v_verbose_1569_ = lean_ctor_get_uint8(v_a_1568_, 0);
lean_dec(v_a_1568_);
if (v_verbose_1569_ == 0)
{
lean_dec_ref(v_e_1550_);
goto v___jp_1560_;
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1570_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1);
v___x_1571_ = l_Lean_indentExpr(v_e_1550_);
v___x_1572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = l_Lean_Meta_Sym_reportIssue(v___x_1572_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_dec_ref_known(v___x_1573_, 1);
goto v___jp_1560_;
}
else
{
return v___x_1573_;
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v_e_1550_);
v_a_1574_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1567_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1567_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_dec_ref(v_e_1550_);
goto v___jp_1560_;
}
}
else
{
lean_object* v___f_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec(v_a_1564_);
lean_inc(v_a_1551_);
v___f_1582_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1582_, 0, v_e_1550_);
lean_closure_set(v___f_1582_, 1, v_a_1551_);
v___x_1583_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1584_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1583_, v___f_1582_, v_a_1552_);
return v___x_1584_;
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_e_1550_);
v_a_1585_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1563_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1563_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
v___jp_1560_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object* v_e_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec(v_a_1594_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object* v_e_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1604_, v_a_1605_, v_a_1606_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object* v_e_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec(v_a_1619_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object* v_00_u03b2_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_1633_, v_x_1634_, v_x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_1637_, lean_object* v_x_1638_, size_t v_x_1639_, size_t v_x_1640_, lean_object* v_x_1641_, lean_object* v_x_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1638_, v_x_1639_, v_x_1640_, v_x_1641_, v_x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_){
_start:
{
size_t v_x_6953__boxed_1650_; size_t v_x_6954__boxed_1651_; lean_object* v_res_1652_; 
v_x_6953__boxed_1650_ = lean_unbox_usize(v_x_1646_);
lean_dec(v_x_1646_);
v_x_6954__boxed_1651_ = lean_unbox_usize(v_x_1647_);
lean_dec(v_x_1647_);
v_res_1652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_1644_, v_x_1645_, v_x_6953__boxed_1650_, v_x_6954__boxed_1651_, v_x_1648_, v_x_1649_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1653_, lean_object* v_n_1654_, lean_object* v_k_1655_, lean_object* v_v_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_1654_, v_k_1655_, v_v_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1658_, size_t v_depth_1659_, lean_object* v_keys_1660_, lean_object* v_vals_1661_, lean_object* v_heq_1662_, lean_object* v_i_1663_, lean_object* v_entries_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_1659_, v_keys_1660_, v_vals_1661_, v_i_1663_, v_entries_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1666_, lean_object* v_depth_1667_, lean_object* v_keys_1668_, lean_object* v_vals_1669_, lean_object* v_heq_1670_, lean_object* v_i_1671_, lean_object* v_entries_1672_){
_start:
{
size_t v_depth_boxed_1673_; lean_object* v_res_1674_; 
v_depth_boxed_1673_ = lean_unbox_usize(v_depth_1667_);
lean_dec(v_depth_1667_);
v_res_1674_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_1666_, v_depth_boxed_1673_, v_keys_1668_, v_vals_1669_, v_heq_1670_, v_i_1671_, v_entries_1672_);
lean_dec_ref(v_vals_1669_);
lean_dec_ref(v_keys_1668_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1676_, v_x_1677_, v_x_1678_, v_x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object* v_e_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1681_, v___y_1682_, v___y_1683_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object* v_e_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(v_e_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object* v_e_1711_, lean_object* v___f_1712_, lean_object* v___f_1713_, lean_object* v_size_1714_, lean_object* v_s_1715_){
_start:
{
lean_object* v_id_1716_; lean_object* v_type_1717_; lean_object* v_u_1718_; lean_object* v_semiringInst_1719_; lean_object* v_addFn_x3f_1720_; lean_object* v_mulFn_x3f_1721_; lean_object* v_powFn_x3f_1722_; lean_object* v_natCastFn_x3f_1723_; lean_object* v_denote_1724_; lean_object* v_vars_1725_; lean_object* v_varMap_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1735_; 
v_id_1716_ = lean_ctor_get(v_s_1715_, 0);
v_type_1717_ = lean_ctor_get(v_s_1715_, 1);
v_u_1718_ = lean_ctor_get(v_s_1715_, 2);
v_semiringInst_1719_ = lean_ctor_get(v_s_1715_, 3);
v_addFn_x3f_1720_ = lean_ctor_get(v_s_1715_, 4);
v_mulFn_x3f_1721_ = lean_ctor_get(v_s_1715_, 5);
v_powFn_x3f_1722_ = lean_ctor_get(v_s_1715_, 6);
v_natCastFn_x3f_1723_ = lean_ctor_get(v_s_1715_, 7);
v_denote_1724_ = lean_ctor_get(v_s_1715_, 8);
v_vars_1725_ = lean_ctor_get(v_s_1715_, 9);
v_varMap_1726_ = lean_ctor_get(v_s_1715_, 10);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_s_1715_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1728_ = v_s_1715_;
v_isShared_1729_ = v_isSharedCheck_1735_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_varMap_1726_);
lean_inc(v_vars_1725_);
lean_inc(v_denote_1724_);
lean_inc(v_natCastFn_x3f_1723_);
lean_inc(v_powFn_x3f_1722_);
lean_inc(v_mulFn_x3f_1721_);
lean_inc(v_addFn_x3f_1720_);
lean_inc(v_semiringInst_1719_);
lean_inc(v_u_1718_);
lean_inc(v_type_1717_);
lean_inc(v_id_1716_);
lean_dec(v_s_1715_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1735_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
lean_inc_ref(v_e_1711_);
v___x_1730_ = l_Lean_PersistentArray_push___redArg(v_vars_1725_, v_e_1711_);
v___x_1731_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1712_, v___f_1713_, v_varMap_1726_, v_e_1711_, v_size_1714_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 10, v___x_1731_);
lean_ctor_set(v___x_1728_, 9, v___x_1730_);
v___x_1733_ = v___x_1728_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_id_1716_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_type_1717_);
lean_ctor_set(v_reuseFailAlloc_1734_, 2, v_u_1718_);
lean_ctor_set(v_reuseFailAlloc_1734_, 3, v_semiringInst_1719_);
lean_ctor_set(v_reuseFailAlloc_1734_, 4, v_addFn_x3f_1720_);
lean_ctor_set(v_reuseFailAlloc_1734_, 5, v_mulFn_x3f_1721_);
lean_ctor_set(v_reuseFailAlloc_1734_, 6, v_powFn_x3f_1722_);
lean_ctor_set(v_reuseFailAlloc_1734_, 7, v_natCastFn_x3f_1723_);
lean_ctor_set(v_reuseFailAlloc_1734_, 8, v_denote_1724_);
lean_ctor_set(v_reuseFailAlloc_1734_, 9, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1734_, 10, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object* v_toPure_1736_, lean_object* v_size_1737_, lean_object* v_____r_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_apply_2(v_toPure_1736_, lean_box(0), v_size_1737_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object* v_e_1740_, lean_object* v_inst_1741_, lean_object* v_toBind_1742_, lean_object* v___f_1743_, lean_object* v_____r_1744_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1745_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1746_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_1746_, 0, lean_box(0));
lean_closure_set(v___x_1746_, 1, v___x_1745_);
lean_closure_set(v___x_1746_, 2, v_e_1740_);
v___x_1747_ = lean_apply_2(v_inst_1741_, lean_box(0), v___x_1746_);
v___x_1748_ = lean_apply_4(v_toBind_1742_, lean_box(0), lean_box(0), v___x_1747_, v___f_1743_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object* v_inst_1749_, lean_object* v_e_1750_, lean_object* v_toBind_1751_, lean_object* v___f_1752_, lean_object* v_____r_1753_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_apply_1(v_inst_1749_, v_e_1750_);
v___x_1755_ = lean_apply_4(v_toBind_1751_, lean_box(0), lean_box(0), v___x_1754_, v___f_1752_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object* v___f_1756_, lean_object* v___f_1757_, lean_object* v_e_1758_, lean_object* v_toPure_1759_, lean_object* v_inst_1760_, lean_object* v_toBind_1761_, lean_object* v_inst_1762_, lean_object* v_modifySemiring_1763_, lean_object* v_s_1764_){
_start:
{
lean_object* v_vars_1765_; lean_object* v_varMap_1766_; lean_object* v___x_1767_; 
v_vars_1765_ = lean_ctor_get(v_s_1764_, 9);
lean_inc_ref(v_vars_1765_);
v_varMap_1766_ = lean_ctor_get(v_s_1764_, 10);
lean_inc_ref(v_varMap_1766_);
lean_dec_ref(v_s_1764_);
lean_inc_ref(v_e_1758_);
lean_inc_ref(v___f_1757_);
lean_inc_ref(v___f_1756_);
v___x_1767_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_1756_, v___f_1757_, v_varMap_1766_, v_e_1758_);
lean_dec_ref(v_varMap_1766_);
if (lean_obj_tag(v___x_1767_) == 1)
{
lean_object* v_val_1768_; lean_object* v___x_1769_; 
lean_dec_ref(v_vars_1765_);
lean_dec(v_modifySemiring_1763_);
lean_dec(v_inst_1762_);
lean_dec(v_toBind_1761_);
lean_dec(v_inst_1760_);
lean_dec_ref(v_e_1758_);
lean_dec_ref(v___f_1757_);
lean_dec_ref(v___f_1756_);
v_val_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_val_1768_);
lean_dec_ref_known(v___x_1767_, 1);
v___x_1769_ = lean_apply_2(v_toPure_1759_, lean_box(0), v_val_1768_);
return v___x_1769_;
}
else
{
lean_object* v_size_1770_; lean_object* v___f_1771_; lean_object* v___f_1772_; lean_object* v___f_1773_; lean_object* v___f_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec(v___x_1767_);
v_size_1770_ = lean_ctor_get(v_vars_1765_, 2);
lean_inc_n(v_size_1770_, 2);
lean_dec_ref(v_vars_1765_);
lean_inc_ref_n(v_e_1758_, 2);
v___f_1771_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1771_, 0, v_e_1758_);
lean_closure_set(v___f_1771_, 1, v___f_1756_);
lean_closure_set(v___f_1771_, 2, v___f_1757_);
lean_closure_set(v___f_1771_, 3, v_size_1770_);
v___f_1772_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1772_, 0, v_toPure_1759_);
lean_closure_set(v___f_1772_, 1, v_size_1770_);
lean_inc_n(v_toBind_1761_, 2);
v___f_1773_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1773_, 0, v_e_1758_);
lean_closure_set(v___f_1773_, 1, v_inst_1760_);
lean_closure_set(v___f_1773_, 2, v_toBind_1761_);
lean_closure_set(v___f_1773_, 3, v___f_1772_);
v___f_1774_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1774_, 0, v_inst_1762_);
lean_closure_set(v___f_1774_, 1, v_e_1758_);
lean_closure_set(v___f_1774_, 2, v_toBind_1761_);
lean_closure_set(v___f_1774_, 3, v___f_1773_);
v___x_1775_ = lean_apply_1(v_modifySemiring_1763_, v___f_1771_);
v___x_1776_ = lean_apply_4(v_toBind_1761_, lean_box(0), lean_box(0), v___x_1775_, v___f_1774_);
return v___x_1776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_e_1783_){
_start:
{
lean_object* v_toApplicative_1784_; lean_object* v_toBind_1785_; lean_object* v_getSemiring_1786_; lean_object* v_modifySemiring_1787_; lean_object* v_toPure_1788_; lean_object* v___f_1789_; lean_object* v___f_1790_; lean_object* v___f_1791_; lean_object* v___x_1792_; 
v_toApplicative_1784_ = lean_ctor_get(v_inst_1780_, 0);
lean_inc_ref(v_toApplicative_1784_);
v_toBind_1785_ = lean_ctor_get(v_inst_1780_, 1);
lean_inc_n(v_toBind_1785_, 2);
lean_dec_ref(v_inst_1780_);
v_getSemiring_1786_ = lean_ctor_get(v_inst_1781_, 0);
lean_inc(v_getSemiring_1786_);
v_modifySemiring_1787_ = lean_ctor_get(v_inst_1781_, 1);
lean_inc(v_modifySemiring_1787_);
lean_dec_ref(v_inst_1781_);
v_toPure_1788_ = lean_ctor_get(v_toApplicative_1784_, 1);
lean_inc(v_toPure_1788_);
lean_dec_ref(v_toApplicative_1784_);
v___f_1789_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0));
v___f_1790_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1));
v___f_1791_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1791_, 0, v___f_1789_);
lean_closure_set(v___f_1791_, 1, v___f_1790_);
lean_closure_set(v___f_1791_, 2, v_e_1783_);
lean_closure_set(v___f_1791_, 3, v_toPure_1788_);
lean_closure_set(v___f_1791_, 4, v_inst_1779_);
lean_closure_set(v___f_1791_, 5, v_toBind_1785_);
lean_closure_set(v___f_1791_, 6, v_inst_1782_);
lean_closure_set(v___f_1791_, 7, v_modifySemiring_1787_);
v___x_1792_ = lean_apply_4(v_toBind_1785_, lean_box(0), lean_box(0), v_getSemiring_1786_, v___f_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object* v_m_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_e_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v_inst_1794_, v_inst_1795_, v_inst_1796_, v_inst_1797_, v_e_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(lean_object* v___y_1800_, lean_object* v_e_1801_, lean_object* v_size_1802_, lean_object* v_s_1803_){
_start:
{
lean_object* v_rings_1804_; lean_object* v_typeIdOf_1805_; lean_object* v_exprToRingId_1806_; lean_object* v_semirings_1807_; lean_object* v_stypeIdOf_1808_; lean_object* v_exprToSemiringId_1809_; lean_object* v_ncRings_1810_; lean_object* v_exprToNCRingId_1811_; lean_object* v_nctypeIdOf_1812_; lean_object* v_ncSemirings_1813_; lean_object* v_exprToNCSemiringId_1814_; lean_object* v_ncstypeIdOf_1815_; lean_object* v_steps_1816_; uint8_t v_reportedMaxDegreeIssue_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v_rings_1804_ = lean_ctor_get(v_s_1803_, 0);
v_typeIdOf_1805_ = lean_ctor_get(v_s_1803_, 1);
v_exprToRingId_1806_ = lean_ctor_get(v_s_1803_, 2);
v_semirings_1807_ = lean_ctor_get(v_s_1803_, 3);
v_stypeIdOf_1808_ = lean_ctor_get(v_s_1803_, 4);
v_exprToSemiringId_1809_ = lean_ctor_get(v_s_1803_, 5);
v_ncRings_1810_ = lean_ctor_get(v_s_1803_, 6);
v_exprToNCRingId_1811_ = lean_ctor_get(v_s_1803_, 7);
v_nctypeIdOf_1812_ = lean_ctor_get(v_s_1803_, 8);
v_ncSemirings_1813_ = lean_ctor_get(v_s_1803_, 9);
v_exprToNCSemiringId_1814_ = lean_ctor_get(v_s_1803_, 10);
v_ncstypeIdOf_1815_ = lean_ctor_get(v_s_1803_, 11);
v_steps_1816_ = lean_ctor_get(v_s_1803_, 12);
v_reportedMaxDegreeIssue_1817_ = lean_ctor_get_uint8(v_s_1803_, sizeof(void*)*13);
v___x_1818_ = lean_array_get_size(v_semirings_1807_);
v___x_1819_ = lean_nat_dec_lt(v___y_1800_, v___x_1818_);
if (v___x_1819_ == 0)
{
lean_dec(v_size_1802_);
lean_dec_ref(v_e_1801_);
return v_s_1803_;
}
else
{
lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1862_; 
lean_inc(v_steps_1816_);
lean_inc_ref(v_ncstypeIdOf_1815_);
lean_inc_ref(v_exprToNCSemiringId_1814_);
lean_inc_ref(v_ncSemirings_1813_);
lean_inc_ref(v_nctypeIdOf_1812_);
lean_inc_ref(v_exprToNCRingId_1811_);
lean_inc_ref(v_ncRings_1810_);
lean_inc_ref(v_exprToSemiringId_1809_);
lean_inc_ref(v_stypeIdOf_1808_);
lean_inc_ref(v_semirings_1807_);
lean_inc_ref(v_exprToRingId_1806_);
lean_inc_ref(v_typeIdOf_1805_);
lean_inc_ref(v_rings_1804_);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_s_1803_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; lean_object* v_unused_1864_; lean_object* v_unused_1865_; lean_object* v_unused_1866_; lean_object* v_unused_1867_; lean_object* v_unused_1868_; lean_object* v_unused_1869_; lean_object* v_unused_1870_; lean_object* v_unused_1871_; lean_object* v_unused_1872_; lean_object* v_unused_1873_; lean_object* v_unused_1874_; lean_object* v_unused_1875_; 
v_unused_1863_ = lean_ctor_get(v_s_1803_, 12);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v_s_1803_, 11);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_s_1803_, 10);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_s_1803_, 9);
lean_dec(v_unused_1866_);
v_unused_1867_ = lean_ctor_get(v_s_1803_, 8);
lean_dec(v_unused_1867_);
v_unused_1868_ = lean_ctor_get(v_s_1803_, 7);
lean_dec(v_unused_1868_);
v_unused_1869_ = lean_ctor_get(v_s_1803_, 6);
lean_dec(v_unused_1869_);
v_unused_1870_ = lean_ctor_get(v_s_1803_, 5);
lean_dec(v_unused_1870_);
v_unused_1871_ = lean_ctor_get(v_s_1803_, 4);
lean_dec(v_unused_1871_);
v_unused_1872_ = lean_ctor_get(v_s_1803_, 3);
lean_dec(v_unused_1872_);
v_unused_1873_ = lean_ctor_get(v_s_1803_, 2);
lean_dec(v_unused_1873_);
v_unused_1874_ = lean_ctor_get(v_s_1803_, 1);
lean_dec(v_unused_1874_);
v_unused_1875_ = lean_ctor_get(v_s_1803_, 0);
lean_dec(v_unused_1875_);
v___x_1821_ = v_s_1803_;
v_isShared_1822_ = v_isSharedCheck_1862_;
goto v_resetjp_1820_;
}
else
{
lean_dec(v_s_1803_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1862_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v_v_1823_; lean_object* v_toSemiring_1824_; lean_object* v_ringId_1825_; lean_object* v_commSemiringInst_1826_; lean_object* v_addRightCancelInst_x3f_1827_; lean_object* v_toQFn_x3f_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1861_; 
v_v_1823_ = lean_array_fget(v_semirings_1807_, v___y_1800_);
v_toSemiring_1824_ = lean_ctor_get(v_v_1823_, 0);
v_ringId_1825_ = lean_ctor_get(v_v_1823_, 1);
v_commSemiringInst_1826_ = lean_ctor_get(v_v_1823_, 2);
v_addRightCancelInst_x3f_1827_ = lean_ctor_get(v_v_1823_, 3);
v_toQFn_x3f_1828_ = lean_ctor_get(v_v_1823_, 4);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_v_1823_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1830_ = v_v_1823_;
v_isShared_1831_ = v_isSharedCheck_1861_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_toQFn_x3f_1828_);
lean_inc(v_addRightCancelInst_x3f_1827_);
lean_inc(v_commSemiringInst_1826_);
lean_inc(v_ringId_1825_);
lean_inc(v_toSemiring_1824_);
lean_dec(v_v_1823_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1861_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v_id_1832_; lean_object* v_type_1833_; lean_object* v_u_1834_; lean_object* v_semiringInst_1835_; lean_object* v_addFn_x3f_1836_; lean_object* v_mulFn_x3f_1837_; lean_object* v_powFn_x3f_1838_; lean_object* v_natCastFn_x3f_1839_; lean_object* v_denote_1840_; lean_object* v_vars_1841_; lean_object* v_varMap_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1860_; 
v_id_1832_ = lean_ctor_get(v_toSemiring_1824_, 0);
v_type_1833_ = lean_ctor_get(v_toSemiring_1824_, 1);
v_u_1834_ = lean_ctor_get(v_toSemiring_1824_, 2);
v_semiringInst_1835_ = lean_ctor_get(v_toSemiring_1824_, 3);
v_addFn_x3f_1836_ = lean_ctor_get(v_toSemiring_1824_, 4);
v_mulFn_x3f_1837_ = lean_ctor_get(v_toSemiring_1824_, 5);
v_powFn_x3f_1838_ = lean_ctor_get(v_toSemiring_1824_, 6);
v_natCastFn_x3f_1839_ = lean_ctor_get(v_toSemiring_1824_, 7);
v_denote_1840_ = lean_ctor_get(v_toSemiring_1824_, 8);
v_vars_1841_ = lean_ctor_get(v_toSemiring_1824_, 9);
v_varMap_1842_ = lean_ctor_get(v_toSemiring_1824_, 10);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_toSemiring_1824_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1844_ = v_toSemiring_1824_;
v_isShared_1845_ = v_isSharedCheck_1860_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_varMap_1842_);
lean_inc(v_vars_1841_);
lean_inc(v_denote_1840_);
lean_inc(v_natCastFn_x3f_1839_);
lean_inc(v_powFn_x3f_1838_);
lean_inc(v_mulFn_x3f_1837_);
lean_inc(v_addFn_x3f_1836_);
lean_inc(v_semiringInst_1835_);
lean_inc(v_u_1834_);
lean_inc(v_type_1833_);
lean_inc(v_id_1832_);
lean_dec(v_toSemiring_1824_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1860_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v_xs_x27_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1846_ = lean_box(0);
v_xs_x27_1847_ = lean_array_fset(v_semirings_1807_, v___y_1800_, v___x_1846_);
lean_inc_ref(v_e_1801_);
v___x_1848_ = l_Lean_PersistentArray_push___redArg(v_vars_1841_, v_e_1801_);
v___x_1849_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_varMap_1842_, v_e_1801_, v_size_1802_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 10, v___x_1849_);
lean_ctor_set(v___x_1844_, 9, v___x_1848_);
v___x_1851_ = v___x_1844_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_id_1832_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_type_1833_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_u_1834_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_semiringInst_1835_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_addFn_x3f_1836_);
lean_ctor_set(v_reuseFailAlloc_1859_, 5, v_mulFn_x3f_1837_);
lean_ctor_set(v_reuseFailAlloc_1859_, 6, v_powFn_x3f_1838_);
lean_ctor_set(v_reuseFailAlloc_1859_, 7, v_natCastFn_x3f_1839_);
lean_ctor_set(v_reuseFailAlloc_1859_, 8, v_denote_1840_);
lean_ctor_set(v_reuseFailAlloc_1859_, 9, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1859_, 10, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1851_);
v___x_1853_ = v___x_1830_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_ringId_1825_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_commSemiringInst_1826_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_addRightCancelInst_x3f_1827_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_toQFn_x3f_1828_);
v___x_1853_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = lean_array_fset(v_xs_x27_1847_, v___y_1800_, v___x_1853_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 3, v___x_1854_);
v___x_1856_ = v___x_1821_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_rings_1804_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_typeIdOf_1805_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_exprToRingId_1806_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_stypeIdOf_1808_);
lean_ctor_set(v_reuseFailAlloc_1857_, 5, v_exprToSemiringId_1809_);
lean_ctor_set(v_reuseFailAlloc_1857_, 6, v_ncRings_1810_);
lean_ctor_set(v_reuseFailAlloc_1857_, 7, v_exprToNCRingId_1811_);
lean_ctor_set(v_reuseFailAlloc_1857_, 8, v_nctypeIdOf_1812_);
lean_ctor_set(v_reuseFailAlloc_1857_, 9, v_ncSemirings_1813_);
lean_ctor_set(v_reuseFailAlloc_1857_, 10, v_exprToNCSemiringId_1814_);
lean_ctor_set(v_reuseFailAlloc_1857_, 11, v_ncstypeIdOf_1815_);
lean_ctor_set(v_reuseFailAlloc_1857_, 12, v_steps_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1817_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed(lean_object* v___y_1876_, lean_object* v_e_1877_, lean_object* v_size_1878_, lean_object* v_s_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(v___y_1876_, v_e_1877_, v_size_1878_, v_s_1879_);
lean_dec(v___y_1876_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(lean_object* v_e_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1945_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1945_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1945_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v_toSemiring_1899_; lean_object* v_vars_1900_; lean_object* v_varMap_1901_; lean_object* v___x_1902_; 
v_toSemiring_1899_ = lean_ctor_get(v_a_1895_, 0);
lean_inc_ref(v_toSemiring_1899_);
lean_dec(v_a_1895_);
v_vars_1900_ = lean_ctor_get(v_toSemiring_1899_, 9);
lean_inc_ref(v_vars_1900_);
v_varMap_1901_ = lean_ctor_get(v_toSemiring_1899_, 10);
lean_inc_ref(v_varMap_1901_);
lean_dec_ref(v_toSemiring_1899_);
v___x_1902_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_varMap_1901_, v_e_1881_);
lean_dec_ref(v_varMap_1901_);
if (lean_obj_tag(v___x_1902_) == 1)
{
lean_object* v_val_1903_; lean_object* v___x_1905_; 
lean_dec_ref(v_vars_1900_);
lean_dec_ref(v_e_1881_);
v_val_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_val_1903_);
lean_dec_ref_known(v___x_1902_, 1);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v_val_1903_);
v___x_1905_ = v___x_1897_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_val_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
else
{
lean_object* v_size_1907_; lean_object* v___f_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
lean_dec(v___x_1902_);
lean_del_object(v___x_1897_);
v_size_1907_ = lean_ctor_get(v_vars_1900_, 2);
lean_inc_n(v_size_1907_, 2);
lean_dec_ref(v_vars_1900_);
lean_inc_ref(v_e_1881_);
lean_inc(v___y_1882_);
v___f_1908_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1908_, 0, v___y_1882_);
lean_closure_set(v___f_1908_, 1, v_e_1881_);
lean_closure_set(v___f_1908_, 2, v_size_1907_);
v___x_1909_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1910_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1909_, v___f_1908_, v___y_1883_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v___x_1911_; 
lean_dec_ref_known(v___x_1910_, 1);
lean_inc_ref(v_e_1881_);
v___x_1911_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1881_, v___y_1882_, v___y_1883_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v___x_1912_; 
lean_dec_ref_known(v___x_1911_, 1);
v___x_1912_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1909_, v_e_1881_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; 
v_unused_1920_ = lean_ctor_get(v___x_1912_, 0);
lean_dec(v_unused_1920_);
v___x_1914_ = v___x_1912_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_dec(v___x_1912_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v_size_1907_);
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_size_1907_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_size_1907_);
v_a_1921_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1912_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1912_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v_size_1907_);
lean_dec_ref(v_e_1881_);
v_a_1929_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1911_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1911_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec(v_size_1907_);
lean_dec_ref(v_e_1881_);
v_a_1937_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1910_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1910_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v_e_1881_);
v_a_1946_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1894_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1894_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___boxed(lean_object* v_e_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object* v_e_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar___boxed(lean_object* v_e_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVar(v_e_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec(v_a_1983_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object* v_a_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_nat_to_int(v_a_1996_);
return v___x_1997_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object* v_msg_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v___x_2012_; lean_object* v___f_2013_; lean_object* v___x_40259__overap_2014_; lean_object* v___x_2015_; 
v___x_2012_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0);
v___f_2013_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2013_, 0, v___x_2012_);
v___x_40259__overap_2014_ = lean_panic_fn_borrowed(v___f_2013_, v_msg_1999_);
lean_dec_ref(v___f_2013_);
lean_inc(v___y_2010_);
lean_inc_ref(v___y_2009_);
lean_inc(v___y_2008_);
lean_inc_ref(v___y_2007_);
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
lean_inc(v___y_2002_);
lean_inc(v___y_2001_);
lean_inc(v___y_2000_);
v___x_2015_ = lean_apply_12(v___x_40259__overap_2014_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, lean_box(0));
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object* v_msg_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_msg_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec(v___y_2017_);
return v_res_2029_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0));
v___x_2032_ = l_Lean_stringToMessageData(v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(lean_object* v_type_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; 
lean_inc_ref(v_type_2033_);
v___x_2040_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2053_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2053_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2053_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
if (lean_obj_tag(v_a_2041_) == 1)
{
lean_object* v_val_2045_; lean_object* v___x_2047_; 
lean_dec_ref(v_type_2033_);
v_val_2045_ = lean_ctor_get(v_a_2041_, 0);
lean_inc(v_val_2045_);
lean_dec_ref_known(v_a_2041_, 1);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v_val_2045_);
v___x_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_val_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_del_object(v___x_2043_);
lean_dec(v_a_2041_);
v___x_2049_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1);
v___x_2050_ = l_Lean_indentExpr(v_type_2033_);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2049_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_2051_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
return v___x_2052_;
}
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec_ref(v_type_2033_);
v_a_2054_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2040_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2040_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_type_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(lean_object* v_type_2070_, lean_object* v_u_2071_, lean_object* v_instDeclName_2072_, lean_object* v_declName_2073_, lean_object* v_expectedInst_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2087_ = lean_box(0);
lean_inc_n(v_u_2071_, 2);
v___x_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2088_, 0, v_u_2071_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2089_, 0, v_u_2071_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2090_, 0, v_u_2071_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
lean_inc_ref(v___x_2090_);
v___x_2091_ = l_Lean_mkConst(v_instDeclName_2072_, v___x_2090_);
lean_inc_ref_n(v_type_2070_, 3);
v___x_2092_ = l_Lean_mkApp3(v___x_2091_, v_type_2070_, v_type_2070_, v_type_2070_);
v___x_2093_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2092_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2095_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc_n(v_a_2094_, 2);
lean_dec_ref_known(v___x_2093_, 1);
lean_inc(v_declName_2073_);
v___x_2095_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2073_, v_a_2094_, v_expectedInst_2074_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_dec_ref_known(v___x_2095_, 1);
v___x_2096_ = l_Lean_mkConst(v_declName_2073_, v___x_2090_);
lean_inc_ref_n(v_type_2070_, 2);
v___x_2097_ = l_Lean_mkApp4(v___x_2096_, v_type_2070_, v_type_2070_, v_type_2070_, v_a_2094_);
v___x_2098_ = l_Lean_Meta_Sym_canon(v___x_2097_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v___x_2100_ = l_Lean_Meta_Sym_shareCommon(v_a_2099_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
return v___x_2100_;
}
else
{
return v___x_2098_;
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec(v_a_2094_);
lean_dec_ref_known(v___x_2090_, 2);
lean_dec(v_declName_2073_);
lean_dec_ref(v_type_2070_);
v_a_2101_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2095_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2095_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2090_, 2);
lean_dec_ref(v_expectedInst_2074_);
lean_dec(v_declName_2073_);
lean_dec_ref(v_type_2070_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_type_2109_ = _args[0];
lean_object* v_u_2110_ = _args[1];
lean_object* v_instDeclName_2111_ = _args[2];
lean_object* v_declName_2112_ = _args[3];
lean_object* v_expectedInst_2113_ = _args[4];
lean_object* v___y_2114_ = _args[5];
lean_object* v___y_2115_ = _args[6];
lean_object* v___y_2116_ = _args[7];
lean_object* v___y_2117_ = _args[8];
lean_object* v___y_2118_ = _args[9];
lean_object* v___y_2119_ = _args[10];
lean_object* v___y_2120_ = _args[11];
lean_object* v___y_2121_ = _args[12];
lean_object* v___y_2122_ = _args[13];
lean_object* v___y_2123_ = _args[14];
lean_object* v___y_2124_ = _args[15];
lean_object* v___y_2125_ = _args[16];
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2109_, v_u_2110_, v_instDeclName_2111_, v_declName_2112_, v_expectedInst_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec(v___y_2114_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object* v_a_2127_, lean_object* v_s_2128_){
_start:
{
lean_object* v_toRing_2129_; lean_object* v_invFn_x3f_2130_; lean_object* v_semiringId_x3f_2131_; lean_object* v_commSemiringInst_2132_; lean_object* v_commRingInst_2133_; lean_object* v_noZeroDivInst_x3f_2134_; lean_object* v_fieldInst_x3f_2135_; lean_object* v_powIdentityInst_x3f_2136_; lean_object* v_denoteEntries_2137_; lean_object* v_nextId_2138_; lean_object* v_steps_2139_; lean_object* v_queue_2140_; lean_object* v_basis_2141_; lean_object* v_diseqs_2142_; uint8_t v_recheck_2143_; lean_object* v_invSet_2144_; lean_object* v_powIdentityVarCount_2145_; lean_object* v_numEq0_x3f_2146_; uint8_t v_numEq0Updated_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2179_; 
v_toRing_2129_ = lean_ctor_get(v_s_2128_, 0);
v_invFn_x3f_2130_ = lean_ctor_get(v_s_2128_, 1);
v_semiringId_x3f_2131_ = lean_ctor_get(v_s_2128_, 2);
v_commSemiringInst_2132_ = lean_ctor_get(v_s_2128_, 3);
v_commRingInst_2133_ = lean_ctor_get(v_s_2128_, 4);
v_noZeroDivInst_x3f_2134_ = lean_ctor_get(v_s_2128_, 5);
v_fieldInst_x3f_2135_ = lean_ctor_get(v_s_2128_, 6);
v_powIdentityInst_x3f_2136_ = lean_ctor_get(v_s_2128_, 7);
v_denoteEntries_2137_ = lean_ctor_get(v_s_2128_, 8);
v_nextId_2138_ = lean_ctor_get(v_s_2128_, 9);
v_steps_2139_ = lean_ctor_get(v_s_2128_, 10);
v_queue_2140_ = lean_ctor_get(v_s_2128_, 11);
v_basis_2141_ = lean_ctor_get(v_s_2128_, 12);
v_diseqs_2142_ = lean_ctor_get(v_s_2128_, 13);
v_recheck_2143_ = lean_ctor_get_uint8(v_s_2128_, sizeof(void*)*17);
v_invSet_2144_ = lean_ctor_get(v_s_2128_, 14);
v_powIdentityVarCount_2145_ = lean_ctor_get(v_s_2128_, 15);
v_numEq0_x3f_2146_ = lean_ctor_get(v_s_2128_, 16);
v_numEq0Updated_2147_ = lean_ctor_get_uint8(v_s_2128_, sizeof(void*)*17 + 1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_s_2128_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2149_ = v_s_2128_;
v_isShared_2150_ = v_isSharedCheck_2179_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_numEq0_x3f_2146_);
lean_inc(v_powIdentityVarCount_2145_);
lean_inc(v_invSet_2144_);
lean_inc(v_diseqs_2142_);
lean_inc(v_basis_2141_);
lean_inc(v_queue_2140_);
lean_inc(v_steps_2139_);
lean_inc(v_nextId_2138_);
lean_inc(v_denoteEntries_2137_);
lean_inc(v_powIdentityInst_x3f_2136_);
lean_inc(v_fieldInst_x3f_2135_);
lean_inc(v_noZeroDivInst_x3f_2134_);
lean_inc(v_commRingInst_2133_);
lean_inc(v_commSemiringInst_2132_);
lean_inc(v_semiringId_x3f_2131_);
lean_inc(v_invFn_x3f_2130_);
lean_inc(v_toRing_2129_);
lean_dec(v_s_2128_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2179_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v_id_2151_; lean_object* v_type_2152_; lean_object* v_u_2153_; lean_object* v_ringInst_2154_; lean_object* v_semiringInst_2155_; lean_object* v_charInst_x3f_2156_; lean_object* v_addFn_x3f_2157_; lean_object* v_subFn_x3f_2158_; lean_object* v_negFn_x3f_2159_; lean_object* v_powFn_x3f_2160_; lean_object* v_intCastFn_x3f_2161_; lean_object* v_natCastFn_x3f_2162_; lean_object* v_one_x3f_2163_; lean_object* v_vars_2164_; lean_object* v_varMap_2165_; lean_object* v_denote_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2177_; 
v_id_2151_ = lean_ctor_get(v_toRing_2129_, 0);
v_type_2152_ = lean_ctor_get(v_toRing_2129_, 1);
v_u_2153_ = lean_ctor_get(v_toRing_2129_, 2);
v_ringInst_2154_ = lean_ctor_get(v_toRing_2129_, 3);
v_semiringInst_2155_ = lean_ctor_get(v_toRing_2129_, 4);
v_charInst_x3f_2156_ = lean_ctor_get(v_toRing_2129_, 5);
v_addFn_x3f_2157_ = lean_ctor_get(v_toRing_2129_, 6);
v_subFn_x3f_2158_ = lean_ctor_get(v_toRing_2129_, 8);
v_negFn_x3f_2159_ = lean_ctor_get(v_toRing_2129_, 9);
v_powFn_x3f_2160_ = lean_ctor_get(v_toRing_2129_, 10);
v_intCastFn_x3f_2161_ = lean_ctor_get(v_toRing_2129_, 11);
v_natCastFn_x3f_2162_ = lean_ctor_get(v_toRing_2129_, 12);
v_one_x3f_2163_ = lean_ctor_get(v_toRing_2129_, 13);
v_vars_2164_ = lean_ctor_get(v_toRing_2129_, 14);
v_varMap_2165_ = lean_ctor_get(v_toRing_2129_, 15);
v_denote_2166_ = lean_ctor_get(v_toRing_2129_, 16);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_toRing_2129_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; 
v_unused_2178_ = lean_ctor_get(v_toRing_2129_, 7);
lean_dec(v_unused_2178_);
v___x_2168_ = v_toRing_2129_;
v_isShared_2169_ = v_isSharedCheck_2177_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_denote_2166_);
lean_inc(v_varMap_2165_);
lean_inc(v_vars_2164_);
lean_inc(v_one_x3f_2163_);
lean_inc(v_natCastFn_x3f_2162_);
lean_inc(v_intCastFn_x3f_2161_);
lean_inc(v_powFn_x3f_2160_);
lean_inc(v_negFn_x3f_2159_);
lean_inc(v_subFn_x3f_2158_);
lean_inc(v_addFn_x3f_2157_);
lean_inc(v_charInst_x3f_2156_);
lean_inc(v_semiringInst_2155_);
lean_inc(v_ringInst_2154_);
lean_inc(v_u_2153_);
lean_inc(v_type_2152_);
lean_inc(v_id_2151_);
lean_dec(v_toRing_2129_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2177_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2170_, 0, v_a_2127_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 7, v___x_2170_);
v___x_2172_ = v___x_2168_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_id_2151_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_type_2152_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_u_2153_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v_ringInst_2154_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v_semiringInst_2155_);
lean_ctor_set(v_reuseFailAlloc_2176_, 5, v_charInst_x3f_2156_);
lean_ctor_set(v_reuseFailAlloc_2176_, 6, v_addFn_x3f_2157_);
lean_ctor_set(v_reuseFailAlloc_2176_, 7, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2176_, 8, v_subFn_x3f_2158_);
lean_ctor_set(v_reuseFailAlloc_2176_, 9, v_negFn_x3f_2159_);
lean_ctor_set(v_reuseFailAlloc_2176_, 10, v_powFn_x3f_2160_);
lean_ctor_set(v_reuseFailAlloc_2176_, 11, v_intCastFn_x3f_2161_);
lean_ctor_set(v_reuseFailAlloc_2176_, 12, v_natCastFn_x3f_2162_);
lean_ctor_set(v_reuseFailAlloc_2176_, 13, v_one_x3f_2163_);
lean_ctor_set(v_reuseFailAlloc_2176_, 14, v_vars_2164_);
lean_ctor_set(v_reuseFailAlloc_2176_, 15, v_varMap_2165_);
lean_ctor_set(v_reuseFailAlloc_2176_, 16, v_denote_2166_);
v___x_2172_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2174_; 
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2172_);
v___x_2174_ = v___x_2149_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_invFn_x3f_2130_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_semiringId_x3f_2131_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_commSemiringInst_2132_);
lean_ctor_set(v_reuseFailAlloc_2175_, 4, v_commRingInst_2133_);
lean_ctor_set(v_reuseFailAlloc_2175_, 5, v_noZeroDivInst_x3f_2134_);
lean_ctor_set(v_reuseFailAlloc_2175_, 6, v_fieldInst_x3f_2135_);
lean_ctor_set(v_reuseFailAlloc_2175_, 7, v_powIdentityInst_x3f_2136_);
lean_ctor_set(v_reuseFailAlloc_2175_, 8, v_denoteEntries_2137_);
lean_ctor_set(v_reuseFailAlloc_2175_, 9, v_nextId_2138_);
lean_ctor_set(v_reuseFailAlloc_2175_, 10, v_steps_2139_);
lean_ctor_set(v_reuseFailAlloc_2175_, 11, v_queue_2140_);
lean_ctor_set(v_reuseFailAlloc_2175_, 12, v_basis_2141_);
lean_ctor_set(v_reuseFailAlloc_2175_, 13, v_diseqs_2142_);
lean_ctor_set(v_reuseFailAlloc_2175_, 14, v_invSet_2144_);
lean_ctor_set(v_reuseFailAlloc_2175_, 15, v_powIdentityVarCount_2145_);
lean_ctor_set(v_reuseFailAlloc_2175_, 16, v_numEq0_x3f_2146_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*17, v_recheck_2143_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*17 + 1, v_numEq0Updated_2147_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2236_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2236_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2236_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_toRing_2197_; lean_object* v_mulFn_x3f_2198_; 
v_toRing_2197_ = lean_ctor_get(v_a_2193_, 0);
lean_inc_ref(v_toRing_2197_);
lean_dec(v_a_2193_);
v_mulFn_x3f_2198_ = lean_ctor_get(v_toRing_2197_, 7);
if (lean_obj_tag(v_mulFn_x3f_2198_) == 1)
{
lean_object* v_val_2199_; lean_object* v___x_2201_; 
lean_inc_ref(v_mulFn_x3f_2198_);
lean_dec_ref(v_toRing_2197_);
v_val_2199_ = lean_ctor_get(v_mulFn_x3f_2198_, 0);
lean_inc(v_val_2199_);
lean_dec_ref_known(v_mulFn_x3f_2198_, 1);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v_val_2199_);
v___x_2201_ = v___x_2195_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_val_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
else
{
lean_object* v_type_2203_; lean_object* v_u_2204_; lean_object* v_semiringInst_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v_expectedInst_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_del_object(v___x_2195_);
v_type_2203_ = lean_ctor_get(v_toRing_2197_, 1);
lean_inc_ref_n(v_type_2203_, 3);
v_u_2204_ = lean_ctor_get(v_toRing_2197_, 2);
lean_inc_n(v_u_2204_, 2);
v_semiringInst_2205_ = lean_ctor_get(v_toRing_2197_, 4);
lean_inc_ref(v_semiringInst_2205_);
lean_dec_ref(v_toRing_2197_);
v___x_2206_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_u_2204_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
lean_inc_ref(v___x_2208_);
v___x_2209_ = l_Lean_mkConst(v___x_2206_, v___x_2208_);
v___x_2210_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_2211_ = l_Lean_mkConst(v___x_2210_, v___x_2208_);
v___x_2212_ = l_Lean_mkAppB(v___x_2211_, v_type_2203_, v_semiringInst_2205_);
v_expectedInst_2213_ = l_Lean_mkAppB(v___x_2209_, v_type_2203_, v___x_2212_);
v___x_2214_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_2215_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_2216_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2203_, v_u_2204_, v___x_2214_, v___x_2215_, v_expectedInst_2213_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___f_2218_; lean_object* v___x_2219_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc_n(v_a_2217_, 2);
lean_dec_ref_known(v___x_2216_, 1);
v___f_2218_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2218_, 0, v_a_2217_);
v___x_2219_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2218_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; 
v_unused_2227_ = lean_ctor_get(v___x_2219_, 0);
lean_dec(v_unused_2227_);
v___x_2221_ = v___x_2219_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_dec(v___x_2219_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v_a_2217_);
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2217_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_a_2217_);
v_a_2228_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2219_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2219_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
return v___x_2216_;
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
v_a_2237_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2192_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2192_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec(v___y_2245_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object* v_a_2258_, lean_object* v_s_2259_){
_start:
{
lean_object* v_toRing_2260_; lean_object* v_invFn_x3f_2261_; lean_object* v_semiringId_x3f_2262_; lean_object* v_commSemiringInst_2263_; lean_object* v_commRingInst_2264_; lean_object* v_noZeroDivInst_x3f_2265_; lean_object* v_fieldInst_x3f_2266_; lean_object* v_powIdentityInst_x3f_2267_; lean_object* v_denoteEntries_2268_; lean_object* v_nextId_2269_; lean_object* v_steps_2270_; lean_object* v_queue_2271_; lean_object* v_basis_2272_; lean_object* v_diseqs_2273_; uint8_t v_recheck_2274_; lean_object* v_invSet_2275_; lean_object* v_powIdentityVarCount_2276_; lean_object* v_numEq0_x3f_2277_; uint8_t v_numEq0Updated_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2310_; 
v_toRing_2260_ = lean_ctor_get(v_s_2259_, 0);
v_invFn_x3f_2261_ = lean_ctor_get(v_s_2259_, 1);
v_semiringId_x3f_2262_ = lean_ctor_get(v_s_2259_, 2);
v_commSemiringInst_2263_ = lean_ctor_get(v_s_2259_, 3);
v_commRingInst_2264_ = lean_ctor_get(v_s_2259_, 4);
v_noZeroDivInst_x3f_2265_ = lean_ctor_get(v_s_2259_, 5);
v_fieldInst_x3f_2266_ = lean_ctor_get(v_s_2259_, 6);
v_powIdentityInst_x3f_2267_ = lean_ctor_get(v_s_2259_, 7);
v_denoteEntries_2268_ = lean_ctor_get(v_s_2259_, 8);
v_nextId_2269_ = lean_ctor_get(v_s_2259_, 9);
v_steps_2270_ = lean_ctor_get(v_s_2259_, 10);
v_queue_2271_ = lean_ctor_get(v_s_2259_, 11);
v_basis_2272_ = lean_ctor_get(v_s_2259_, 12);
v_diseqs_2273_ = lean_ctor_get(v_s_2259_, 13);
v_recheck_2274_ = lean_ctor_get_uint8(v_s_2259_, sizeof(void*)*17);
v_invSet_2275_ = lean_ctor_get(v_s_2259_, 14);
v_powIdentityVarCount_2276_ = lean_ctor_get(v_s_2259_, 15);
v_numEq0_x3f_2277_ = lean_ctor_get(v_s_2259_, 16);
v_numEq0Updated_2278_ = lean_ctor_get_uint8(v_s_2259_, sizeof(void*)*17 + 1);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_s_2259_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2280_ = v_s_2259_;
v_isShared_2281_ = v_isSharedCheck_2310_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_numEq0_x3f_2277_);
lean_inc(v_powIdentityVarCount_2276_);
lean_inc(v_invSet_2275_);
lean_inc(v_diseqs_2273_);
lean_inc(v_basis_2272_);
lean_inc(v_queue_2271_);
lean_inc(v_steps_2270_);
lean_inc(v_nextId_2269_);
lean_inc(v_denoteEntries_2268_);
lean_inc(v_powIdentityInst_x3f_2267_);
lean_inc(v_fieldInst_x3f_2266_);
lean_inc(v_noZeroDivInst_x3f_2265_);
lean_inc(v_commRingInst_2264_);
lean_inc(v_commSemiringInst_2263_);
lean_inc(v_semiringId_x3f_2262_);
lean_inc(v_invFn_x3f_2261_);
lean_inc(v_toRing_2260_);
lean_dec(v_s_2259_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2310_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v_id_2282_; lean_object* v_type_2283_; lean_object* v_u_2284_; lean_object* v_ringInst_2285_; lean_object* v_semiringInst_2286_; lean_object* v_charInst_x3f_2287_; lean_object* v_mulFn_x3f_2288_; lean_object* v_subFn_x3f_2289_; lean_object* v_negFn_x3f_2290_; lean_object* v_powFn_x3f_2291_; lean_object* v_intCastFn_x3f_2292_; lean_object* v_natCastFn_x3f_2293_; lean_object* v_one_x3f_2294_; lean_object* v_vars_2295_; lean_object* v_varMap_2296_; lean_object* v_denote_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2308_; 
v_id_2282_ = lean_ctor_get(v_toRing_2260_, 0);
v_type_2283_ = lean_ctor_get(v_toRing_2260_, 1);
v_u_2284_ = lean_ctor_get(v_toRing_2260_, 2);
v_ringInst_2285_ = lean_ctor_get(v_toRing_2260_, 3);
v_semiringInst_2286_ = lean_ctor_get(v_toRing_2260_, 4);
v_charInst_x3f_2287_ = lean_ctor_get(v_toRing_2260_, 5);
v_mulFn_x3f_2288_ = lean_ctor_get(v_toRing_2260_, 7);
v_subFn_x3f_2289_ = lean_ctor_get(v_toRing_2260_, 8);
v_negFn_x3f_2290_ = lean_ctor_get(v_toRing_2260_, 9);
v_powFn_x3f_2291_ = lean_ctor_get(v_toRing_2260_, 10);
v_intCastFn_x3f_2292_ = lean_ctor_get(v_toRing_2260_, 11);
v_natCastFn_x3f_2293_ = lean_ctor_get(v_toRing_2260_, 12);
v_one_x3f_2294_ = lean_ctor_get(v_toRing_2260_, 13);
v_vars_2295_ = lean_ctor_get(v_toRing_2260_, 14);
v_varMap_2296_ = lean_ctor_get(v_toRing_2260_, 15);
v_denote_2297_ = lean_ctor_get(v_toRing_2260_, 16);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_toRing_2260_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v_toRing_2260_, 6);
lean_dec(v_unused_2309_);
v___x_2299_ = v_toRing_2260_;
v_isShared_2300_ = v_isSharedCheck_2308_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_denote_2297_);
lean_inc(v_varMap_2296_);
lean_inc(v_vars_2295_);
lean_inc(v_one_x3f_2294_);
lean_inc(v_natCastFn_x3f_2293_);
lean_inc(v_intCastFn_x3f_2292_);
lean_inc(v_powFn_x3f_2291_);
lean_inc(v_negFn_x3f_2290_);
lean_inc(v_subFn_x3f_2289_);
lean_inc(v_mulFn_x3f_2288_);
lean_inc(v_charInst_x3f_2287_);
lean_inc(v_semiringInst_2286_);
lean_inc(v_ringInst_2285_);
lean_inc(v_u_2284_);
lean_inc(v_type_2283_);
lean_inc(v_id_2282_);
lean_dec(v_toRing_2260_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2308_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2301_, 0, v_a_2258_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 6, v___x_2301_);
v___x_2303_ = v___x_2299_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_id_2282_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_type_2283_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_u_2284_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v_ringInst_2285_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v_semiringInst_2286_);
lean_ctor_set(v_reuseFailAlloc_2307_, 5, v_charInst_x3f_2287_);
lean_ctor_set(v_reuseFailAlloc_2307_, 6, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2307_, 7, v_mulFn_x3f_2288_);
lean_ctor_set(v_reuseFailAlloc_2307_, 8, v_subFn_x3f_2289_);
lean_ctor_set(v_reuseFailAlloc_2307_, 9, v_negFn_x3f_2290_);
lean_ctor_set(v_reuseFailAlloc_2307_, 10, v_powFn_x3f_2291_);
lean_ctor_set(v_reuseFailAlloc_2307_, 11, v_intCastFn_x3f_2292_);
lean_ctor_set(v_reuseFailAlloc_2307_, 12, v_natCastFn_x3f_2293_);
lean_ctor_set(v_reuseFailAlloc_2307_, 13, v_one_x3f_2294_);
lean_ctor_set(v_reuseFailAlloc_2307_, 14, v_vars_2295_);
lean_ctor_set(v_reuseFailAlloc_2307_, 15, v_varMap_2296_);
lean_ctor_set(v_reuseFailAlloc_2307_, 16, v_denote_2297_);
v___x_2303_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2305_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2303_);
v___x_2305_ = v___x_2280_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_invFn_x3f_2261_);
lean_ctor_set(v_reuseFailAlloc_2306_, 2, v_semiringId_x3f_2262_);
lean_ctor_set(v_reuseFailAlloc_2306_, 3, v_commSemiringInst_2263_);
lean_ctor_set(v_reuseFailAlloc_2306_, 4, v_commRingInst_2264_);
lean_ctor_set(v_reuseFailAlloc_2306_, 5, v_noZeroDivInst_x3f_2265_);
lean_ctor_set(v_reuseFailAlloc_2306_, 6, v_fieldInst_x3f_2266_);
lean_ctor_set(v_reuseFailAlloc_2306_, 7, v_powIdentityInst_x3f_2267_);
lean_ctor_set(v_reuseFailAlloc_2306_, 8, v_denoteEntries_2268_);
lean_ctor_set(v_reuseFailAlloc_2306_, 9, v_nextId_2269_);
lean_ctor_set(v_reuseFailAlloc_2306_, 10, v_steps_2270_);
lean_ctor_set(v_reuseFailAlloc_2306_, 11, v_queue_2271_);
lean_ctor_set(v_reuseFailAlloc_2306_, 12, v_basis_2272_);
lean_ctor_set(v_reuseFailAlloc_2306_, 13, v_diseqs_2273_);
lean_ctor_set(v_reuseFailAlloc_2306_, 14, v_invSet_2275_);
lean_ctor_set(v_reuseFailAlloc_2306_, 15, v_powIdentityVarCount_2276_);
lean_ctor_set(v_reuseFailAlloc_2306_, 16, v_numEq0_x3f_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2306_, sizeof(void*)*17, v_recheck_2274_);
lean_ctor_set_uint8(v_reuseFailAlloc_2306_, sizeof(void*)*17 + 1, v_numEq0Updated_2278_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2367_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2367_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2367_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_toRing_2328_; lean_object* v_addFn_x3f_2329_; 
v_toRing_2328_ = lean_ctor_get(v_a_2324_, 0);
lean_inc_ref(v_toRing_2328_);
lean_dec(v_a_2324_);
v_addFn_x3f_2329_ = lean_ctor_get(v_toRing_2328_, 6);
if (lean_obj_tag(v_addFn_x3f_2329_) == 1)
{
lean_object* v_val_2330_; lean_object* v___x_2332_; 
lean_inc_ref(v_addFn_x3f_2329_);
lean_dec_ref(v_toRing_2328_);
v_val_2330_ = lean_ctor_get(v_addFn_x3f_2329_, 0);
lean_inc(v_val_2330_);
lean_dec_ref_known(v_addFn_x3f_2329_, 1);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v_val_2330_);
v___x_2332_ = v___x_2326_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_val_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
else
{
lean_object* v_type_2334_; lean_object* v_u_2335_; lean_object* v_semiringInst_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v_expectedInst_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_del_object(v___x_2326_);
v_type_2334_ = lean_ctor_get(v_toRing_2328_, 1);
lean_inc_ref_n(v_type_2334_, 3);
v_u_2335_ = lean_ctor_get(v_toRing_2328_, 2);
lean_inc_n(v_u_2335_, 2);
v_semiringInst_2336_ = lean_ctor_get(v_toRing_2328_, 4);
lean_inc_ref(v_semiringInst_2336_);
lean_dec_ref(v_toRing_2328_);
v___x_2337_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_2338_ = lean_box(0);
v___x_2339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2339_, 0, v_u_2335_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
lean_inc_ref(v___x_2339_);
v___x_2340_ = l_Lean_mkConst(v___x_2337_, v___x_2339_);
v___x_2341_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_2342_ = l_Lean_mkConst(v___x_2341_, v___x_2339_);
v___x_2343_ = l_Lean_mkAppB(v___x_2342_, v_type_2334_, v_semiringInst_2336_);
v_expectedInst_2344_ = l_Lean_mkAppB(v___x_2340_, v_type_2334_, v___x_2343_);
v___x_2345_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_2346_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_2347_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2334_, v_u_2335_, v___x_2345_, v___x_2346_, v_expectedInst_2344_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___f_2349_; lean_object* v___x_2350_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc_n(v_a_2348_, 2);
lean_dec_ref_known(v___x_2347_, 1);
v___f_2349_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_2349_, 0, v_a_2348_);
v___x_2350_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2349_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2357_ == 0)
{
lean_object* v_unused_2358_; 
v_unused_2358_ = lean_ctor_get(v___x_2350_, 0);
lean_dec(v_unused_2358_);
v___x_2352_ = v___x_2350_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_dec(v___x_2350_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v_a_2348_);
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2348_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec(v_a_2348_);
v_a_2359_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2350_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2350_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
v_a_2368_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2323_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2323_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec(v___y_2376_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(lean_object* v_type_2389_, lean_object* v_u_2390_, lean_object* v_instDeclName_2391_, lean_object* v_declName_2392_, lean_object* v_expectedInst_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2406_ = lean_box(0);
v___x_2407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2407_, 0, v_u_2390_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
lean_inc_ref(v___x_2407_);
v___x_2408_ = l_Lean_mkConst(v_instDeclName_2391_, v___x_2407_);
lean_inc_ref(v_type_2389_);
v___x_2409_ = l_Lean_Expr_app___override(v___x_2408_, v_type_2389_);
v___x_2410_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2409_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2412_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc_n(v_a_2411_, 2);
lean_dec_ref_known(v___x_2410_, 1);
lean_inc(v_declName_2392_);
v___x_2412_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2392_, v_a_2411_, v_expectedInst_2393_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
lean_dec_ref_known(v___x_2412_, 1);
v___x_2413_ = l_Lean_mkConst(v_declName_2392_, v___x_2407_);
v___x_2414_ = l_Lean_mkAppB(v___x_2413_, v_type_2389_, v_a_2411_);
v___x_2415_ = l_Lean_Meta_Sym_canon(v___x_2414_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2417_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v___x_2417_ = l_Lean_Meta_Sym_shareCommon(v_a_2416_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
return v___x_2417_;
}
else
{
return v___x_2415_;
}
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_dec(v_a_2411_);
lean_dec_ref_known(v___x_2407_, 2);
lean_dec(v_declName_2392_);
lean_dec_ref(v_type_2389_);
v_a_2418_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2412_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2412_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2407_, 2);
lean_dec_ref(v_expectedInst_2393_);
lean_dec(v_declName_2392_);
lean_dec_ref(v_type_2389_);
return v___x_2410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_type_2426_ = _args[0];
lean_object* v_u_2427_ = _args[1];
lean_object* v_instDeclName_2428_ = _args[2];
lean_object* v_declName_2429_ = _args[3];
lean_object* v_expectedInst_2430_ = _args[4];
lean_object* v___y_2431_ = _args[5];
lean_object* v___y_2432_ = _args[6];
lean_object* v___y_2433_ = _args[7];
lean_object* v___y_2434_ = _args[8];
lean_object* v___y_2435_ = _args[9];
lean_object* v___y_2436_ = _args[10];
lean_object* v___y_2437_ = _args[11];
lean_object* v___y_2438_ = _args[12];
lean_object* v___y_2439_ = _args[13];
lean_object* v___y_2440_ = _args[14];
lean_object* v___y_2441_ = _args[15];
lean_object* v___y_2442_ = _args[16];
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2426_, v_u_2427_, v_instDeclName_2428_, v_declName_2429_, v_expectedInst_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec(v___y_2431_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object* v_a_2444_, lean_object* v_s_2445_){
_start:
{
lean_object* v_toRing_2446_; lean_object* v_invFn_x3f_2447_; lean_object* v_semiringId_x3f_2448_; lean_object* v_commSemiringInst_2449_; lean_object* v_commRingInst_2450_; lean_object* v_noZeroDivInst_x3f_2451_; lean_object* v_fieldInst_x3f_2452_; lean_object* v_powIdentityInst_x3f_2453_; lean_object* v_denoteEntries_2454_; lean_object* v_nextId_2455_; lean_object* v_steps_2456_; lean_object* v_queue_2457_; lean_object* v_basis_2458_; lean_object* v_diseqs_2459_; uint8_t v_recheck_2460_; lean_object* v_invSet_2461_; lean_object* v_powIdentityVarCount_2462_; lean_object* v_numEq0_x3f_2463_; uint8_t v_numEq0Updated_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2496_; 
v_toRing_2446_ = lean_ctor_get(v_s_2445_, 0);
v_invFn_x3f_2447_ = lean_ctor_get(v_s_2445_, 1);
v_semiringId_x3f_2448_ = lean_ctor_get(v_s_2445_, 2);
v_commSemiringInst_2449_ = lean_ctor_get(v_s_2445_, 3);
v_commRingInst_2450_ = lean_ctor_get(v_s_2445_, 4);
v_noZeroDivInst_x3f_2451_ = lean_ctor_get(v_s_2445_, 5);
v_fieldInst_x3f_2452_ = lean_ctor_get(v_s_2445_, 6);
v_powIdentityInst_x3f_2453_ = lean_ctor_get(v_s_2445_, 7);
v_denoteEntries_2454_ = lean_ctor_get(v_s_2445_, 8);
v_nextId_2455_ = lean_ctor_get(v_s_2445_, 9);
v_steps_2456_ = lean_ctor_get(v_s_2445_, 10);
v_queue_2457_ = lean_ctor_get(v_s_2445_, 11);
v_basis_2458_ = lean_ctor_get(v_s_2445_, 12);
v_diseqs_2459_ = lean_ctor_get(v_s_2445_, 13);
v_recheck_2460_ = lean_ctor_get_uint8(v_s_2445_, sizeof(void*)*17);
v_invSet_2461_ = lean_ctor_get(v_s_2445_, 14);
v_powIdentityVarCount_2462_ = lean_ctor_get(v_s_2445_, 15);
v_numEq0_x3f_2463_ = lean_ctor_get(v_s_2445_, 16);
v_numEq0Updated_2464_ = lean_ctor_get_uint8(v_s_2445_, sizeof(void*)*17 + 1);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_s_2445_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2466_ = v_s_2445_;
v_isShared_2467_ = v_isSharedCheck_2496_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_numEq0_x3f_2463_);
lean_inc(v_powIdentityVarCount_2462_);
lean_inc(v_invSet_2461_);
lean_inc(v_diseqs_2459_);
lean_inc(v_basis_2458_);
lean_inc(v_queue_2457_);
lean_inc(v_steps_2456_);
lean_inc(v_nextId_2455_);
lean_inc(v_denoteEntries_2454_);
lean_inc(v_powIdentityInst_x3f_2453_);
lean_inc(v_fieldInst_x3f_2452_);
lean_inc(v_noZeroDivInst_x3f_2451_);
lean_inc(v_commRingInst_2450_);
lean_inc(v_commSemiringInst_2449_);
lean_inc(v_semiringId_x3f_2448_);
lean_inc(v_invFn_x3f_2447_);
lean_inc(v_toRing_2446_);
lean_dec(v_s_2445_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2496_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v_id_2468_; lean_object* v_type_2469_; lean_object* v_u_2470_; lean_object* v_ringInst_2471_; lean_object* v_semiringInst_2472_; lean_object* v_charInst_x3f_2473_; lean_object* v_addFn_x3f_2474_; lean_object* v_mulFn_x3f_2475_; lean_object* v_subFn_x3f_2476_; lean_object* v_powFn_x3f_2477_; lean_object* v_intCastFn_x3f_2478_; lean_object* v_natCastFn_x3f_2479_; lean_object* v_one_x3f_2480_; lean_object* v_vars_2481_; lean_object* v_varMap_2482_; lean_object* v_denote_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2494_; 
v_id_2468_ = lean_ctor_get(v_toRing_2446_, 0);
v_type_2469_ = lean_ctor_get(v_toRing_2446_, 1);
v_u_2470_ = lean_ctor_get(v_toRing_2446_, 2);
v_ringInst_2471_ = lean_ctor_get(v_toRing_2446_, 3);
v_semiringInst_2472_ = lean_ctor_get(v_toRing_2446_, 4);
v_charInst_x3f_2473_ = lean_ctor_get(v_toRing_2446_, 5);
v_addFn_x3f_2474_ = lean_ctor_get(v_toRing_2446_, 6);
v_mulFn_x3f_2475_ = lean_ctor_get(v_toRing_2446_, 7);
v_subFn_x3f_2476_ = lean_ctor_get(v_toRing_2446_, 8);
v_powFn_x3f_2477_ = lean_ctor_get(v_toRing_2446_, 10);
v_intCastFn_x3f_2478_ = lean_ctor_get(v_toRing_2446_, 11);
v_natCastFn_x3f_2479_ = lean_ctor_get(v_toRing_2446_, 12);
v_one_x3f_2480_ = lean_ctor_get(v_toRing_2446_, 13);
v_vars_2481_ = lean_ctor_get(v_toRing_2446_, 14);
v_varMap_2482_ = lean_ctor_get(v_toRing_2446_, 15);
v_denote_2483_ = lean_ctor_get(v_toRing_2446_, 16);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_toRing_2446_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; 
v_unused_2495_ = lean_ctor_get(v_toRing_2446_, 9);
lean_dec(v_unused_2495_);
v___x_2485_ = v_toRing_2446_;
v_isShared_2486_ = v_isSharedCheck_2494_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_denote_2483_);
lean_inc(v_varMap_2482_);
lean_inc(v_vars_2481_);
lean_inc(v_one_x3f_2480_);
lean_inc(v_natCastFn_x3f_2479_);
lean_inc(v_intCastFn_x3f_2478_);
lean_inc(v_powFn_x3f_2477_);
lean_inc(v_subFn_x3f_2476_);
lean_inc(v_mulFn_x3f_2475_);
lean_inc(v_addFn_x3f_2474_);
lean_inc(v_charInst_x3f_2473_);
lean_inc(v_semiringInst_2472_);
lean_inc(v_ringInst_2471_);
lean_inc(v_u_2470_);
lean_inc(v_type_2469_);
lean_inc(v_id_2468_);
lean_dec(v_toRing_2446_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2494_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2487_, 0, v_a_2444_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 9, v___x_2487_);
v___x_2489_ = v___x_2485_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_id_2468_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_type_2469_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_u_2470_);
lean_ctor_set(v_reuseFailAlloc_2493_, 3, v_ringInst_2471_);
lean_ctor_set(v_reuseFailAlloc_2493_, 4, v_semiringInst_2472_);
lean_ctor_set(v_reuseFailAlloc_2493_, 5, v_charInst_x3f_2473_);
lean_ctor_set(v_reuseFailAlloc_2493_, 6, v_addFn_x3f_2474_);
lean_ctor_set(v_reuseFailAlloc_2493_, 7, v_mulFn_x3f_2475_);
lean_ctor_set(v_reuseFailAlloc_2493_, 8, v_subFn_x3f_2476_);
lean_ctor_set(v_reuseFailAlloc_2493_, 9, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2493_, 10, v_powFn_x3f_2477_);
lean_ctor_set(v_reuseFailAlloc_2493_, 11, v_intCastFn_x3f_2478_);
lean_ctor_set(v_reuseFailAlloc_2493_, 12, v_natCastFn_x3f_2479_);
lean_ctor_set(v_reuseFailAlloc_2493_, 13, v_one_x3f_2480_);
lean_ctor_set(v_reuseFailAlloc_2493_, 14, v_vars_2481_);
lean_ctor_set(v_reuseFailAlloc_2493_, 15, v_varMap_2482_);
lean_ctor_set(v_reuseFailAlloc_2493_, 16, v_denote_2483_);
v___x_2489_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2491_; 
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2489_);
v___x_2491_ = v___x_2466_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_invFn_x3f_2447_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_semiringId_x3f_2448_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_commSemiringInst_2449_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_commRingInst_2450_);
lean_ctor_set(v_reuseFailAlloc_2492_, 5, v_noZeroDivInst_x3f_2451_);
lean_ctor_set(v_reuseFailAlloc_2492_, 6, v_fieldInst_x3f_2452_);
lean_ctor_set(v_reuseFailAlloc_2492_, 7, v_powIdentityInst_x3f_2453_);
lean_ctor_set(v_reuseFailAlloc_2492_, 8, v_denoteEntries_2454_);
lean_ctor_set(v_reuseFailAlloc_2492_, 9, v_nextId_2455_);
lean_ctor_set(v_reuseFailAlloc_2492_, 10, v_steps_2456_);
lean_ctor_set(v_reuseFailAlloc_2492_, 11, v_queue_2457_);
lean_ctor_set(v_reuseFailAlloc_2492_, 12, v_basis_2458_);
lean_ctor_set(v_reuseFailAlloc_2492_, 13, v_diseqs_2459_);
lean_ctor_set(v_reuseFailAlloc_2492_, 14, v_invSet_2461_);
lean_ctor_set(v_reuseFailAlloc_2492_, 15, v_powIdentityVarCount_2462_);
lean_ctor_set(v_reuseFailAlloc_2492_, 16, v_numEq0_x3f_2463_);
lean_ctor_set_uint8(v_reuseFailAlloc_2492_, sizeof(void*)*17, v_recheck_2460_);
lean_ctor_set_uint8(v_reuseFailAlloc_2492_, sizeof(void*)*17 + 1, v_numEq0Updated_2464_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2563_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2563_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2563_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v_toRing_2527_; lean_object* v_negFn_x3f_2528_; 
v_toRing_2527_ = lean_ctor_get(v_a_2523_, 0);
lean_inc_ref(v_toRing_2527_);
lean_dec(v_a_2523_);
v_negFn_x3f_2528_ = lean_ctor_get(v_toRing_2527_, 9);
if (lean_obj_tag(v_negFn_x3f_2528_) == 1)
{
lean_object* v_val_2529_; lean_object* v___x_2531_; 
lean_inc_ref(v_negFn_x3f_2528_);
lean_dec_ref(v_toRing_2527_);
v_val_2529_ = lean_ctor_get(v_negFn_x3f_2528_, 0);
lean_inc(v_val_2529_);
lean_dec_ref_known(v_negFn_x3f_2528_, 1);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v_val_2529_);
v___x_2531_ = v___x_2525_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_val_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
else
{
lean_object* v_type_2533_; lean_object* v_u_2534_; lean_object* v_ringInst_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v_expectedInst_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_del_object(v___x_2525_);
v_type_2533_ = lean_ctor_get(v_toRing_2527_, 1);
lean_inc_ref_n(v_type_2533_, 2);
v_u_2534_ = lean_ctor_get(v_toRing_2527_, 2);
lean_inc_n(v_u_2534_, 2);
v_ringInst_2535_ = lean_ctor_get(v_toRing_2527_, 3);
lean_inc_ref(v_ringInst_2535_);
lean_dec_ref(v_toRing_2527_);
v___x_2536_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1));
v___x_2537_ = lean_box(0);
v___x_2538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2538_, 0, v_u_2534_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = l_Lean_mkConst(v___x_2536_, v___x_2538_);
v_expectedInst_2540_ = l_Lean_mkAppB(v___x_2539_, v_type_2533_, v_ringInst_2535_);
v___x_2541_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3));
v___x_2542_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5));
v___x_2543_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2533_, v_u_2534_, v___x_2541_, v___x_2542_, v_expectedInst_2540_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___f_2545_; lean_object* v___x_2546_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc_n(v_a_2544_, 2);
lean_dec_ref_known(v___x_2543_, 1);
v___f_2545_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_2545_, 0, v_a_2544_);
v___x_2546_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2545_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; 
v_unused_2554_ = lean_ctor_get(v___x_2546_, 0);
lean_dec(v_unused_2554_);
v___x_2548_ = v___x_2546_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_dec(v___x_2546_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v_a_2544_);
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2544_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v_a_2544_);
v_a_2555_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2546_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2546_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
return v___x_2543_;
}
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
v_a_2564_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2522_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2522_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec(v___y_2572_);
return v_res_2584_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = lean_nat_to_int(v___x_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object* v_k_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v_toRing_2614_; lean_object* v_type_2615_; lean_object* v_u_2616_; lean_object* v_semiringInst_2617_; lean_object* v___x_2618_; lean_object* v_n_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
v_toRing_2614_ = lean_ctor_get(v_a_2613_, 0);
lean_inc_ref(v_toRing_2614_);
lean_dec(v_a_2613_);
v_type_2615_ = lean_ctor_get(v_toRing_2614_, 1);
lean_inc_ref_n(v_type_2615_, 2);
v_u_2616_ = lean_ctor_get(v_toRing_2614_, 2);
lean_inc(v_u_2616_);
v_semiringInst_2617_ = lean_ctor_get(v_toRing_2614_, 4);
lean_inc_ref(v_semiringInst_2617_);
lean_dec_ref(v_toRing_2614_);
v___x_2618_ = lean_nat_abs(v_k_2599_);
v_n_2619_ = l_Lean_mkRawNatLit(v___x_2618_);
v___x_2620_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1));
v___x_2621_ = lean_box(0);
v___x_2622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2622_, 0, v_u_2616_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
lean_inc_ref(v___x_2622_);
v___x_2623_ = l_Lean_mkConst(v___x_2620_, v___x_2622_);
lean_inc_ref(v_n_2619_);
v___x_2624_ = l_Lean_mkAppB(v___x_2623_, v_type_2615_, v_n_2619_);
v___x_2625_ = lean_box(0);
v___x_2626_ = l_Lean_Meta_synthInstance_x3f(v___x_2624_, v___x_2625_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2666_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2666_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2666_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_ofNatInst_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; 
if (lean_obj_tag(v_a_2627_) == 1)
{
lean_object* v_val_2662_; 
lean_dec_ref(v_semiringInst_2617_);
v_val_2662_ = lean_ctor_get(v_a_2627_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v_a_2627_, 1);
v_ofNatInst_2632_ = v_val_2662_;
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
v___y_2643_ = v___y_2610_;
goto v___jp_2631_;
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_dec(v_a_2627_);
v___x_2663_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5));
lean_inc_ref(v___x_2622_);
v___x_2664_ = l_Lean_mkConst(v___x_2663_, v___x_2622_);
lean_inc_ref(v_n_2619_);
lean_inc_ref(v_type_2615_);
v___x_2665_ = l_Lean_mkApp3(v___x_2664_, v_type_2615_, v_semiringInst_2617_, v_n_2619_);
v_ofNatInst_2632_ = v___x_2665_;
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
v___y_2643_ = v___y_2610_;
goto v___jp_2631_;
}
v___jp_2631_:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v_n_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2644_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3));
v___x_2645_ = l_Lean_mkConst(v___x_2644_, v___x_2622_);
v_n_2646_ = l_Lean_mkApp3(v___x_2645_, v_type_2615_, v_n_2619_, v_ofNatInst_2632_);
v___x_2647_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4);
v___x_2648_ = lean_int_dec_lt(v_k_2599_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2650_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v_n_2646_);
v___x_2650_ = v___x_2629_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_n_2646_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
else
{
lean_object* v___x_2652_; 
lean_del_object(v___x_2629_);
v___x_2652_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2661_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2661_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2661_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2657_ = l_Lean_Expr_app___override(v_a_2653_, v_n_2646_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2657_);
v___x_2659_ = v___x_2655_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
else
{
lean_dec_ref(v_n_2646_);
return v___x_2652_;
}
}
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec_ref_known(v___x_2622_, 2);
lean_dec_ref(v_n_2619_);
lean_dec_ref(v_semiringInst_2617_);
lean_dec_ref(v_type_2615_);
v_a_2667_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2626_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2626_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
v_a_2675_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2612_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2612_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object* v_k_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec(v_k_2683_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object* v_a_2697_, lean_object* v_s_2698_){
_start:
{
lean_object* v_toRing_2699_; lean_object* v_invFn_x3f_2700_; lean_object* v_semiringId_x3f_2701_; lean_object* v_commSemiringInst_2702_; lean_object* v_commRingInst_2703_; lean_object* v_noZeroDivInst_x3f_2704_; lean_object* v_fieldInst_x3f_2705_; lean_object* v_powIdentityInst_x3f_2706_; lean_object* v_denoteEntries_2707_; lean_object* v_nextId_2708_; lean_object* v_steps_2709_; lean_object* v_queue_2710_; lean_object* v_basis_2711_; lean_object* v_diseqs_2712_; uint8_t v_recheck_2713_; lean_object* v_invSet_2714_; lean_object* v_powIdentityVarCount_2715_; lean_object* v_numEq0_x3f_2716_; uint8_t v_numEq0Updated_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2749_; 
v_toRing_2699_ = lean_ctor_get(v_s_2698_, 0);
v_invFn_x3f_2700_ = lean_ctor_get(v_s_2698_, 1);
v_semiringId_x3f_2701_ = lean_ctor_get(v_s_2698_, 2);
v_commSemiringInst_2702_ = lean_ctor_get(v_s_2698_, 3);
v_commRingInst_2703_ = lean_ctor_get(v_s_2698_, 4);
v_noZeroDivInst_x3f_2704_ = lean_ctor_get(v_s_2698_, 5);
v_fieldInst_x3f_2705_ = lean_ctor_get(v_s_2698_, 6);
v_powIdentityInst_x3f_2706_ = lean_ctor_get(v_s_2698_, 7);
v_denoteEntries_2707_ = lean_ctor_get(v_s_2698_, 8);
v_nextId_2708_ = lean_ctor_get(v_s_2698_, 9);
v_steps_2709_ = lean_ctor_get(v_s_2698_, 10);
v_queue_2710_ = lean_ctor_get(v_s_2698_, 11);
v_basis_2711_ = lean_ctor_get(v_s_2698_, 12);
v_diseqs_2712_ = lean_ctor_get(v_s_2698_, 13);
v_recheck_2713_ = lean_ctor_get_uint8(v_s_2698_, sizeof(void*)*17);
v_invSet_2714_ = lean_ctor_get(v_s_2698_, 14);
v_powIdentityVarCount_2715_ = lean_ctor_get(v_s_2698_, 15);
v_numEq0_x3f_2716_ = lean_ctor_get(v_s_2698_, 16);
v_numEq0Updated_2717_ = lean_ctor_get_uint8(v_s_2698_, sizeof(void*)*17 + 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_s_2698_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2719_ = v_s_2698_;
v_isShared_2720_ = v_isSharedCheck_2749_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_numEq0_x3f_2716_);
lean_inc(v_powIdentityVarCount_2715_);
lean_inc(v_invSet_2714_);
lean_inc(v_diseqs_2712_);
lean_inc(v_basis_2711_);
lean_inc(v_queue_2710_);
lean_inc(v_steps_2709_);
lean_inc(v_nextId_2708_);
lean_inc(v_denoteEntries_2707_);
lean_inc(v_powIdentityInst_x3f_2706_);
lean_inc(v_fieldInst_x3f_2705_);
lean_inc(v_noZeroDivInst_x3f_2704_);
lean_inc(v_commRingInst_2703_);
lean_inc(v_commSemiringInst_2702_);
lean_inc(v_semiringId_x3f_2701_);
lean_inc(v_invFn_x3f_2700_);
lean_inc(v_toRing_2699_);
lean_dec(v_s_2698_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2749_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v_id_2721_; lean_object* v_type_2722_; lean_object* v_u_2723_; lean_object* v_ringInst_2724_; lean_object* v_semiringInst_2725_; lean_object* v_charInst_x3f_2726_; lean_object* v_addFn_x3f_2727_; lean_object* v_mulFn_x3f_2728_; lean_object* v_subFn_x3f_2729_; lean_object* v_negFn_x3f_2730_; lean_object* v_intCastFn_x3f_2731_; lean_object* v_natCastFn_x3f_2732_; lean_object* v_one_x3f_2733_; lean_object* v_vars_2734_; lean_object* v_varMap_2735_; lean_object* v_denote_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2747_; 
v_id_2721_ = lean_ctor_get(v_toRing_2699_, 0);
v_type_2722_ = lean_ctor_get(v_toRing_2699_, 1);
v_u_2723_ = lean_ctor_get(v_toRing_2699_, 2);
v_ringInst_2724_ = lean_ctor_get(v_toRing_2699_, 3);
v_semiringInst_2725_ = lean_ctor_get(v_toRing_2699_, 4);
v_charInst_x3f_2726_ = lean_ctor_get(v_toRing_2699_, 5);
v_addFn_x3f_2727_ = lean_ctor_get(v_toRing_2699_, 6);
v_mulFn_x3f_2728_ = lean_ctor_get(v_toRing_2699_, 7);
v_subFn_x3f_2729_ = lean_ctor_get(v_toRing_2699_, 8);
v_negFn_x3f_2730_ = lean_ctor_get(v_toRing_2699_, 9);
v_intCastFn_x3f_2731_ = lean_ctor_get(v_toRing_2699_, 11);
v_natCastFn_x3f_2732_ = lean_ctor_get(v_toRing_2699_, 12);
v_one_x3f_2733_ = lean_ctor_get(v_toRing_2699_, 13);
v_vars_2734_ = lean_ctor_get(v_toRing_2699_, 14);
v_varMap_2735_ = lean_ctor_get(v_toRing_2699_, 15);
v_denote_2736_ = lean_ctor_get(v_toRing_2699_, 16);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_toRing_2699_);
if (v_isSharedCheck_2747_ == 0)
{
lean_object* v_unused_2748_; 
v_unused_2748_ = lean_ctor_get(v_toRing_2699_, 10);
lean_dec(v_unused_2748_);
v___x_2738_ = v_toRing_2699_;
v_isShared_2739_ = v_isSharedCheck_2747_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_denote_2736_);
lean_inc(v_varMap_2735_);
lean_inc(v_vars_2734_);
lean_inc(v_one_x3f_2733_);
lean_inc(v_natCastFn_x3f_2732_);
lean_inc(v_intCastFn_x3f_2731_);
lean_inc(v_negFn_x3f_2730_);
lean_inc(v_subFn_x3f_2729_);
lean_inc(v_mulFn_x3f_2728_);
lean_inc(v_addFn_x3f_2727_);
lean_inc(v_charInst_x3f_2726_);
lean_inc(v_semiringInst_2725_);
lean_inc(v_ringInst_2724_);
lean_inc(v_u_2723_);
lean_inc(v_type_2722_);
lean_inc(v_id_2721_);
lean_dec(v_toRing_2699_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2747_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2740_, 0, v_a_2697_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 10, v___x_2740_);
v___x_2742_ = v___x_2738_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_id_2721_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v_type_2722_);
lean_ctor_set(v_reuseFailAlloc_2746_, 2, v_u_2723_);
lean_ctor_set(v_reuseFailAlloc_2746_, 3, v_ringInst_2724_);
lean_ctor_set(v_reuseFailAlloc_2746_, 4, v_semiringInst_2725_);
lean_ctor_set(v_reuseFailAlloc_2746_, 5, v_charInst_x3f_2726_);
lean_ctor_set(v_reuseFailAlloc_2746_, 6, v_addFn_x3f_2727_);
lean_ctor_set(v_reuseFailAlloc_2746_, 7, v_mulFn_x3f_2728_);
lean_ctor_set(v_reuseFailAlloc_2746_, 8, v_subFn_x3f_2729_);
lean_ctor_set(v_reuseFailAlloc_2746_, 9, v_negFn_x3f_2730_);
lean_ctor_set(v_reuseFailAlloc_2746_, 10, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2746_, 11, v_intCastFn_x3f_2731_);
lean_ctor_set(v_reuseFailAlloc_2746_, 12, v_natCastFn_x3f_2732_);
lean_ctor_set(v_reuseFailAlloc_2746_, 13, v_one_x3f_2733_);
lean_ctor_set(v_reuseFailAlloc_2746_, 14, v_vars_2734_);
lean_ctor_set(v_reuseFailAlloc_2746_, 15, v_varMap_2735_);
lean_ctor_set(v_reuseFailAlloc_2746_, 16, v_denote_2736_);
v___x_2742_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2744_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2742_);
v___x_2744_ = v___x_2719_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2742_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_invFn_x3f_2700_);
lean_ctor_set(v_reuseFailAlloc_2745_, 2, v_semiringId_x3f_2701_);
lean_ctor_set(v_reuseFailAlloc_2745_, 3, v_commSemiringInst_2702_);
lean_ctor_set(v_reuseFailAlloc_2745_, 4, v_commRingInst_2703_);
lean_ctor_set(v_reuseFailAlloc_2745_, 5, v_noZeroDivInst_x3f_2704_);
lean_ctor_set(v_reuseFailAlloc_2745_, 6, v_fieldInst_x3f_2705_);
lean_ctor_set(v_reuseFailAlloc_2745_, 7, v_powIdentityInst_x3f_2706_);
lean_ctor_set(v_reuseFailAlloc_2745_, 8, v_denoteEntries_2707_);
lean_ctor_set(v_reuseFailAlloc_2745_, 9, v_nextId_2708_);
lean_ctor_set(v_reuseFailAlloc_2745_, 10, v_steps_2709_);
lean_ctor_set(v_reuseFailAlloc_2745_, 11, v_queue_2710_);
lean_ctor_set(v_reuseFailAlloc_2745_, 12, v_basis_2711_);
lean_ctor_set(v_reuseFailAlloc_2745_, 13, v_diseqs_2712_);
lean_ctor_set(v_reuseFailAlloc_2745_, 14, v_invSet_2714_);
lean_ctor_set(v_reuseFailAlloc_2745_, 15, v_powIdentityVarCount_2715_);
lean_ctor_set(v_reuseFailAlloc_2745_, 16, v_numEq0_x3f_2716_);
lean_ctor_set_uint8(v_reuseFailAlloc_2745_, sizeof(void*)*17, v_recheck_2713_);
lean_ctor_set_uint8(v_reuseFailAlloc_2745_, sizeof(void*)*17 + 1, v_numEq0Updated_2717_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = lean_unsigned_to_nat(0u);
v___x_2754_ = l_Lean_Level_ofNat(v___x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(lean_object* v_u_2765_, lean_object* v_type_2766_, lean_object* v_semiringInst_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2780_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1));
v___x_2781_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2);
v___x_2782_ = lean_box(0);
lean_inc(v_u_2765_);
v___x_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2783_, 0, v_u_2765_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
lean_inc_ref(v___x_2783_);
v___x_2784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2781_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
v___x_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2785_, 0, v_u_2765_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
lean_inc_ref(v___x_2785_);
v___x_2786_ = l_Lean_mkConst(v___x_2780_, v___x_2785_);
v___x_2787_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2766_, 2);
v___x_2788_ = l_Lean_mkApp3(v___x_2786_, v_type_2766_, v___x_2787_, v_type_2766_);
v___x_2789_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2788_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v_inst_x27_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc_n(v_a_2790_, 2);
lean_dec_ref_known(v___x_2789_, 1);
v___x_2791_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4));
v___x_2792_ = l_Lean_mkConst(v___x_2791_, v___x_2783_);
lean_inc_ref(v_type_2766_);
v_inst_x27_2793_ = l_Lean_mkAppB(v___x_2792_, v_type_2766_, v_semiringInst_2767_);
v___x_2794_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6));
v___x_2795_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_2794_, v_a_2790_, v_inst_x27_2793_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
lean_dec_ref_known(v___x_2795_, 1);
v___x_2796_ = l_Lean_mkConst(v___x_2794_, v___x_2785_);
lean_inc_ref(v_type_2766_);
v___x_2797_ = l_Lean_mkApp4(v___x_2796_, v_type_2766_, v___x_2787_, v_type_2766_, v_a_2790_);
v___x_2798_ = l_Lean_Meta_Sym_canon(v___x_2797_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2800_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref_known(v___x_2798_, 1);
v___x_2800_ = l_Lean_Meta_Sym_shareCommon(v_a_2799_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
return v___x_2800_;
}
else
{
return v___x_2798_;
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2790_);
lean_dec_ref_known(v___x_2785_, 2);
lean_dec_ref(v_type_2766_);
v_a_2801_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2795_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2795_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2785_, 2);
lean_dec_ref_known(v___x_2783_, 2);
lean_dec_ref(v_semiringInst_2767_);
lean_dec_ref(v_type_2766_);
return v___x_2789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___boxed(lean_object* v_u_2809_, lean_object* v_type_2810_, lean_object* v_semiringInst_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2809_, v_type_2810_, v_semiringInst_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec(v___y_2812_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2871_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2871_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2871_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v_toRing_2842_; lean_object* v_powFn_x3f_2843_; 
v_toRing_2842_ = lean_ctor_get(v_a_2838_, 0);
lean_inc_ref(v_toRing_2842_);
lean_dec(v_a_2838_);
v_powFn_x3f_2843_ = lean_ctor_get(v_toRing_2842_, 10);
if (lean_obj_tag(v_powFn_x3f_2843_) == 1)
{
lean_object* v_val_2844_; lean_object* v___x_2846_; 
lean_inc_ref(v_powFn_x3f_2843_);
lean_dec_ref(v_toRing_2842_);
v_val_2844_ = lean_ctor_get(v_powFn_x3f_2843_, 0);
lean_inc(v_val_2844_);
lean_dec_ref_known(v_powFn_x3f_2843_, 1);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v_val_2844_);
v___x_2846_ = v___x_2840_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_val_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
else
{
lean_object* v_type_2848_; lean_object* v_u_2849_; lean_object* v_semiringInst_2850_; lean_object* v___x_2851_; 
lean_del_object(v___x_2840_);
v_type_2848_ = lean_ctor_get(v_toRing_2842_, 1);
lean_inc_ref(v_type_2848_);
v_u_2849_ = lean_ctor_get(v_toRing_2842_, 2);
lean_inc(v_u_2849_);
v_semiringInst_2850_ = lean_ctor_get(v_toRing_2842_, 4);
lean_inc_ref(v_semiringInst_2850_);
lean_dec_ref(v_toRing_2842_);
v___x_2851_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2849_, v_type_2848_, v_semiringInst_2850_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___f_2853_; lean_object* v___x_2854_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc_n(v_a_2852_, 2);
lean_dec_ref_known(v___x_2851_, 1);
v___f_2853_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_2853_, 0, v_a_2852_);
v___x_2854_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2853_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2861_ == 0)
{
lean_object* v_unused_2862_; 
v_unused_2862_ = lean_ctor_get(v___x_2854_, 0);
lean_dec(v_unused_2862_);
v___x_2856_ = v___x_2854_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_dec(v___x_2854_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v_a_2852_);
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2852_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v_a_2852_);
v_a_2863_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2854_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2854_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
return v___x_2851_;
}
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
v_a_2872_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2837_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2837_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec(v___y_2880_);
return v_res_2892_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2896_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2));
v___x_2897_ = lean_unsigned_to_nat(39u);
v___x_2898_ = lean_unsigned_to_nat(159u);
v___x_2899_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1));
v___x_2900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0));
v___x_2901_ = l_mkPanicMessageWithDecl(v___x_2900_, v___x_2899_, v___x_2898_, v___x_2897_, v___x_2896_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
switch(lean_obj_tag(v_a_2902_))
{
case 0:
{
lean_object* v_k_2915_; lean_object* v___x_2916_; 
v_k_2915_ = lean_ctor_get(v_a_2902_, 0);
lean_inc(v_k_2915_);
lean_dec_ref_known(v_a_2902_, 1);
v___x_2916_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2915_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
lean_dec(v_k_2915_);
return v___x_2916_;
}
case 1:
{
lean_object* v_k_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_k_2917_ = lean_ctor_get(v_a_2902_, 0);
lean_inc(v_k_2917_);
lean_dec_ref_known(v_a_2902_, 1);
v___x_2918_ = lean_nat_to_int(v_k_2917_);
v___x_2919_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_2918_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
lean_dec(v___x_2918_);
return v___x_2919_;
}
case 3:
{
lean_object* v_i_2920_; lean_object* v___x_2921_; 
v_i_2920_ = lean_ctor_get(v_a_2902_, 0);
lean_inc(v_i_2920_);
lean_dec_ref_known(v_a_2902_, 1);
v___x_2921_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2923_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___x_2921_, 1);
v___x_2923_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2941_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2941_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2941_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___y_2929_; lean_object* v_toSemiring_2934_; lean_object* v_vars_2935_; lean_object* v_size_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v_toSemiring_2934_ = lean_ctor_get(v_a_2924_, 0);
lean_inc_ref(v_toSemiring_2934_);
lean_dec(v_a_2924_);
v_vars_2935_ = lean_ctor_get(v_toSemiring_2934_, 9);
lean_inc_ref(v_vars_2935_);
lean_dec_ref(v_toSemiring_2934_);
v_size_2936_ = lean_ctor_get(v_vars_2935_, 2);
v___x_2937_ = l_Lean_instInhabitedExpr;
v___x_2938_ = lean_nat_dec_lt(v_i_2920_, v_size_2936_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; 
lean_dec_ref(v_vars_2935_);
lean_dec(v_i_2920_);
v___x_2939_ = l_outOfBounds___redArg(v___x_2937_);
v___y_2929_ = v___x_2939_;
goto v___jp_2928_;
}
else
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2937_, v_vars_2935_, v_i_2920_);
lean_dec(v_i_2920_);
lean_dec_ref(v_vars_2935_);
v___y_2929_ = v___x_2940_;
goto v___jp_2928_;
}
v___jp_2928_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2930_ = l_Lean_Expr_app___override(v_a_2922_, v___y_2929_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2930_);
v___x_2932_ = v___x_2926_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2930_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec(v_a_2922_);
lean_dec(v_i_2920_);
v_a_2942_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2923_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2923_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
else
{
lean_dec(v_i_2920_);
return v___x_2921_;
}
}
case 5:
{
lean_object* v_a_2950_; lean_object* v_b_2951_; lean_object* v___x_2952_; 
v_a_2950_ = lean_ctor_get(v_a_2902_, 0);
lean_inc_ref(v_a_2950_);
v_b_2951_ = lean_ctor_get(v_a_2902_, 1);
lean_inc_ref(v_b_2951_);
lean_dec_ref_known(v_a_2902_, 2);
v___x_2952_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2954_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v___x_2954_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2950_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2956_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2954_, 1);
v___x_2956_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2951_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2965_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2965_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2965_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2961_ = l_Lean_mkAppB(v_a_2953_, v_a_2955_, v_a_2957_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 0, v___x_2961_);
v___x_2963_ = v___x_2959_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
else
{
lean_dec(v_a_2955_);
lean_dec(v_a_2953_);
return v___x_2956_;
}
}
else
{
lean_dec(v_a_2953_);
lean_dec_ref(v_b_2951_);
return v___x_2954_;
}
}
else
{
lean_dec_ref(v_b_2951_);
lean_dec_ref(v_a_2950_);
return v___x_2952_;
}
}
case 7:
{
lean_object* v_a_2966_; lean_object* v_b_2967_; lean_object* v___x_2968_; 
v_a_2966_ = lean_ctor_get(v_a_2902_, 0);
lean_inc_ref(v_a_2966_);
v_b_2967_ = lean_ctor_get(v_a_2902_, 1);
lean_inc_ref(v_b_2967_);
lean_dec_ref_known(v_a_2902_, 2);
v___x_2968_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2970_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 1);
v___x_2970_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2966_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___x_2972_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref_known(v___x_2970_, 1);
v___x_2972_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2967_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2981_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_2981_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2981_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2979_; 
v___x_2977_ = l_Lean_mkAppB(v_a_2969_, v_a_2971_, v_a_2973_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_2977_);
v___x_2979_ = v___x_2975_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
else
{
lean_dec(v_a_2971_);
lean_dec(v_a_2969_);
return v___x_2972_;
}
}
else
{
lean_dec(v_a_2969_);
lean_dec_ref(v_b_2967_);
return v___x_2970_;
}
}
else
{
lean_dec_ref(v_b_2967_);
lean_dec_ref(v_a_2966_);
return v___x_2968_;
}
}
case 8:
{
lean_object* v_a_2982_; lean_object* v_k_2983_; lean_object* v___x_2984_; 
v_a_2982_ = lean_ctor_get(v_a_2902_, 0);
lean_inc_ref(v_a_2982_);
v_k_2983_ = lean_ctor_get(v_a_2902_, 1);
lean_inc(v_k_2983_);
lean_dec_ref_known(v_a_2902_, 2);
v___x_2984_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2986_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref_known(v___x_2984_, 1);
v___x_2986_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2982_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2996_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2989_ = v___x_2986_;
v_isShared_2990_ = v_isSharedCheck_2996_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2996_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2991_ = l_Lean_mkNatLit(v_k_2983_);
v___x_2992_ = l_Lean_mkAppB(v_a_2985_, v_a_2987_, v___x_2991_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2992_);
v___x_2994_ = v___x_2989_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
else
{
lean_dec(v_a_2985_);
lean_dec(v_k_2983_);
return v___x_2986_;
}
}
else
{
lean_dec(v_k_2983_);
lean_dec_ref(v_a_2982_);
return v___x_2984_;
}
}
default: 
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec_ref(v_a_2902_);
v___x_2997_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
v___x_2998_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___x_2997_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
return v___x_2998_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec(v_a_3001_);
lean_dec(v_a_3000_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(lean_object* v_type_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_3013_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(lean_object* v_type_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(v_type_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec(v___y_3028_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object* v_e_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_e_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3056_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3055_);
lean_dec_ref_known(v___x_3054_, 1);
v___x_3056_ = l_Lean_Meta_Sym_shareCommon(v_a_3055_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
return v___x_3056_;
}
else
{
return v___x_3054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object* v_e_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(v_e_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec(v_a_3058_);
return v_res_3070_;
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
