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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
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
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
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
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v_k_x27_1216_; uint8_t v___x_1217_; 
v_k_x27_1216_ = lean_array_fget_borrowed(v_keys_1209_, v_i_1211_);
v___x_1217_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_1212_, v_k_x27_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_unsigned_to_nat(1u);
v___x_1219_ = lean_nat_add(v_i_1211_, v___x_1218_);
lean_dec(v_i_1211_);
v_i_1211_ = v___x_1219_;
goto _start;
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_array_fget_borrowed(v_vals_1210_, v_i_1211_);
lean_dec(v_i_1211_);
lean_inc(v___x_1221_);
v___x_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1223_, lean_object* v_vals_1224_, lean_object* v_i_1225_, lean_object* v_k_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1223_, v_vals_1224_, v_i_1225_, v_k_1226_);
lean_dec_ref(v_k_1226_);
lean_dec_ref(v_vals_1224_);
lean_dec_ref(v_keys_1223_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_1228_, size_t v_x_1229_, lean_object* v_x_1230_){
_start:
{
if (lean_obj_tag(v_x_1228_) == 0)
{
lean_object* v_es_1231_; lean_object* v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; lean_object* v_j_1235_; lean_object* v___x_1236_; 
v_es_1231_ = lean_ctor_get(v_x_1228_, 0);
v___x_1232_ = lean_box(2);
v___x_1233_ = ((size_t)31ULL);
v___x_1234_ = lean_usize_land(v_x_1229_, v___x_1233_);
v_j_1235_ = lean_usize_to_nat(v___x_1234_);
v___x_1236_ = lean_array_get_borrowed(v___x_1232_, v_es_1231_, v_j_1235_);
lean_dec(v_j_1235_);
switch(lean_obj_tag(v___x_1236_))
{
case 0:
{
lean_object* v_key_1237_; lean_object* v_val_1238_; uint8_t v___x_1239_; 
v_key_1237_ = lean_ctor_get(v___x_1236_, 0);
v_val_1238_ = lean_ctor_get(v___x_1236_, 1);
v___x_1239_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1230_, v_key_1237_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_box(0);
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; 
lean_inc(v_val_1238_);
v___x_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_val_1238_);
return v___x_1241_;
}
}
case 1:
{
lean_object* v_node_1242_; size_t v___x_1243_; size_t v___x_1244_; 
v_node_1242_ = lean_ctor_get(v___x_1236_, 0);
v___x_1243_ = ((size_t)5ULL);
v___x_1244_ = lean_usize_shift_right(v_x_1229_, v___x_1243_);
v_x_1228_ = v_node_1242_;
v_x_1229_ = v___x_1244_;
goto _start;
}
default: 
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_box(0);
return v___x_1246_;
}
}
}
else
{
lean_object* v_ks_1247_; lean_object* v_vs_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_ks_1247_ = lean_ctor_get(v_x_1228_, 0);
v_vs_1248_ = lean_ctor_get(v_x_1228_, 1);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1247_, v_vs_1248_, v___x_1249_, v_x_1230_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
size_t v_x_866__boxed_1254_; lean_object* v_res_1255_; 
v_x_866__boxed_1254_ = lean_unbox_usize(v_x_1252_);
lean_dec(v_x_1252_);
v_res_1255_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1251_, v_x_866__boxed_1254_, v_x_1253_);
lean_dec_ref(v_x_1253_);
lean_dec_ref(v_x_1251_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
uint64_t v___x_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1257_);
v___x_1259_ = lean_uint64_to_usize(v___x_1258_);
v___x_1260_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1256_, v___x_1259_, v_x_1257_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_1261_, v_x_1262_);
lean_dec_ref(v_x_1262_);
lean_dec_ref(v_x_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(lean_object* v_e_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1265_, v_a_1266_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1278_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1278_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1278_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v_exprToSemiringId_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v_exprToSemiringId_1273_ = lean_ctor_get(v_a_1269_, 5);
lean_inc_ref(v_exprToSemiringId_1273_);
lean_dec(v_a_1269_);
v___x_1274_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_exprToSemiringId_1273_, v_e_1264_);
lean_dec_ref(v_exprToSemiringId_1273_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1274_);
v___x_1276_ = v___x_1271_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
v_a_1279_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1268_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1268_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(lean_object* v_e_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1287_, v_a_1288_, v_a_1289_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_e_1287_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(lean_object* v_e_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1292_, v_a_1293_, v_a_1301_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(lean_object* v_e_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(v_e_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_e_1305_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(lean_object* v_00_u03b2_1318_, lean_object* v_x_1319_, lean_object* v_x_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_1319_, v_x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1322_, lean_object* v_x_1323_, lean_object* v_x_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(v_00_u03b2_1322_, v_x_1323_, v_x_1324_);
lean_dec_ref(v_x_1324_);
lean_dec_ref(v_x_1323_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1326_, lean_object* v_x_1327_, size_t v_x_1328_, lean_object* v_x_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1327_, v_x_1328_, v_x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_){
_start:
{
size_t v_x_977__boxed_1335_; lean_object* v_res_1336_; 
v_x_977__boxed_1335_ = lean_unbox_usize(v_x_1333_);
lean_dec(v_x_1333_);
v_res_1336_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(v_00_u03b2_1331_, v_x_1332_, v_x_977__boxed_1335_, v_x_1334_);
lean_dec_ref(v_x_1334_);
lean_dec_ref(v_x_1332_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1337_, lean_object* v_keys_1338_, lean_object* v_vals_1339_, lean_object* v_heq_1340_, lean_object* v_i_1341_, lean_object* v_k_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1338_, v_vals_1339_, v_i_1341_, v_k_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1344_, lean_object* v_keys_1345_, lean_object* v_vals_1346_, lean_object* v_heq_1347_, lean_object* v_i_1348_, lean_object* v_k_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1344_, v_keys_1345_, v_vals_1346_, v_heq_1347_, v_i_1348_, v_k_1349_);
lean_dec_ref(v_k_1349_);
lean_dec_ref(v_vals_1346_);
lean_dec_ref(v_keys_1345_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1351_, lean_object* v_x_1352_, lean_object* v_x_1353_, lean_object* v_x_1354_){
_start:
{
lean_object* v_ks_1355_; lean_object* v_vs_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1380_; 
v_ks_1355_ = lean_ctor_get(v_x_1351_, 0);
v_vs_1356_ = lean_ctor_get(v_x_1351_, 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_x_1351_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1358_ = v_x_1351_;
v_isShared_1359_ = v_isSharedCheck_1380_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_vs_1356_);
lean_inc(v_ks_1355_);
lean_dec(v_x_1351_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1380_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = lean_array_get_size(v_ks_1355_);
v___x_1361_ = lean_nat_dec_lt(v_x_1352_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
lean_dec(v_x_1352_);
v___x_1362_ = lean_array_push(v_ks_1355_, v_x_1353_);
v___x_1363_ = lean_array_push(v_vs_1356_, v_x_1354_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___x_1363_);
lean_ctor_set(v___x_1358_, 0, v___x_1362_);
v___x_1365_ = v___x_1358_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
else
{
lean_object* v_k_x27_1367_; uint8_t v___x_1368_; 
v_k_x27_1367_ = lean_array_fget_borrowed(v_ks_1355_, v_x_1352_);
v___x_1368_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1353_, v_k_x27_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1370_; 
if (v_isShared_1359_ == 0)
{
v___x_1370_ = v___x_1358_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_ks_1355_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_vs_1356_);
v___x_1370_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v_x_1352_, v___x_1371_);
lean_dec(v_x_1352_);
v_x_1351_ = v___x_1370_;
v_x_1352_ = v___x_1372_;
goto _start;
}
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1375_ = lean_array_fset(v_ks_1355_, v_x_1352_, v_x_1353_);
v___x_1376_ = lean_array_fset(v_vs_1356_, v_x_1352_, v_x_1354_);
lean_dec(v_x_1352_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___x_1376_);
lean_ctor_set(v___x_1358_, 0, v___x_1375_);
v___x_1378_ = v___x_1358_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1381_, lean_object* v_k_1382_, lean_object* v_v_1383_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1381_, v___x_1384_, v_k_1382_, v_v_1383_);
return v___x_1385_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(lean_object* v_x_1387_, size_t v_x_1388_, size_t v_x_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
if (lean_obj_tag(v_x_1387_) == 0)
{
lean_object* v_es_1392_; size_t v___x_1393_; size_t v___x_1394_; lean_object* v_j_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v_es_1392_ = lean_ctor_get(v_x_1387_, 0);
v___x_1393_ = ((size_t)31ULL);
v___x_1394_ = lean_usize_land(v_x_1388_, v___x_1393_);
v_j_1395_ = lean_usize_to_nat(v___x_1394_);
v___x_1396_ = lean_array_get_size(v_es_1392_);
v___x_1397_ = lean_nat_dec_lt(v_j_1395_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_dec(v_j_1395_);
lean_dec(v_x_1391_);
lean_dec_ref(v_x_1390_);
return v_x_1387_;
}
else
{
lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1436_; 
lean_inc_ref(v_es_1392_);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_x_1387_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v_x_1387_, 0);
lean_dec(v_unused_1437_);
v___x_1399_ = v_x_1387_;
v_isShared_1400_ = v_isSharedCheck_1436_;
goto v_resetjp_1398_;
}
else
{
lean_dec(v_x_1387_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1436_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_v_1401_; lean_object* v___x_1402_; lean_object* v_xs_x27_1403_; lean_object* v___y_1405_; 
v_v_1401_ = lean_array_fget(v_es_1392_, v_j_1395_);
v___x_1402_ = lean_box(0);
v_xs_x27_1403_ = lean_array_fset(v_es_1392_, v_j_1395_, v___x_1402_);
switch(lean_obj_tag(v_v_1401_))
{
case 0:
{
lean_object* v_key_1410_; lean_object* v_val_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1421_; 
v_key_1410_ = lean_ctor_get(v_v_1401_, 0);
v_val_1411_ = lean_ctor_get(v_v_1401_, 1);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_v_1401_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1413_ = v_v_1401_;
v_isShared_1414_ = v_isSharedCheck_1421_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_val_1411_);
lean_inc(v_key_1410_);
lean_dec(v_v_1401_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1421_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
uint8_t v___x_1415_; 
v___x_1415_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1390_, v_key_1410_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_del_object(v___x_1413_);
v___x_1416_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1410_, v_val_1411_, v_x_1390_, v_x_1391_);
v___x_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
v___y_1405_ = v___x_1417_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1419_; 
lean_dec(v_val_1411_);
lean_dec(v_key_1410_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v_x_1391_);
lean_ctor_set(v___x_1413_, 0, v_x_1390_);
v___x_1419_ = v___x_1413_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_x_1390_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_x_1391_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
v___y_1405_ = v___x_1419_;
goto v___jp_1404_;
}
}
}
}
case 1:
{
lean_object* v_node_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1434_; 
v_node_1422_ = lean_ctor_get(v_v_1401_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_v_1401_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1424_ = v_v_1401_;
v_isShared_1425_ = v_isSharedCheck_1434_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_node_1422_);
lean_dec(v_v_1401_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1434_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
size_t v___x_1426_; size_t v___x_1427_; size_t v___x_1428_; size_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1426_ = ((size_t)5ULL);
v___x_1427_ = lean_usize_shift_right(v_x_1388_, v___x_1426_);
v___x_1428_ = ((size_t)1ULL);
v___x_1429_ = lean_usize_add(v_x_1389_, v___x_1428_);
v___x_1430_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_node_1422_, v___x_1427_, v___x_1429_, v_x_1390_, v_x_1391_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1430_);
v___x_1432_ = v___x_1424_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
v___y_1405_ = v___x_1432_;
goto v___jp_1404_;
}
}
}
default: 
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_x_1390_);
lean_ctor_set(v___x_1435_, 1, v_x_1391_);
v___y_1405_ = v___x_1435_;
goto v___jp_1404_;
}
}
v___jp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = lean_array_fset(v_xs_x27_1403_, v_j_1395_, v___y_1405_);
lean_dec(v_j_1395_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1406_);
v___x_1408_ = v___x_1399_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
else
{
lean_object* v_ks_1438_; lean_object* v_vs_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1459_; 
v_ks_1438_ = lean_ctor_get(v_x_1387_, 0);
v_vs_1439_ = lean_ctor_get(v_x_1387_, 1);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_x_1387_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1441_ = v_x_1387_;
v_isShared_1442_ = v_isSharedCheck_1459_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_vs_1439_);
lean_inc(v_ks_1438_);
lean_dec(v_x_1387_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1459_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_ks_1438_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_vs_1439_);
v___x_1444_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v_newNode_1445_; uint8_t v___y_1447_; size_t v___x_1453_; uint8_t v___x_1454_; 
v_newNode_1445_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v___x_1444_, v_x_1390_, v_x_1391_);
v___x_1453_ = ((size_t)7ULL);
v___x_1454_ = lean_usize_dec_le(v___x_1453_, v_x_1389_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1455_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1445_);
v___x_1456_ = lean_unsigned_to_nat(4u);
v___x_1457_ = lean_nat_dec_lt(v___x_1455_, v___x_1456_);
lean_dec(v___x_1455_);
v___y_1447_ = v___x_1457_;
goto v___jp_1446_;
}
else
{
v___y_1447_ = v___x_1454_;
goto v___jp_1446_;
}
v___jp_1446_:
{
if (v___y_1447_ == 0)
{
lean_object* v_ks_1448_; lean_object* v_vs_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_ks_1448_ = lean_ctor_get(v_newNode_1445_, 0);
lean_inc_ref(v_ks_1448_);
v_vs_1449_ = lean_ctor_get(v_newNode_1445_, 1);
lean_inc_ref(v_vs_1449_);
lean_dec_ref(v_newNode_1445_);
v___x_1450_ = lean_unsigned_to_nat(0u);
v___x_1451_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_1452_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_x_1389_, v_ks_1448_, v_vs_1449_, v___x_1450_, v___x_1451_);
lean_dec_ref(v_vs_1449_);
lean_dec_ref(v_ks_1448_);
return v___x_1452_;
}
else
{
return v_newNode_1445_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1460_, lean_object* v_keys_1461_, lean_object* v_vals_1462_, lean_object* v_i_1463_, lean_object* v_entries_1464_){
_start:
{
lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = lean_array_get_size(v_keys_1461_);
v___x_1466_ = lean_nat_dec_lt(v_i_1463_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_dec(v_i_1463_);
return v_entries_1464_;
}
else
{
lean_object* v_k_1467_; lean_object* v_v_1468_; uint64_t v___x_1469_; size_t v_h_1470_; size_t v___x_1471_; lean_object* v___x_1472_; size_t v___x_1473_; size_t v___x_1474_; size_t v___x_1475_; size_t v_h_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_k_1467_ = lean_array_fget_borrowed(v_keys_1461_, v_i_1463_);
v_v_1468_ = lean_array_fget_borrowed(v_vals_1462_, v_i_1463_);
v___x_1469_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1467_);
v_h_1470_ = lean_uint64_to_usize(v___x_1469_);
v___x_1471_ = ((size_t)5ULL);
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = ((size_t)1ULL);
v___x_1474_ = lean_usize_sub(v_depth_1460_, v___x_1473_);
v___x_1475_ = lean_usize_mul(v___x_1471_, v___x_1474_);
v_h_1476_ = lean_usize_shift_right(v_h_1470_, v___x_1475_);
v___x_1477_ = lean_nat_add(v_i_1463_, v___x_1472_);
lean_dec(v_i_1463_);
lean_inc(v_v_1468_);
lean_inc(v_k_1467_);
v___x_1478_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_entries_1464_, v_h_1476_, v_depth_1460_, v_k_1467_, v_v_1468_);
v_i_1463_ = v___x_1477_;
v_entries_1464_ = v___x_1478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1480_, lean_object* v_keys_1481_, lean_object* v_vals_1482_, lean_object* v_i_1483_, lean_object* v_entries_1484_){
_start:
{
size_t v_depth_boxed_1485_; lean_object* v_res_1486_; 
v_depth_boxed_1485_ = lean_unbox_usize(v_depth_1480_);
lean_dec(v_depth_1480_);
v_res_1486_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1485_, v_keys_1481_, v_vals_1482_, v_i_1483_, v_entries_1484_);
lean_dec_ref(v_vals_1482_);
lean_dec_ref(v_keys_1481_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_){
_start:
{
size_t v_x_7232__boxed_1492_; size_t v_x_7233__boxed_1493_; lean_object* v_res_1494_; 
v_x_7232__boxed_1492_ = lean_unbox_usize(v_x_1488_);
lean_dec(v_x_1488_);
v_x_7233__boxed_1493_ = lean_unbox_usize(v_x_1489_);
lean_dec(v_x_1489_);
v_res_1494_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1487_, v_x_7232__boxed_1492_, v_x_7233__boxed_1493_, v_x_1490_, v_x_1491_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_){
_start:
{
uint64_t v___x_1498_; size_t v___x_1499_; size_t v___x_1500_; lean_object* v___x_1501_; 
v___x_1498_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1496_);
v___x_1499_ = lean_uint64_to_usize(v___x_1498_);
v___x_1500_ = ((size_t)1ULL);
v___x_1501_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1495_, v___x_1499_, v___x_1500_, v_x_1496_, v_x_1497_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object* v_e_1502_, lean_object* v_a_1503_, lean_object* v_s_1504_){
_start:
{
lean_object* v_rings_1505_; lean_object* v_typeIdOf_1506_; lean_object* v_exprToRingId_1507_; lean_object* v_semirings_1508_; lean_object* v_stypeIdOf_1509_; lean_object* v_exprToSemiringId_1510_; lean_object* v_ncRings_1511_; lean_object* v_exprToNCRingId_1512_; lean_object* v_nctypeIdOf_1513_; lean_object* v_ncSemirings_1514_; lean_object* v_exprToNCSemiringId_1515_; lean_object* v_ncstypeIdOf_1516_; lean_object* v_steps_1517_; uint8_t v_reportedMaxDegreeIssue_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1526_; 
v_rings_1505_ = lean_ctor_get(v_s_1504_, 0);
v_typeIdOf_1506_ = lean_ctor_get(v_s_1504_, 1);
v_exprToRingId_1507_ = lean_ctor_get(v_s_1504_, 2);
v_semirings_1508_ = lean_ctor_get(v_s_1504_, 3);
v_stypeIdOf_1509_ = lean_ctor_get(v_s_1504_, 4);
v_exprToSemiringId_1510_ = lean_ctor_get(v_s_1504_, 5);
v_ncRings_1511_ = lean_ctor_get(v_s_1504_, 6);
v_exprToNCRingId_1512_ = lean_ctor_get(v_s_1504_, 7);
v_nctypeIdOf_1513_ = lean_ctor_get(v_s_1504_, 8);
v_ncSemirings_1514_ = lean_ctor_get(v_s_1504_, 9);
v_exprToNCSemiringId_1515_ = lean_ctor_get(v_s_1504_, 10);
v_ncstypeIdOf_1516_ = lean_ctor_get(v_s_1504_, 11);
v_steps_1517_ = lean_ctor_get(v_s_1504_, 12);
v_reportedMaxDegreeIssue_1518_ = lean_ctor_get_uint8(v_s_1504_, sizeof(void*)*13);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_s_1504_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1520_ = v_s_1504_;
v_isShared_1521_ = v_isSharedCheck_1526_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_steps_1517_);
lean_inc(v_ncstypeIdOf_1516_);
lean_inc(v_exprToNCSemiringId_1515_);
lean_inc(v_ncSemirings_1514_);
lean_inc(v_nctypeIdOf_1513_);
lean_inc(v_exprToNCRingId_1512_);
lean_inc(v_ncRings_1511_);
lean_inc(v_exprToSemiringId_1510_);
lean_inc(v_stypeIdOf_1509_);
lean_inc(v_semirings_1508_);
lean_inc(v_exprToRingId_1507_);
lean_inc(v_typeIdOf_1506_);
lean_inc(v_rings_1505_);
lean_dec(v_s_1504_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1526_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
lean_inc(v_a_1503_);
v___x_1522_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_exprToSemiringId_1510_, v_e_1502_, v_a_1503_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 5, v___x_1522_);
v___x_1524_ = v___x_1520_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_rings_1505_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_typeIdOf_1506_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_exprToRingId_1507_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_semirings_1508_);
lean_ctor_set(v_reuseFailAlloc_1525_, 4, v_stypeIdOf_1509_);
lean_ctor_set(v_reuseFailAlloc_1525_, 5, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1525_, 6, v_ncRings_1511_);
lean_ctor_set(v_reuseFailAlloc_1525_, 7, v_exprToNCRingId_1512_);
lean_ctor_set(v_reuseFailAlloc_1525_, 8, v_nctypeIdOf_1513_);
lean_ctor_set(v_reuseFailAlloc_1525_, 9, v_ncSemirings_1514_);
lean_ctor_set(v_reuseFailAlloc_1525_, 10, v_exprToNCSemiringId_1515_);
lean_ctor_set(v_reuseFailAlloc_1525_, 11, v_ncstypeIdOf_1516_);
lean_ctor_set(v_reuseFailAlloc_1525_, 12, v_steps_1517_);
lean_ctor_set_uint8(v_reuseFailAlloc_1525_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1518_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object* v_e_1527_, lean_object* v_a_1528_, lean_object* v_s_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(v_e_1527_, v_a_1528_, v_s_1529_);
lean_dec(v_a_1528_);
return v_res_1530_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object* v_e_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1534_, v_a_1536_, v_a_1541_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
if (lean_obj_tag(v_a_1548_) == 1)
{
lean_object* v_val_1549_; uint8_t v___x_1550_; 
v_val_1549_ = lean_ctor_get(v_a_1548_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v_a_1548_, 1);
v___x_1550_ = lean_nat_dec_eq(v_val_1549_, v_a_1535_);
lean_dec(v_val_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1537_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; uint8_t v_verbose_1553_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v_verbose_1553_ = lean_ctor_get_uint8(v_a_1552_, 0);
lean_dec(v_a_1552_);
if (v_verbose_1553_ == 0)
{
lean_dec_ref(v_e_1534_);
goto v___jp_1544_;
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1554_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1);
v___x_1555_ = l_Lean_indentExpr(v_e_1534_);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = l_Lean_Meta_Sym_reportIssue(v___x_1556_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_dec_ref_known(v___x_1557_, 1);
goto v___jp_1544_;
}
else
{
return v___x_1557_;
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v_e_1534_);
v_a_1558_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1551_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1551_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_dec_ref(v_e_1534_);
goto v___jp_1544_;
}
}
else
{
lean_object* v___f_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec(v_a_1548_);
lean_inc(v_a_1535_);
v___f_1566_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1566_, 0, v_e_1534_);
lean_closure_set(v___f_1566_, 1, v_a_1535_);
v___x_1567_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1568_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1567_, v___f_1566_, v_a_1536_);
return v___x_1568_;
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec_ref(v_e_1534_);
v_a_1569_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1547_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1547_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
v___jp_1544_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_box(0);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object* v_e_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec(v_a_1578_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object* v_e_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1588_, v_a_1589_, v_a_1590_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object* v_e_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec(v_a_1603_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object* v_00_u03b2_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_1617_, v_x_1618_, v_x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_1621_, lean_object* v_x_1622_, size_t v_x_1623_, size_t v_x_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1622_, v_x_1623_, v_x_1624_, v_x_1625_, v_x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
size_t v_x_7509__boxed_1634_; size_t v_x_7510__boxed_1635_; lean_object* v_res_1636_; 
v_x_7509__boxed_1634_ = lean_unbox_usize(v_x_1630_);
lean_dec(v_x_1630_);
v_x_7510__boxed_1635_ = lean_unbox_usize(v_x_1631_);
lean_dec(v_x_1631_);
v_res_1636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_1628_, v_x_1629_, v_x_7509__boxed_1634_, v_x_7510__boxed_1635_, v_x_1632_, v_x_1633_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1637_, lean_object* v_n_1638_, lean_object* v_k_1639_, lean_object* v_v_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_1638_, v_k_1639_, v_v_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1642_, size_t v_depth_1643_, lean_object* v_keys_1644_, lean_object* v_vals_1645_, lean_object* v_heq_1646_, lean_object* v_i_1647_, lean_object* v_entries_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_1643_, v_keys_1644_, v_vals_1645_, v_i_1647_, v_entries_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1650_, lean_object* v_depth_1651_, lean_object* v_keys_1652_, lean_object* v_vals_1653_, lean_object* v_heq_1654_, lean_object* v_i_1655_, lean_object* v_entries_1656_){
_start:
{
size_t v_depth_boxed_1657_; lean_object* v_res_1658_; 
v_depth_boxed_1657_ = lean_unbox_usize(v_depth_1651_);
lean_dec(v_depth_1651_);
v_res_1658_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_1650_, v_depth_boxed_1657_, v_keys_1652_, v_vals_1653_, v_heq_1654_, v_i_1655_, v_entries_1656_);
lean_dec_ref(v_vals_1653_);
lean_dec_ref(v_keys_1652_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1659_, lean_object* v_x_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1660_, v_x_1661_, v_x_1662_, v_x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object* v_e_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1665_, v___y_1666_, v___y_1667_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object* v_e_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(v_e_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec(v___y_1680_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object* v_e_1695_, lean_object* v___f_1696_, lean_object* v___f_1697_, lean_object* v_size_1698_, lean_object* v_s_1699_){
_start:
{
lean_object* v_id_1700_; lean_object* v_type_1701_; lean_object* v_u_1702_; lean_object* v_semiringInst_1703_; lean_object* v_addFn_x3f_1704_; lean_object* v_mulFn_x3f_1705_; lean_object* v_powFn_x3f_1706_; lean_object* v_natCastFn_x3f_1707_; lean_object* v_denote_1708_; lean_object* v_vars_1709_; lean_object* v_varMap_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1719_; 
v_id_1700_ = lean_ctor_get(v_s_1699_, 0);
v_type_1701_ = lean_ctor_get(v_s_1699_, 1);
v_u_1702_ = lean_ctor_get(v_s_1699_, 2);
v_semiringInst_1703_ = lean_ctor_get(v_s_1699_, 3);
v_addFn_x3f_1704_ = lean_ctor_get(v_s_1699_, 4);
v_mulFn_x3f_1705_ = lean_ctor_get(v_s_1699_, 5);
v_powFn_x3f_1706_ = lean_ctor_get(v_s_1699_, 6);
v_natCastFn_x3f_1707_ = lean_ctor_get(v_s_1699_, 7);
v_denote_1708_ = lean_ctor_get(v_s_1699_, 8);
v_vars_1709_ = lean_ctor_get(v_s_1699_, 9);
v_varMap_1710_ = lean_ctor_get(v_s_1699_, 10);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_s_1699_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1712_ = v_s_1699_;
v_isShared_1713_ = v_isSharedCheck_1719_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_varMap_1710_);
lean_inc(v_vars_1709_);
lean_inc(v_denote_1708_);
lean_inc(v_natCastFn_x3f_1707_);
lean_inc(v_powFn_x3f_1706_);
lean_inc(v_mulFn_x3f_1705_);
lean_inc(v_addFn_x3f_1704_);
lean_inc(v_semiringInst_1703_);
lean_inc(v_u_1702_);
lean_inc(v_type_1701_);
lean_inc(v_id_1700_);
lean_dec(v_s_1699_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1719_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
lean_inc_ref(v_e_1695_);
v___x_1714_ = l_Lean_PersistentArray_push___redArg(v_vars_1709_, v_e_1695_);
v___x_1715_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1696_, v___f_1697_, v_varMap_1710_, v_e_1695_, v_size_1698_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 10, v___x_1715_);
lean_ctor_set(v___x_1712_, 9, v___x_1714_);
v___x_1717_ = v___x_1712_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_id_1700_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_type_1701_);
lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_u_1702_);
lean_ctor_set(v_reuseFailAlloc_1718_, 3, v_semiringInst_1703_);
lean_ctor_set(v_reuseFailAlloc_1718_, 4, v_addFn_x3f_1704_);
lean_ctor_set(v_reuseFailAlloc_1718_, 5, v_mulFn_x3f_1705_);
lean_ctor_set(v_reuseFailAlloc_1718_, 6, v_powFn_x3f_1706_);
lean_ctor_set(v_reuseFailAlloc_1718_, 7, v_natCastFn_x3f_1707_);
lean_ctor_set(v_reuseFailAlloc_1718_, 8, v_denote_1708_);
lean_ctor_set(v_reuseFailAlloc_1718_, 9, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1718_, 10, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object* v_toPure_1720_, lean_object* v_size_1721_, lean_object* v_____r_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_apply_2(v_toPure_1720_, lean_box(0), v_size_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object* v_e_1724_, lean_object* v_inst_1725_, lean_object* v_toBind_1726_, lean_object* v___f_1727_, lean_object* v_____r_1728_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1729_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1730_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_1730_, 0, lean_box(0));
lean_closure_set(v___x_1730_, 1, v___x_1729_);
lean_closure_set(v___x_1730_, 2, v_e_1724_);
v___x_1731_ = lean_apply_2(v_inst_1725_, lean_box(0), v___x_1730_);
v___x_1732_ = lean_apply_4(v_toBind_1726_, lean_box(0), lean_box(0), v___x_1731_, v___f_1727_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object* v_inst_1733_, lean_object* v_e_1734_, lean_object* v_toBind_1735_, lean_object* v___f_1736_, lean_object* v_____r_1737_){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_apply_1(v_inst_1733_, v_e_1734_);
v___x_1739_ = lean_apply_4(v_toBind_1735_, lean_box(0), lean_box(0), v___x_1738_, v___f_1736_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object* v___f_1740_, lean_object* v___f_1741_, lean_object* v_e_1742_, lean_object* v_toPure_1743_, lean_object* v_inst_1744_, lean_object* v_toBind_1745_, lean_object* v_inst_1746_, lean_object* v_modifySemiring_1747_, lean_object* v_s_1748_){
_start:
{
lean_object* v_vars_1749_; lean_object* v_varMap_1750_; lean_object* v___x_1751_; 
v_vars_1749_ = lean_ctor_get(v_s_1748_, 9);
lean_inc_ref(v_vars_1749_);
v_varMap_1750_ = lean_ctor_get(v_s_1748_, 10);
lean_inc_ref(v_varMap_1750_);
lean_dec_ref(v_s_1748_);
lean_inc_ref(v_e_1742_);
lean_inc_ref(v___f_1741_);
lean_inc_ref(v___f_1740_);
v___x_1751_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_1740_, v___f_1741_, v_varMap_1750_, v_e_1742_);
lean_dec_ref(v_varMap_1750_);
if (lean_obj_tag(v___x_1751_) == 1)
{
lean_object* v_val_1752_; lean_object* v___x_1753_; 
lean_dec_ref(v_vars_1749_);
lean_dec(v_modifySemiring_1747_);
lean_dec(v_inst_1746_);
lean_dec(v_toBind_1745_);
lean_dec(v_inst_1744_);
lean_dec_ref(v_e_1742_);
lean_dec_ref(v___f_1741_);
lean_dec_ref(v___f_1740_);
v_val_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_val_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1753_ = lean_apply_2(v_toPure_1743_, lean_box(0), v_val_1752_);
return v___x_1753_;
}
else
{
lean_object* v_size_1754_; lean_object* v___f_1755_; lean_object* v___f_1756_; lean_object* v___f_1757_; lean_object* v___f_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v___x_1751_);
v_size_1754_ = lean_ctor_get(v_vars_1749_, 2);
lean_inc_n(v_size_1754_, 2);
lean_dec_ref(v_vars_1749_);
lean_inc_ref_n(v_e_1742_, 2);
v___f_1755_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1755_, 0, v_e_1742_);
lean_closure_set(v___f_1755_, 1, v___f_1740_);
lean_closure_set(v___f_1755_, 2, v___f_1741_);
lean_closure_set(v___f_1755_, 3, v_size_1754_);
v___f_1756_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1756_, 0, v_toPure_1743_);
lean_closure_set(v___f_1756_, 1, v_size_1754_);
lean_inc_n(v_toBind_1745_, 2);
v___f_1757_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1757_, 0, v_e_1742_);
lean_closure_set(v___f_1757_, 1, v_inst_1744_);
lean_closure_set(v___f_1757_, 2, v_toBind_1745_);
lean_closure_set(v___f_1757_, 3, v___f_1756_);
v___f_1758_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1758_, 0, v_inst_1746_);
lean_closure_set(v___f_1758_, 1, v_e_1742_);
lean_closure_set(v___f_1758_, 2, v_toBind_1745_);
lean_closure_set(v___f_1758_, 3, v___f_1757_);
v___x_1759_ = lean_apply_1(v_modifySemiring_1747_, v___f_1755_);
v___x_1760_ = lean_apply_4(v_toBind_1745_, lean_box(0), lean_box(0), v___x_1759_, v___f_1758_);
return v___x_1760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_e_1767_){
_start:
{
lean_object* v_toApplicative_1768_; lean_object* v_toBind_1769_; lean_object* v_getSemiring_1770_; lean_object* v_modifySemiring_1771_; lean_object* v_toPure_1772_; lean_object* v___f_1773_; lean_object* v___f_1774_; lean_object* v___f_1775_; lean_object* v___x_1776_; 
v_toApplicative_1768_ = lean_ctor_get(v_inst_1764_, 0);
lean_inc_ref(v_toApplicative_1768_);
v_toBind_1769_ = lean_ctor_get(v_inst_1764_, 1);
lean_inc_n(v_toBind_1769_, 2);
lean_dec_ref(v_inst_1764_);
v_getSemiring_1770_ = lean_ctor_get(v_inst_1765_, 0);
lean_inc(v_getSemiring_1770_);
v_modifySemiring_1771_ = lean_ctor_get(v_inst_1765_, 1);
lean_inc(v_modifySemiring_1771_);
lean_dec_ref(v_inst_1765_);
v_toPure_1772_ = lean_ctor_get(v_toApplicative_1768_, 1);
lean_inc(v_toPure_1772_);
lean_dec_ref(v_toApplicative_1768_);
v___f_1773_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0));
v___f_1774_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1));
v___f_1775_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1775_, 0, v___f_1773_);
lean_closure_set(v___f_1775_, 1, v___f_1774_);
lean_closure_set(v___f_1775_, 2, v_e_1767_);
lean_closure_set(v___f_1775_, 3, v_toPure_1772_);
lean_closure_set(v___f_1775_, 4, v_inst_1763_);
lean_closure_set(v___f_1775_, 5, v_toBind_1769_);
lean_closure_set(v___f_1775_, 6, v_inst_1766_);
lean_closure_set(v___f_1775_, 7, v_modifySemiring_1771_);
v___x_1776_ = lean_apply_4(v_toBind_1769_, lean_box(0), lean_box(0), v_getSemiring_1770_, v___f_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object* v_m_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_e_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v_inst_1778_, v_inst_1779_, v_inst_1780_, v_inst_1781_, v_e_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(lean_object* v___y_1784_, lean_object* v_e_1785_, lean_object* v_size_1786_, lean_object* v_s_1787_){
_start:
{
lean_object* v_rings_1788_; lean_object* v_typeIdOf_1789_; lean_object* v_exprToRingId_1790_; lean_object* v_semirings_1791_; lean_object* v_stypeIdOf_1792_; lean_object* v_exprToSemiringId_1793_; lean_object* v_ncRings_1794_; lean_object* v_exprToNCRingId_1795_; lean_object* v_nctypeIdOf_1796_; lean_object* v_ncSemirings_1797_; lean_object* v_exprToNCSemiringId_1798_; lean_object* v_ncstypeIdOf_1799_; lean_object* v_steps_1800_; uint8_t v_reportedMaxDegreeIssue_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v_rings_1788_ = lean_ctor_get(v_s_1787_, 0);
v_typeIdOf_1789_ = lean_ctor_get(v_s_1787_, 1);
v_exprToRingId_1790_ = lean_ctor_get(v_s_1787_, 2);
v_semirings_1791_ = lean_ctor_get(v_s_1787_, 3);
v_stypeIdOf_1792_ = lean_ctor_get(v_s_1787_, 4);
v_exprToSemiringId_1793_ = lean_ctor_get(v_s_1787_, 5);
v_ncRings_1794_ = lean_ctor_get(v_s_1787_, 6);
v_exprToNCRingId_1795_ = lean_ctor_get(v_s_1787_, 7);
v_nctypeIdOf_1796_ = lean_ctor_get(v_s_1787_, 8);
v_ncSemirings_1797_ = lean_ctor_get(v_s_1787_, 9);
v_exprToNCSemiringId_1798_ = lean_ctor_get(v_s_1787_, 10);
v_ncstypeIdOf_1799_ = lean_ctor_get(v_s_1787_, 11);
v_steps_1800_ = lean_ctor_get(v_s_1787_, 12);
v_reportedMaxDegreeIssue_1801_ = lean_ctor_get_uint8(v_s_1787_, sizeof(void*)*13);
v___x_1802_ = lean_array_get_size(v_semirings_1791_);
v___x_1803_ = lean_nat_dec_lt(v___y_1784_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_dec(v_size_1786_);
lean_dec_ref(v_e_1785_);
return v_s_1787_;
}
else
{
lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1846_; 
lean_inc(v_steps_1800_);
lean_inc_ref(v_ncstypeIdOf_1799_);
lean_inc_ref(v_exprToNCSemiringId_1798_);
lean_inc_ref(v_ncSemirings_1797_);
lean_inc_ref(v_nctypeIdOf_1796_);
lean_inc_ref(v_exprToNCRingId_1795_);
lean_inc_ref(v_ncRings_1794_);
lean_inc_ref(v_exprToSemiringId_1793_);
lean_inc_ref(v_stypeIdOf_1792_);
lean_inc_ref(v_semirings_1791_);
lean_inc_ref(v_exprToRingId_1790_);
lean_inc_ref(v_typeIdOf_1789_);
lean_inc_ref(v_rings_1788_);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_s_1787_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; lean_object* v_unused_1848_; lean_object* v_unused_1849_; lean_object* v_unused_1850_; lean_object* v_unused_1851_; lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; 
v_unused_1847_ = lean_ctor_get(v_s_1787_, 12);
lean_dec(v_unused_1847_);
v_unused_1848_ = lean_ctor_get(v_s_1787_, 11);
lean_dec(v_unused_1848_);
v_unused_1849_ = lean_ctor_get(v_s_1787_, 10);
lean_dec(v_unused_1849_);
v_unused_1850_ = lean_ctor_get(v_s_1787_, 9);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_s_1787_, 8);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_s_1787_, 7);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v_s_1787_, 6);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_s_1787_, 5);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v_s_1787_, 4);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_s_1787_, 3);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_s_1787_, 2);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_s_1787_, 1);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_s_1787_, 0);
lean_dec(v_unused_1859_);
v___x_1805_ = v_s_1787_;
v_isShared_1806_ = v_isSharedCheck_1846_;
goto v_resetjp_1804_;
}
else
{
lean_dec(v_s_1787_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1846_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_v_1807_; lean_object* v_toSemiring_1808_; lean_object* v_ringId_1809_; lean_object* v_commSemiringInst_1810_; lean_object* v_addRightCancelInst_x3f_1811_; lean_object* v_toQFn_x3f_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1845_; 
v_v_1807_ = lean_array_fget(v_semirings_1791_, v___y_1784_);
v_toSemiring_1808_ = lean_ctor_get(v_v_1807_, 0);
v_ringId_1809_ = lean_ctor_get(v_v_1807_, 1);
v_commSemiringInst_1810_ = lean_ctor_get(v_v_1807_, 2);
v_addRightCancelInst_x3f_1811_ = lean_ctor_get(v_v_1807_, 3);
v_toQFn_x3f_1812_ = lean_ctor_get(v_v_1807_, 4);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_v_1807_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1814_ = v_v_1807_;
v_isShared_1815_ = v_isSharedCheck_1845_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_toQFn_x3f_1812_);
lean_inc(v_addRightCancelInst_x3f_1811_);
lean_inc(v_commSemiringInst_1810_);
lean_inc(v_ringId_1809_);
lean_inc(v_toSemiring_1808_);
lean_dec(v_v_1807_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1845_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v_id_1816_; lean_object* v_type_1817_; lean_object* v_u_1818_; lean_object* v_semiringInst_1819_; lean_object* v_addFn_x3f_1820_; lean_object* v_mulFn_x3f_1821_; lean_object* v_powFn_x3f_1822_; lean_object* v_natCastFn_x3f_1823_; lean_object* v_denote_1824_; lean_object* v_vars_1825_; lean_object* v_varMap_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1844_; 
v_id_1816_ = lean_ctor_get(v_toSemiring_1808_, 0);
v_type_1817_ = lean_ctor_get(v_toSemiring_1808_, 1);
v_u_1818_ = lean_ctor_get(v_toSemiring_1808_, 2);
v_semiringInst_1819_ = lean_ctor_get(v_toSemiring_1808_, 3);
v_addFn_x3f_1820_ = lean_ctor_get(v_toSemiring_1808_, 4);
v_mulFn_x3f_1821_ = lean_ctor_get(v_toSemiring_1808_, 5);
v_powFn_x3f_1822_ = lean_ctor_get(v_toSemiring_1808_, 6);
v_natCastFn_x3f_1823_ = lean_ctor_get(v_toSemiring_1808_, 7);
v_denote_1824_ = lean_ctor_get(v_toSemiring_1808_, 8);
v_vars_1825_ = lean_ctor_get(v_toSemiring_1808_, 9);
v_varMap_1826_ = lean_ctor_get(v_toSemiring_1808_, 10);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_toSemiring_1808_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1828_ = v_toSemiring_1808_;
v_isShared_1829_ = v_isSharedCheck_1844_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_varMap_1826_);
lean_inc(v_vars_1825_);
lean_inc(v_denote_1824_);
lean_inc(v_natCastFn_x3f_1823_);
lean_inc(v_powFn_x3f_1822_);
lean_inc(v_mulFn_x3f_1821_);
lean_inc(v_addFn_x3f_1820_);
lean_inc(v_semiringInst_1819_);
lean_inc(v_u_1818_);
lean_inc(v_type_1817_);
lean_inc(v_id_1816_);
lean_dec(v_toSemiring_1808_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1844_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v_xs_x27_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1830_ = lean_box(0);
v_xs_x27_1831_ = lean_array_fset(v_semirings_1791_, v___y_1784_, v___x_1830_);
lean_inc_ref(v_e_1785_);
v___x_1832_ = l_Lean_PersistentArray_push___redArg(v_vars_1825_, v_e_1785_);
v___x_1833_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_varMap_1826_, v_e_1785_, v_size_1786_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 10, v___x_1833_);
lean_ctor_set(v___x_1828_, 9, v___x_1832_);
v___x_1835_ = v___x_1828_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_id_1816_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_type_1817_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_u_1818_);
lean_ctor_set(v_reuseFailAlloc_1843_, 3, v_semiringInst_1819_);
lean_ctor_set(v_reuseFailAlloc_1843_, 4, v_addFn_x3f_1820_);
lean_ctor_set(v_reuseFailAlloc_1843_, 5, v_mulFn_x3f_1821_);
lean_ctor_set(v_reuseFailAlloc_1843_, 6, v_powFn_x3f_1822_);
lean_ctor_set(v_reuseFailAlloc_1843_, 7, v_natCastFn_x3f_1823_);
lean_ctor_set(v_reuseFailAlloc_1843_, 8, v_denote_1824_);
lean_ctor_set(v_reuseFailAlloc_1843_, 9, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1843_, 10, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1835_);
v___x_1837_ = v___x_1814_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_ringId_1809_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_commSemiringInst_1810_);
lean_ctor_set(v_reuseFailAlloc_1842_, 3, v_addRightCancelInst_x3f_1811_);
lean_ctor_set(v_reuseFailAlloc_1842_, 4, v_toQFn_x3f_1812_);
v___x_1837_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = lean_array_fset(v_xs_x27_1831_, v___y_1784_, v___x_1837_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 3, v___x_1838_);
v___x_1840_ = v___x_1805_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_rings_1788_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_typeIdOf_1789_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_exprToRingId_1790_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_stypeIdOf_1792_);
lean_ctor_set(v_reuseFailAlloc_1841_, 5, v_exprToSemiringId_1793_);
lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_ncRings_1794_);
lean_ctor_set(v_reuseFailAlloc_1841_, 7, v_exprToNCRingId_1795_);
lean_ctor_set(v_reuseFailAlloc_1841_, 8, v_nctypeIdOf_1796_);
lean_ctor_set(v_reuseFailAlloc_1841_, 9, v_ncSemirings_1797_);
lean_ctor_set(v_reuseFailAlloc_1841_, 10, v_exprToNCSemiringId_1798_);
lean_ctor_set(v_reuseFailAlloc_1841_, 11, v_ncstypeIdOf_1799_);
lean_ctor_set(v_reuseFailAlloc_1841_, 12, v_steps_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1801_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed(lean_object* v___y_1860_, lean_object* v_e_1861_, lean_object* v_size_1862_, lean_object* v_s_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(v___y_1860_, v_e_1861_, v_size_1862_, v_s_1863_);
lean_dec(v___y_1860_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(lean_object* v_e_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1929_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1929_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1929_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v_toSemiring_1883_; lean_object* v_vars_1884_; lean_object* v_varMap_1885_; lean_object* v___x_1886_; 
v_toSemiring_1883_ = lean_ctor_get(v_a_1879_, 0);
lean_inc_ref(v_toSemiring_1883_);
lean_dec(v_a_1879_);
v_vars_1884_ = lean_ctor_get(v_toSemiring_1883_, 9);
lean_inc_ref(v_vars_1884_);
v_varMap_1885_ = lean_ctor_get(v_toSemiring_1883_, 10);
lean_inc_ref(v_varMap_1885_);
lean_dec_ref(v_toSemiring_1883_);
v___x_1886_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_varMap_1885_, v_e_1865_);
lean_dec_ref(v_varMap_1885_);
if (lean_obj_tag(v___x_1886_) == 1)
{
lean_object* v_val_1887_; lean_object* v___x_1889_; 
lean_dec_ref(v_vars_1884_);
lean_dec_ref(v_e_1865_);
v_val_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_val_1887_);
lean_dec_ref_known(v___x_1886_, 1);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v_val_1887_);
v___x_1889_ = v___x_1881_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_val_1887_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
else
{
lean_object* v_size_1891_; lean_object* v___f_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec(v___x_1886_);
lean_del_object(v___x_1881_);
v_size_1891_ = lean_ctor_get(v_vars_1884_, 2);
lean_inc_n(v_size_1891_, 2);
lean_dec_ref(v_vars_1884_);
lean_inc_ref(v_e_1865_);
lean_inc(v___y_1866_);
v___f_1892_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1892_, 0, v___y_1866_);
lean_closure_set(v___f_1892_, 1, v_e_1865_);
lean_closure_set(v___f_1892_, 2, v_size_1891_);
v___x_1893_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1894_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1893_, v___f_1892_, v___y_1867_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1895_; 
lean_dec_ref_known(v___x_1894_, 1);
lean_inc_ref(v_e_1865_);
v___x_1895_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1865_, v___y_1866_, v___y_1867_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v___x_1896_; 
lean_dec_ref_known(v___x_1895_, 1);
v___x_1896_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1893_, v_e_1865_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1903_ == 0)
{
lean_object* v_unused_1904_; 
v_unused_1904_ = lean_ctor_get(v___x_1896_, 0);
lean_dec(v_unused_1904_);
v___x_1898_ = v___x_1896_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_dec(v___x_1896_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v_size_1891_);
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_size_1891_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v_size_1891_);
v_a_1905_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1896_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1896_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_size_1891_);
lean_dec_ref(v_e_1865_);
v_a_1913_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1895_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1895_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_size_1891_);
lean_dec_ref(v_e_1865_);
v_a_1921_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1894_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1894_);
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
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v_e_1865_);
v_a_1930_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1878_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1878_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___boxed(lean_object* v_e_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec(v___y_1939_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object* v_e_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar___boxed(lean_object* v_e_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVar(v_e_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec(v_a_1967_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object* v_a_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_nat_to_int(v_a_1980_);
return v___x_1981_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object* v_msg_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; lean_object* v___f_1997_; lean_object* v___x_40218__overap_1998_; lean_object* v___x_1999_; 
v___x_1996_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0);
v___f_1997_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1997_, 0, v___x_1996_);
v___x_40218__overap_1998_ = lean_panic_fn_borrowed(v___f_1997_, v_msg_1983_);
lean_dec_ref(v___f_1997_);
lean_inc(v___y_1994_);
lean_inc_ref(v___y_1993_);
lean_inc(v___y_1992_);
lean_inc_ref(v___y_1991_);
lean_inc(v___y_1990_);
lean_inc_ref(v___y_1989_);
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1987_);
lean_inc(v___y_1986_);
lean_inc(v___y_1985_);
lean_inc(v___y_1984_);
v___x_1999_ = lean_apply_12(v___x_40218__overap_1998_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, lean_box(0));
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object* v_msg_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_msg_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec(v___y_2001_);
return v_res_2013_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0));
v___x_2016_ = l_Lean_stringToMessageData(v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(lean_object* v_type_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
lean_inc_ref(v_type_2017_);
v___x_2024_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2037_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2037_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2037_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
if (lean_obj_tag(v_a_2025_) == 1)
{
lean_object* v_val_2029_; lean_object* v___x_2031_; 
lean_dec_ref(v_type_2017_);
v_val_2029_ = lean_ctor_get(v_a_2025_, 0);
lean_inc(v_val_2029_);
lean_dec_ref_known(v_a_2025_, 1);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v_val_2029_);
v___x_2031_ = v___x_2027_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_val_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_del_object(v___x_2027_);
lean_dec(v_a_2025_);
v___x_2033_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1);
v___x_2034_ = l_Lean_indentExpr(v_type_2017_);
v___x_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2033_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_2035_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
return v___x_2036_;
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_type_2017_);
v_a_2038_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2024_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2024_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_type_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(lean_object* v_type_2054_, lean_object* v_u_2055_, lean_object* v_instDeclName_2056_, lean_object* v_declName_2057_, lean_object* v_expectedInst_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2071_ = lean_box(0);
lean_inc_n(v_u_2055_, 2);
v___x_2072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2072_, 0, v_u_2055_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2073_, 0, v_u_2055_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_u_2055_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
lean_inc_ref(v___x_2074_);
v___x_2075_ = l_Lean_mkConst(v_instDeclName_2056_, v___x_2074_);
lean_inc_ref_n(v_type_2054_, 3);
v___x_2076_ = l_Lean_mkApp3(v___x_2075_, v_type_2054_, v_type_2054_, v_type_2054_);
v___x_2077_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2076_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc_n(v_a_2078_, 2);
lean_dec_ref_known(v___x_2077_, 1);
lean_inc(v_declName_2057_);
v___x_2079_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2057_, v_a_2078_, v_expectedInst_2058_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec_ref_known(v___x_2079_, 1);
v___x_2080_ = l_Lean_mkConst(v_declName_2057_, v___x_2074_);
lean_inc_ref_n(v_type_2054_, 2);
v___x_2081_ = l_Lean_mkApp4(v___x_2080_, v_type_2054_, v_type_2054_, v_type_2054_, v_a_2078_);
v___x_2082_ = l_Lean_Meta_Sym_canon(v___x_2081_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2084_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v___x_2084_ = l_Lean_Meta_Sym_shareCommon(v_a_2083_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
return v___x_2084_;
}
else
{
return v___x_2082_;
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_a_2078_);
lean_dec_ref_known(v___x_2074_, 2);
lean_dec(v_declName_2057_);
lean_dec_ref(v_type_2054_);
v_a_2085_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2079_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2079_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2074_, 2);
lean_dec_ref(v_expectedInst_2058_);
lean_dec(v_declName_2057_);
lean_dec_ref(v_type_2054_);
return v___x_2077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_type_2093_ = _args[0];
lean_object* v_u_2094_ = _args[1];
lean_object* v_instDeclName_2095_ = _args[2];
lean_object* v_declName_2096_ = _args[3];
lean_object* v_expectedInst_2097_ = _args[4];
lean_object* v___y_2098_ = _args[5];
lean_object* v___y_2099_ = _args[6];
lean_object* v___y_2100_ = _args[7];
lean_object* v___y_2101_ = _args[8];
lean_object* v___y_2102_ = _args[9];
lean_object* v___y_2103_ = _args[10];
lean_object* v___y_2104_ = _args[11];
lean_object* v___y_2105_ = _args[12];
lean_object* v___y_2106_ = _args[13];
lean_object* v___y_2107_ = _args[14];
lean_object* v___y_2108_ = _args[15];
lean_object* v___y_2109_ = _args[16];
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2093_, v_u_2094_, v_instDeclName_2095_, v_declName_2096_, v_expectedInst_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec(v___y_2098_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object* v_a_2111_, lean_object* v_s_2112_){
_start:
{
lean_object* v_toRing_2113_; lean_object* v_invFn_x3f_2114_; lean_object* v_semiringId_x3f_2115_; lean_object* v_commSemiringInst_2116_; lean_object* v_commRingInst_2117_; lean_object* v_noZeroDivInst_x3f_2118_; lean_object* v_fieldInst_x3f_2119_; lean_object* v_powIdentityInst_x3f_2120_; lean_object* v_denoteEntries_2121_; lean_object* v_nextId_2122_; lean_object* v_steps_2123_; lean_object* v_queue_2124_; lean_object* v_basis_2125_; lean_object* v_diseqs_2126_; uint8_t v_recheck_2127_; lean_object* v_invSet_2128_; lean_object* v_powIdentityVarCount_2129_; lean_object* v_numEq0_x3f_2130_; uint8_t v_numEq0Updated_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2163_; 
v_toRing_2113_ = lean_ctor_get(v_s_2112_, 0);
v_invFn_x3f_2114_ = lean_ctor_get(v_s_2112_, 1);
v_semiringId_x3f_2115_ = lean_ctor_get(v_s_2112_, 2);
v_commSemiringInst_2116_ = lean_ctor_get(v_s_2112_, 3);
v_commRingInst_2117_ = lean_ctor_get(v_s_2112_, 4);
v_noZeroDivInst_x3f_2118_ = lean_ctor_get(v_s_2112_, 5);
v_fieldInst_x3f_2119_ = lean_ctor_get(v_s_2112_, 6);
v_powIdentityInst_x3f_2120_ = lean_ctor_get(v_s_2112_, 7);
v_denoteEntries_2121_ = lean_ctor_get(v_s_2112_, 8);
v_nextId_2122_ = lean_ctor_get(v_s_2112_, 9);
v_steps_2123_ = lean_ctor_get(v_s_2112_, 10);
v_queue_2124_ = lean_ctor_get(v_s_2112_, 11);
v_basis_2125_ = lean_ctor_get(v_s_2112_, 12);
v_diseqs_2126_ = lean_ctor_get(v_s_2112_, 13);
v_recheck_2127_ = lean_ctor_get_uint8(v_s_2112_, sizeof(void*)*17);
v_invSet_2128_ = lean_ctor_get(v_s_2112_, 14);
v_powIdentityVarCount_2129_ = lean_ctor_get(v_s_2112_, 15);
v_numEq0_x3f_2130_ = lean_ctor_get(v_s_2112_, 16);
v_numEq0Updated_2131_ = lean_ctor_get_uint8(v_s_2112_, sizeof(void*)*17 + 1);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_s_2112_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2133_ = v_s_2112_;
v_isShared_2134_ = v_isSharedCheck_2163_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_numEq0_x3f_2130_);
lean_inc(v_powIdentityVarCount_2129_);
lean_inc(v_invSet_2128_);
lean_inc(v_diseqs_2126_);
lean_inc(v_basis_2125_);
lean_inc(v_queue_2124_);
lean_inc(v_steps_2123_);
lean_inc(v_nextId_2122_);
lean_inc(v_denoteEntries_2121_);
lean_inc(v_powIdentityInst_x3f_2120_);
lean_inc(v_fieldInst_x3f_2119_);
lean_inc(v_noZeroDivInst_x3f_2118_);
lean_inc(v_commRingInst_2117_);
lean_inc(v_commSemiringInst_2116_);
lean_inc(v_semiringId_x3f_2115_);
lean_inc(v_invFn_x3f_2114_);
lean_inc(v_toRing_2113_);
lean_dec(v_s_2112_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2163_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_id_2135_; lean_object* v_type_2136_; lean_object* v_u_2137_; lean_object* v_ringInst_2138_; lean_object* v_semiringInst_2139_; lean_object* v_charInst_x3f_2140_; lean_object* v_addFn_x3f_2141_; lean_object* v_subFn_x3f_2142_; lean_object* v_negFn_x3f_2143_; lean_object* v_powFn_x3f_2144_; lean_object* v_intCastFn_x3f_2145_; lean_object* v_natCastFn_x3f_2146_; lean_object* v_one_x3f_2147_; lean_object* v_vars_2148_; lean_object* v_varMap_2149_; lean_object* v_denote_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2161_; 
v_id_2135_ = lean_ctor_get(v_toRing_2113_, 0);
v_type_2136_ = lean_ctor_get(v_toRing_2113_, 1);
v_u_2137_ = lean_ctor_get(v_toRing_2113_, 2);
v_ringInst_2138_ = lean_ctor_get(v_toRing_2113_, 3);
v_semiringInst_2139_ = lean_ctor_get(v_toRing_2113_, 4);
v_charInst_x3f_2140_ = lean_ctor_get(v_toRing_2113_, 5);
v_addFn_x3f_2141_ = lean_ctor_get(v_toRing_2113_, 6);
v_subFn_x3f_2142_ = lean_ctor_get(v_toRing_2113_, 8);
v_negFn_x3f_2143_ = lean_ctor_get(v_toRing_2113_, 9);
v_powFn_x3f_2144_ = lean_ctor_get(v_toRing_2113_, 10);
v_intCastFn_x3f_2145_ = lean_ctor_get(v_toRing_2113_, 11);
v_natCastFn_x3f_2146_ = lean_ctor_get(v_toRing_2113_, 12);
v_one_x3f_2147_ = lean_ctor_get(v_toRing_2113_, 13);
v_vars_2148_ = lean_ctor_get(v_toRing_2113_, 14);
v_varMap_2149_ = lean_ctor_get(v_toRing_2113_, 15);
v_denote_2150_ = lean_ctor_get(v_toRing_2113_, 16);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_toRing_2113_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v_toRing_2113_, 7);
lean_dec(v_unused_2162_);
v___x_2152_ = v_toRing_2113_;
v_isShared_2153_ = v_isSharedCheck_2161_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_denote_2150_);
lean_inc(v_varMap_2149_);
lean_inc(v_vars_2148_);
lean_inc(v_one_x3f_2147_);
lean_inc(v_natCastFn_x3f_2146_);
lean_inc(v_intCastFn_x3f_2145_);
lean_inc(v_powFn_x3f_2144_);
lean_inc(v_negFn_x3f_2143_);
lean_inc(v_subFn_x3f_2142_);
lean_inc(v_addFn_x3f_2141_);
lean_inc(v_charInst_x3f_2140_);
lean_inc(v_semiringInst_2139_);
lean_inc(v_ringInst_2138_);
lean_inc(v_u_2137_);
lean_inc(v_type_2136_);
lean_inc(v_id_2135_);
lean_dec(v_toRing_2113_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2161_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2154_, 0, v_a_2111_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 7, v___x_2154_);
v___x_2156_ = v___x_2152_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_id_2135_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_type_2136_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_u_2137_);
lean_ctor_set(v_reuseFailAlloc_2160_, 3, v_ringInst_2138_);
lean_ctor_set(v_reuseFailAlloc_2160_, 4, v_semiringInst_2139_);
lean_ctor_set(v_reuseFailAlloc_2160_, 5, v_charInst_x3f_2140_);
lean_ctor_set(v_reuseFailAlloc_2160_, 6, v_addFn_x3f_2141_);
lean_ctor_set(v_reuseFailAlloc_2160_, 7, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2160_, 8, v_subFn_x3f_2142_);
lean_ctor_set(v_reuseFailAlloc_2160_, 9, v_negFn_x3f_2143_);
lean_ctor_set(v_reuseFailAlloc_2160_, 10, v_powFn_x3f_2144_);
lean_ctor_set(v_reuseFailAlloc_2160_, 11, v_intCastFn_x3f_2145_);
lean_ctor_set(v_reuseFailAlloc_2160_, 12, v_natCastFn_x3f_2146_);
lean_ctor_set(v_reuseFailAlloc_2160_, 13, v_one_x3f_2147_);
lean_ctor_set(v_reuseFailAlloc_2160_, 14, v_vars_2148_);
lean_ctor_set(v_reuseFailAlloc_2160_, 15, v_varMap_2149_);
lean_ctor_set(v_reuseFailAlloc_2160_, 16, v_denote_2150_);
v___x_2156_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2158_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2156_);
v___x_2158_ = v___x_2133_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_invFn_x3f_2114_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_semiringId_x3f_2115_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_commSemiringInst_2116_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v_commRingInst_2117_);
lean_ctor_set(v_reuseFailAlloc_2159_, 5, v_noZeroDivInst_x3f_2118_);
lean_ctor_set(v_reuseFailAlloc_2159_, 6, v_fieldInst_x3f_2119_);
lean_ctor_set(v_reuseFailAlloc_2159_, 7, v_powIdentityInst_x3f_2120_);
lean_ctor_set(v_reuseFailAlloc_2159_, 8, v_denoteEntries_2121_);
lean_ctor_set(v_reuseFailAlloc_2159_, 9, v_nextId_2122_);
lean_ctor_set(v_reuseFailAlloc_2159_, 10, v_steps_2123_);
lean_ctor_set(v_reuseFailAlloc_2159_, 11, v_queue_2124_);
lean_ctor_set(v_reuseFailAlloc_2159_, 12, v_basis_2125_);
lean_ctor_set(v_reuseFailAlloc_2159_, 13, v_diseqs_2126_);
lean_ctor_set(v_reuseFailAlloc_2159_, 14, v_invSet_2128_);
lean_ctor_set(v_reuseFailAlloc_2159_, 15, v_powIdentityVarCount_2129_);
lean_ctor_set(v_reuseFailAlloc_2159_, 16, v_numEq0_x3f_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, sizeof(void*)*17, v_recheck_2127_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, sizeof(void*)*17 + 1, v_numEq0Updated_2131_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2220_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2220_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2220_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_toRing_2181_; lean_object* v_mulFn_x3f_2182_; 
v_toRing_2181_ = lean_ctor_get(v_a_2177_, 0);
lean_inc_ref(v_toRing_2181_);
lean_dec(v_a_2177_);
v_mulFn_x3f_2182_ = lean_ctor_get(v_toRing_2181_, 7);
if (lean_obj_tag(v_mulFn_x3f_2182_) == 1)
{
lean_object* v_val_2183_; lean_object* v___x_2185_; 
lean_inc_ref(v_mulFn_x3f_2182_);
lean_dec_ref(v_toRing_2181_);
v_val_2183_ = lean_ctor_get(v_mulFn_x3f_2182_, 0);
lean_inc(v_val_2183_);
lean_dec_ref_known(v_mulFn_x3f_2182_, 1);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v_val_2183_);
v___x_2185_ = v___x_2179_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_val_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
else
{
lean_object* v_type_2187_; lean_object* v_u_2188_; lean_object* v_semiringInst_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v_expectedInst_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_del_object(v___x_2179_);
v_type_2187_ = lean_ctor_get(v_toRing_2181_, 1);
lean_inc_ref_n(v_type_2187_, 3);
v_u_2188_ = lean_ctor_get(v_toRing_2181_, 2);
lean_inc_n(v_u_2188_, 2);
v_semiringInst_2189_ = lean_ctor_get(v_toRing_2181_, 4);
lean_inc_ref(v_semiringInst_2189_);
lean_dec_ref(v_toRing_2181_);
v___x_2190_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_u_2188_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
lean_inc_ref(v___x_2192_);
v___x_2193_ = l_Lean_mkConst(v___x_2190_, v___x_2192_);
v___x_2194_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_2195_ = l_Lean_mkConst(v___x_2194_, v___x_2192_);
v___x_2196_ = l_Lean_mkAppB(v___x_2195_, v_type_2187_, v_semiringInst_2189_);
v_expectedInst_2197_ = l_Lean_mkAppB(v___x_2193_, v_type_2187_, v___x_2196_);
v___x_2198_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_2199_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_2200_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2187_, v_u_2188_, v___x_2198_, v___x_2199_, v_expectedInst_2197_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___f_2202_; lean_object* v___x_2203_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc_n(v_a_2201_, 2);
lean_dec_ref_known(v___x_2200_, 1);
v___f_2202_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2202_, 0, v_a_2201_);
v___x_2203_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2202_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; 
v_unused_2211_ = lean_ctor_get(v___x_2203_, 0);
lean_dec(v_unused_2211_);
v___x_2205_ = v___x_2203_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_dec(v___x_2203_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v_a_2201_);
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2201_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_a_2201_);
v_a_2212_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2203_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2203_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
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
return v___x_2200_;
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
v_a_2221_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2176_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2176_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec(v___y_2229_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object* v_a_2242_, lean_object* v_s_2243_){
_start:
{
lean_object* v_toRing_2244_; lean_object* v_invFn_x3f_2245_; lean_object* v_semiringId_x3f_2246_; lean_object* v_commSemiringInst_2247_; lean_object* v_commRingInst_2248_; lean_object* v_noZeroDivInst_x3f_2249_; lean_object* v_fieldInst_x3f_2250_; lean_object* v_powIdentityInst_x3f_2251_; lean_object* v_denoteEntries_2252_; lean_object* v_nextId_2253_; lean_object* v_steps_2254_; lean_object* v_queue_2255_; lean_object* v_basis_2256_; lean_object* v_diseqs_2257_; uint8_t v_recheck_2258_; lean_object* v_invSet_2259_; lean_object* v_powIdentityVarCount_2260_; lean_object* v_numEq0_x3f_2261_; uint8_t v_numEq0Updated_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2294_; 
v_toRing_2244_ = lean_ctor_get(v_s_2243_, 0);
v_invFn_x3f_2245_ = lean_ctor_get(v_s_2243_, 1);
v_semiringId_x3f_2246_ = lean_ctor_get(v_s_2243_, 2);
v_commSemiringInst_2247_ = lean_ctor_get(v_s_2243_, 3);
v_commRingInst_2248_ = lean_ctor_get(v_s_2243_, 4);
v_noZeroDivInst_x3f_2249_ = lean_ctor_get(v_s_2243_, 5);
v_fieldInst_x3f_2250_ = lean_ctor_get(v_s_2243_, 6);
v_powIdentityInst_x3f_2251_ = lean_ctor_get(v_s_2243_, 7);
v_denoteEntries_2252_ = lean_ctor_get(v_s_2243_, 8);
v_nextId_2253_ = lean_ctor_get(v_s_2243_, 9);
v_steps_2254_ = lean_ctor_get(v_s_2243_, 10);
v_queue_2255_ = lean_ctor_get(v_s_2243_, 11);
v_basis_2256_ = lean_ctor_get(v_s_2243_, 12);
v_diseqs_2257_ = lean_ctor_get(v_s_2243_, 13);
v_recheck_2258_ = lean_ctor_get_uint8(v_s_2243_, sizeof(void*)*17);
v_invSet_2259_ = lean_ctor_get(v_s_2243_, 14);
v_powIdentityVarCount_2260_ = lean_ctor_get(v_s_2243_, 15);
v_numEq0_x3f_2261_ = lean_ctor_get(v_s_2243_, 16);
v_numEq0Updated_2262_ = lean_ctor_get_uint8(v_s_2243_, sizeof(void*)*17 + 1);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_s_2243_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2264_ = v_s_2243_;
v_isShared_2265_ = v_isSharedCheck_2294_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_numEq0_x3f_2261_);
lean_inc(v_powIdentityVarCount_2260_);
lean_inc(v_invSet_2259_);
lean_inc(v_diseqs_2257_);
lean_inc(v_basis_2256_);
lean_inc(v_queue_2255_);
lean_inc(v_steps_2254_);
lean_inc(v_nextId_2253_);
lean_inc(v_denoteEntries_2252_);
lean_inc(v_powIdentityInst_x3f_2251_);
lean_inc(v_fieldInst_x3f_2250_);
lean_inc(v_noZeroDivInst_x3f_2249_);
lean_inc(v_commRingInst_2248_);
lean_inc(v_commSemiringInst_2247_);
lean_inc(v_semiringId_x3f_2246_);
lean_inc(v_invFn_x3f_2245_);
lean_inc(v_toRing_2244_);
lean_dec(v_s_2243_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2294_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v_id_2266_; lean_object* v_type_2267_; lean_object* v_u_2268_; lean_object* v_ringInst_2269_; lean_object* v_semiringInst_2270_; lean_object* v_charInst_x3f_2271_; lean_object* v_mulFn_x3f_2272_; lean_object* v_subFn_x3f_2273_; lean_object* v_negFn_x3f_2274_; lean_object* v_powFn_x3f_2275_; lean_object* v_intCastFn_x3f_2276_; lean_object* v_natCastFn_x3f_2277_; lean_object* v_one_x3f_2278_; lean_object* v_vars_2279_; lean_object* v_varMap_2280_; lean_object* v_denote_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2292_; 
v_id_2266_ = lean_ctor_get(v_toRing_2244_, 0);
v_type_2267_ = lean_ctor_get(v_toRing_2244_, 1);
v_u_2268_ = lean_ctor_get(v_toRing_2244_, 2);
v_ringInst_2269_ = lean_ctor_get(v_toRing_2244_, 3);
v_semiringInst_2270_ = lean_ctor_get(v_toRing_2244_, 4);
v_charInst_x3f_2271_ = lean_ctor_get(v_toRing_2244_, 5);
v_mulFn_x3f_2272_ = lean_ctor_get(v_toRing_2244_, 7);
v_subFn_x3f_2273_ = lean_ctor_get(v_toRing_2244_, 8);
v_negFn_x3f_2274_ = lean_ctor_get(v_toRing_2244_, 9);
v_powFn_x3f_2275_ = lean_ctor_get(v_toRing_2244_, 10);
v_intCastFn_x3f_2276_ = lean_ctor_get(v_toRing_2244_, 11);
v_natCastFn_x3f_2277_ = lean_ctor_get(v_toRing_2244_, 12);
v_one_x3f_2278_ = lean_ctor_get(v_toRing_2244_, 13);
v_vars_2279_ = lean_ctor_get(v_toRing_2244_, 14);
v_varMap_2280_ = lean_ctor_get(v_toRing_2244_, 15);
v_denote_2281_ = lean_ctor_get(v_toRing_2244_, 16);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_toRing_2244_);
if (v_isSharedCheck_2292_ == 0)
{
lean_object* v_unused_2293_; 
v_unused_2293_ = lean_ctor_get(v_toRing_2244_, 6);
lean_dec(v_unused_2293_);
v___x_2283_ = v_toRing_2244_;
v_isShared_2284_ = v_isSharedCheck_2292_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_denote_2281_);
lean_inc(v_varMap_2280_);
lean_inc(v_vars_2279_);
lean_inc(v_one_x3f_2278_);
lean_inc(v_natCastFn_x3f_2277_);
lean_inc(v_intCastFn_x3f_2276_);
lean_inc(v_powFn_x3f_2275_);
lean_inc(v_negFn_x3f_2274_);
lean_inc(v_subFn_x3f_2273_);
lean_inc(v_mulFn_x3f_2272_);
lean_inc(v_charInst_x3f_2271_);
lean_inc(v_semiringInst_2270_);
lean_inc(v_ringInst_2269_);
lean_inc(v_u_2268_);
lean_inc(v_type_2267_);
lean_inc(v_id_2266_);
lean_dec(v_toRing_2244_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2292_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2285_, 0, v_a_2242_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 6, v___x_2285_);
v___x_2287_ = v___x_2283_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_id_2266_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_type_2267_);
lean_ctor_set(v_reuseFailAlloc_2291_, 2, v_u_2268_);
lean_ctor_set(v_reuseFailAlloc_2291_, 3, v_ringInst_2269_);
lean_ctor_set(v_reuseFailAlloc_2291_, 4, v_semiringInst_2270_);
lean_ctor_set(v_reuseFailAlloc_2291_, 5, v_charInst_x3f_2271_);
lean_ctor_set(v_reuseFailAlloc_2291_, 6, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2291_, 7, v_mulFn_x3f_2272_);
lean_ctor_set(v_reuseFailAlloc_2291_, 8, v_subFn_x3f_2273_);
lean_ctor_set(v_reuseFailAlloc_2291_, 9, v_negFn_x3f_2274_);
lean_ctor_set(v_reuseFailAlloc_2291_, 10, v_powFn_x3f_2275_);
lean_ctor_set(v_reuseFailAlloc_2291_, 11, v_intCastFn_x3f_2276_);
lean_ctor_set(v_reuseFailAlloc_2291_, 12, v_natCastFn_x3f_2277_);
lean_ctor_set(v_reuseFailAlloc_2291_, 13, v_one_x3f_2278_);
lean_ctor_set(v_reuseFailAlloc_2291_, 14, v_vars_2279_);
lean_ctor_set(v_reuseFailAlloc_2291_, 15, v_varMap_2280_);
lean_ctor_set(v_reuseFailAlloc_2291_, 16, v_denote_2281_);
v___x_2287_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2289_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2287_);
v___x_2289_ = v___x_2264_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_invFn_x3f_2245_);
lean_ctor_set(v_reuseFailAlloc_2290_, 2, v_semiringId_x3f_2246_);
lean_ctor_set(v_reuseFailAlloc_2290_, 3, v_commSemiringInst_2247_);
lean_ctor_set(v_reuseFailAlloc_2290_, 4, v_commRingInst_2248_);
lean_ctor_set(v_reuseFailAlloc_2290_, 5, v_noZeroDivInst_x3f_2249_);
lean_ctor_set(v_reuseFailAlloc_2290_, 6, v_fieldInst_x3f_2250_);
lean_ctor_set(v_reuseFailAlloc_2290_, 7, v_powIdentityInst_x3f_2251_);
lean_ctor_set(v_reuseFailAlloc_2290_, 8, v_denoteEntries_2252_);
lean_ctor_set(v_reuseFailAlloc_2290_, 9, v_nextId_2253_);
lean_ctor_set(v_reuseFailAlloc_2290_, 10, v_steps_2254_);
lean_ctor_set(v_reuseFailAlloc_2290_, 11, v_queue_2255_);
lean_ctor_set(v_reuseFailAlloc_2290_, 12, v_basis_2256_);
lean_ctor_set(v_reuseFailAlloc_2290_, 13, v_diseqs_2257_);
lean_ctor_set(v_reuseFailAlloc_2290_, 14, v_invSet_2259_);
lean_ctor_set(v_reuseFailAlloc_2290_, 15, v_powIdentityVarCount_2260_);
lean_ctor_set(v_reuseFailAlloc_2290_, 16, v_numEq0_x3f_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2290_, sizeof(void*)*17, v_recheck_2258_);
lean_ctor_set_uint8(v_reuseFailAlloc_2290_, sizeof(void*)*17 + 1, v_numEq0Updated_2262_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2351_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2351_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2351_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_toRing_2312_; lean_object* v_addFn_x3f_2313_; 
v_toRing_2312_ = lean_ctor_get(v_a_2308_, 0);
lean_inc_ref(v_toRing_2312_);
lean_dec(v_a_2308_);
v_addFn_x3f_2313_ = lean_ctor_get(v_toRing_2312_, 6);
if (lean_obj_tag(v_addFn_x3f_2313_) == 1)
{
lean_object* v_val_2314_; lean_object* v___x_2316_; 
lean_inc_ref(v_addFn_x3f_2313_);
lean_dec_ref(v_toRing_2312_);
v_val_2314_ = lean_ctor_get(v_addFn_x3f_2313_, 0);
lean_inc(v_val_2314_);
lean_dec_ref_known(v_addFn_x3f_2313_, 1);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v_val_2314_);
v___x_2316_ = v___x_2310_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_val_2314_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
else
{
lean_object* v_type_2318_; lean_object* v_u_2319_; lean_object* v_semiringInst_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v_expectedInst_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_del_object(v___x_2310_);
v_type_2318_ = lean_ctor_get(v_toRing_2312_, 1);
lean_inc_ref_n(v_type_2318_, 3);
v_u_2319_ = lean_ctor_get(v_toRing_2312_, 2);
lean_inc_n(v_u_2319_, 2);
v_semiringInst_2320_ = lean_ctor_get(v_toRing_2312_, 4);
lean_inc_ref(v_semiringInst_2320_);
lean_dec_ref(v_toRing_2312_);
v___x_2321_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_u_2319_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
lean_inc_ref(v___x_2323_);
v___x_2324_ = l_Lean_mkConst(v___x_2321_, v___x_2323_);
v___x_2325_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_2326_ = l_Lean_mkConst(v___x_2325_, v___x_2323_);
v___x_2327_ = l_Lean_mkAppB(v___x_2326_, v_type_2318_, v_semiringInst_2320_);
v_expectedInst_2328_ = l_Lean_mkAppB(v___x_2324_, v_type_2318_, v___x_2327_);
v___x_2329_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_2330_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_2331_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2318_, v_u_2319_, v___x_2329_, v___x_2330_, v_expectedInst_2328_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___f_2333_; lean_object* v___x_2334_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc_n(v_a_2332_, 2);
lean_dec_ref_known(v___x_2331_, 1);
v___f_2333_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_2333_, 0, v_a_2332_);
v___x_2334_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2333_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; 
v_unused_2342_ = lean_ctor_get(v___x_2334_, 0);
lean_dec(v_unused_2342_);
v___x_2336_ = v___x_2334_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_dec(v___x_2334_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v_a_2332_);
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2332_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_a_2332_);
v_a_2343_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2334_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2334_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
else
{
return v___x_2331_;
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
v_a_2352_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2307_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2307_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec(v___y_2360_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(lean_object* v_type_2373_, lean_object* v_u_2374_, lean_object* v_instDeclName_2375_, lean_object* v_declName_2376_, lean_object* v_expectedInst_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2391_, 0, v_u_2374_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
lean_inc_ref(v___x_2391_);
v___x_2392_ = l_Lean_mkConst(v_instDeclName_2375_, v___x_2391_);
lean_inc_ref(v_type_2373_);
v___x_2393_ = l_Lean_Expr_app___override(v___x_2392_, v_type_2373_);
v___x_2394_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2393_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2396_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc_n(v_a_2395_, 2);
lean_dec_ref_known(v___x_2394_, 1);
lean_inc(v_declName_2376_);
v___x_2396_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2376_, v_a_2395_, v_expectedInst_2377_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_dec_ref_known(v___x_2396_, 1);
v___x_2397_ = l_Lean_mkConst(v_declName_2376_, v___x_2391_);
v___x_2398_ = l_Lean_mkAppB(v___x_2397_, v_type_2373_, v_a_2395_);
v___x_2399_ = l_Lean_Meta_Sym_canon(v___x_2398_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2401_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v___x_2401_ = l_Lean_Meta_Sym_shareCommon(v_a_2400_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
return v___x_2401_;
}
else
{
return v___x_2399_;
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec(v_a_2395_);
lean_dec_ref_known(v___x_2391_, 2);
lean_dec(v_declName_2376_);
lean_dec_ref(v_type_2373_);
v_a_2402_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2396_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2396_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2391_, 2);
lean_dec_ref(v_expectedInst_2377_);
lean_dec(v_declName_2376_);
lean_dec_ref(v_type_2373_);
return v___x_2394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_type_2410_ = _args[0];
lean_object* v_u_2411_ = _args[1];
lean_object* v_instDeclName_2412_ = _args[2];
lean_object* v_declName_2413_ = _args[3];
lean_object* v_expectedInst_2414_ = _args[4];
lean_object* v___y_2415_ = _args[5];
lean_object* v___y_2416_ = _args[6];
lean_object* v___y_2417_ = _args[7];
lean_object* v___y_2418_ = _args[8];
lean_object* v___y_2419_ = _args[9];
lean_object* v___y_2420_ = _args[10];
lean_object* v___y_2421_ = _args[11];
lean_object* v___y_2422_ = _args[12];
lean_object* v___y_2423_ = _args[13];
lean_object* v___y_2424_ = _args[14];
lean_object* v___y_2425_ = _args[15];
lean_object* v___y_2426_ = _args[16];
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2410_, v_u_2411_, v_instDeclName_2412_, v_declName_2413_, v_expectedInst_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec(v___y_2415_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object* v_a_2428_, lean_object* v_s_2429_){
_start:
{
lean_object* v_toRing_2430_; lean_object* v_invFn_x3f_2431_; lean_object* v_semiringId_x3f_2432_; lean_object* v_commSemiringInst_2433_; lean_object* v_commRingInst_2434_; lean_object* v_noZeroDivInst_x3f_2435_; lean_object* v_fieldInst_x3f_2436_; lean_object* v_powIdentityInst_x3f_2437_; lean_object* v_denoteEntries_2438_; lean_object* v_nextId_2439_; lean_object* v_steps_2440_; lean_object* v_queue_2441_; lean_object* v_basis_2442_; lean_object* v_diseqs_2443_; uint8_t v_recheck_2444_; lean_object* v_invSet_2445_; lean_object* v_powIdentityVarCount_2446_; lean_object* v_numEq0_x3f_2447_; uint8_t v_numEq0Updated_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2480_; 
v_toRing_2430_ = lean_ctor_get(v_s_2429_, 0);
v_invFn_x3f_2431_ = lean_ctor_get(v_s_2429_, 1);
v_semiringId_x3f_2432_ = lean_ctor_get(v_s_2429_, 2);
v_commSemiringInst_2433_ = lean_ctor_get(v_s_2429_, 3);
v_commRingInst_2434_ = lean_ctor_get(v_s_2429_, 4);
v_noZeroDivInst_x3f_2435_ = lean_ctor_get(v_s_2429_, 5);
v_fieldInst_x3f_2436_ = lean_ctor_get(v_s_2429_, 6);
v_powIdentityInst_x3f_2437_ = lean_ctor_get(v_s_2429_, 7);
v_denoteEntries_2438_ = lean_ctor_get(v_s_2429_, 8);
v_nextId_2439_ = lean_ctor_get(v_s_2429_, 9);
v_steps_2440_ = lean_ctor_get(v_s_2429_, 10);
v_queue_2441_ = lean_ctor_get(v_s_2429_, 11);
v_basis_2442_ = lean_ctor_get(v_s_2429_, 12);
v_diseqs_2443_ = lean_ctor_get(v_s_2429_, 13);
v_recheck_2444_ = lean_ctor_get_uint8(v_s_2429_, sizeof(void*)*17);
v_invSet_2445_ = lean_ctor_get(v_s_2429_, 14);
v_powIdentityVarCount_2446_ = lean_ctor_get(v_s_2429_, 15);
v_numEq0_x3f_2447_ = lean_ctor_get(v_s_2429_, 16);
v_numEq0Updated_2448_ = lean_ctor_get_uint8(v_s_2429_, sizeof(void*)*17 + 1);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_s_2429_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2450_ = v_s_2429_;
v_isShared_2451_ = v_isSharedCheck_2480_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_numEq0_x3f_2447_);
lean_inc(v_powIdentityVarCount_2446_);
lean_inc(v_invSet_2445_);
lean_inc(v_diseqs_2443_);
lean_inc(v_basis_2442_);
lean_inc(v_queue_2441_);
lean_inc(v_steps_2440_);
lean_inc(v_nextId_2439_);
lean_inc(v_denoteEntries_2438_);
lean_inc(v_powIdentityInst_x3f_2437_);
lean_inc(v_fieldInst_x3f_2436_);
lean_inc(v_noZeroDivInst_x3f_2435_);
lean_inc(v_commRingInst_2434_);
lean_inc(v_commSemiringInst_2433_);
lean_inc(v_semiringId_x3f_2432_);
lean_inc(v_invFn_x3f_2431_);
lean_inc(v_toRing_2430_);
lean_dec(v_s_2429_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2480_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_id_2452_; lean_object* v_type_2453_; lean_object* v_u_2454_; lean_object* v_ringInst_2455_; lean_object* v_semiringInst_2456_; lean_object* v_charInst_x3f_2457_; lean_object* v_addFn_x3f_2458_; lean_object* v_mulFn_x3f_2459_; lean_object* v_subFn_x3f_2460_; lean_object* v_powFn_x3f_2461_; lean_object* v_intCastFn_x3f_2462_; lean_object* v_natCastFn_x3f_2463_; lean_object* v_one_x3f_2464_; lean_object* v_vars_2465_; lean_object* v_varMap_2466_; lean_object* v_denote_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2478_; 
v_id_2452_ = lean_ctor_get(v_toRing_2430_, 0);
v_type_2453_ = lean_ctor_get(v_toRing_2430_, 1);
v_u_2454_ = lean_ctor_get(v_toRing_2430_, 2);
v_ringInst_2455_ = lean_ctor_get(v_toRing_2430_, 3);
v_semiringInst_2456_ = lean_ctor_get(v_toRing_2430_, 4);
v_charInst_x3f_2457_ = lean_ctor_get(v_toRing_2430_, 5);
v_addFn_x3f_2458_ = lean_ctor_get(v_toRing_2430_, 6);
v_mulFn_x3f_2459_ = lean_ctor_get(v_toRing_2430_, 7);
v_subFn_x3f_2460_ = lean_ctor_get(v_toRing_2430_, 8);
v_powFn_x3f_2461_ = lean_ctor_get(v_toRing_2430_, 10);
v_intCastFn_x3f_2462_ = lean_ctor_get(v_toRing_2430_, 11);
v_natCastFn_x3f_2463_ = lean_ctor_get(v_toRing_2430_, 12);
v_one_x3f_2464_ = lean_ctor_get(v_toRing_2430_, 13);
v_vars_2465_ = lean_ctor_get(v_toRing_2430_, 14);
v_varMap_2466_ = lean_ctor_get(v_toRing_2430_, 15);
v_denote_2467_ = lean_ctor_get(v_toRing_2430_, 16);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_toRing_2430_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v_toRing_2430_, 9);
lean_dec(v_unused_2479_);
v___x_2469_ = v_toRing_2430_;
v_isShared_2470_ = v_isSharedCheck_2478_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_denote_2467_);
lean_inc(v_varMap_2466_);
lean_inc(v_vars_2465_);
lean_inc(v_one_x3f_2464_);
lean_inc(v_natCastFn_x3f_2463_);
lean_inc(v_intCastFn_x3f_2462_);
lean_inc(v_powFn_x3f_2461_);
lean_inc(v_subFn_x3f_2460_);
lean_inc(v_mulFn_x3f_2459_);
lean_inc(v_addFn_x3f_2458_);
lean_inc(v_charInst_x3f_2457_);
lean_inc(v_semiringInst_2456_);
lean_inc(v_ringInst_2455_);
lean_inc(v_u_2454_);
lean_inc(v_type_2453_);
lean_inc(v_id_2452_);
lean_dec(v_toRing_2430_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2478_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2471_, 0, v_a_2428_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 9, v___x_2471_);
v___x_2473_ = v___x_2469_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_id_2452_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_type_2453_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_u_2454_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_ringInst_2455_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_semiringInst_2456_);
lean_ctor_set(v_reuseFailAlloc_2477_, 5, v_charInst_x3f_2457_);
lean_ctor_set(v_reuseFailAlloc_2477_, 6, v_addFn_x3f_2458_);
lean_ctor_set(v_reuseFailAlloc_2477_, 7, v_mulFn_x3f_2459_);
lean_ctor_set(v_reuseFailAlloc_2477_, 8, v_subFn_x3f_2460_);
lean_ctor_set(v_reuseFailAlloc_2477_, 9, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2477_, 10, v_powFn_x3f_2461_);
lean_ctor_set(v_reuseFailAlloc_2477_, 11, v_intCastFn_x3f_2462_);
lean_ctor_set(v_reuseFailAlloc_2477_, 12, v_natCastFn_x3f_2463_);
lean_ctor_set(v_reuseFailAlloc_2477_, 13, v_one_x3f_2464_);
lean_ctor_set(v_reuseFailAlloc_2477_, 14, v_vars_2465_);
lean_ctor_set(v_reuseFailAlloc_2477_, 15, v_varMap_2466_);
lean_ctor_set(v_reuseFailAlloc_2477_, 16, v_denote_2467_);
v___x_2473_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2475_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2473_);
v___x_2475_ = v___x_2450_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_invFn_x3f_2431_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_semiringId_x3f_2432_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v_commSemiringInst_2433_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v_commRingInst_2434_);
lean_ctor_set(v_reuseFailAlloc_2476_, 5, v_noZeroDivInst_x3f_2435_);
lean_ctor_set(v_reuseFailAlloc_2476_, 6, v_fieldInst_x3f_2436_);
lean_ctor_set(v_reuseFailAlloc_2476_, 7, v_powIdentityInst_x3f_2437_);
lean_ctor_set(v_reuseFailAlloc_2476_, 8, v_denoteEntries_2438_);
lean_ctor_set(v_reuseFailAlloc_2476_, 9, v_nextId_2439_);
lean_ctor_set(v_reuseFailAlloc_2476_, 10, v_steps_2440_);
lean_ctor_set(v_reuseFailAlloc_2476_, 11, v_queue_2441_);
lean_ctor_set(v_reuseFailAlloc_2476_, 12, v_basis_2442_);
lean_ctor_set(v_reuseFailAlloc_2476_, 13, v_diseqs_2443_);
lean_ctor_set(v_reuseFailAlloc_2476_, 14, v_invSet_2445_);
lean_ctor_set(v_reuseFailAlloc_2476_, 15, v_powIdentityVarCount_2446_);
lean_ctor_set(v_reuseFailAlloc_2476_, 16, v_numEq0_x3f_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*17, v_recheck_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*17 + 1, v_numEq0Updated_2448_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2547_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2509_ = v___x_2506_;
v_isShared_2510_ = v_isSharedCheck_2547_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2506_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2547_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v_toRing_2511_; lean_object* v_negFn_x3f_2512_; 
v_toRing_2511_ = lean_ctor_get(v_a_2507_, 0);
lean_inc_ref(v_toRing_2511_);
lean_dec(v_a_2507_);
v_negFn_x3f_2512_ = lean_ctor_get(v_toRing_2511_, 9);
if (lean_obj_tag(v_negFn_x3f_2512_) == 1)
{
lean_object* v_val_2513_; lean_object* v___x_2515_; 
lean_inc_ref(v_negFn_x3f_2512_);
lean_dec_ref(v_toRing_2511_);
v_val_2513_ = lean_ctor_get(v_negFn_x3f_2512_, 0);
lean_inc(v_val_2513_);
lean_dec_ref_known(v_negFn_x3f_2512_, 1);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v_val_2513_);
v___x_2515_ = v___x_2509_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_val_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
else
{
lean_object* v_type_2517_; lean_object* v_u_2518_; lean_object* v_ringInst_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v_expectedInst_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_del_object(v___x_2509_);
v_type_2517_ = lean_ctor_get(v_toRing_2511_, 1);
lean_inc_ref_n(v_type_2517_, 2);
v_u_2518_ = lean_ctor_get(v_toRing_2511_, 2);
lean_inc_n(v_u_2518_, 2);
v_ringInst_2519_ = lean_ctor_get(v_toRing_2511_, 3);
lean_inc_ref(v_ringInst_2519_);
lean_dec_ref(v_toRing_2511_);
v___x_2520_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1));
v___x_2521_ = lean_box(0);
v___x_2522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2522_, 0, v_u_2518_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = l_Lean_mkConst(v___x_2520_, v___x_2522_);
v_expectedInst_2524_ = l_Lean_mkAppB(v___x_2523_, v_type_2517_, v_ringInst_2519_);
v___x_2525_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3));
v___x_2526_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5));
v___x_2527_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2517_, v_u_2518_, v___x_2525_, v___x_2526_, v_expectedInst_2524_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___f_2529_; lean_object* v___x_2530_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc_n(v_a_2528_, 2);
lean_dec_ref_known(v___x_2527_, 1);
v___f_2529_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_2529_, 0, v_a_2528_);
v___x_2530_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2529_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2537_ == 0)
{
lean_object* v_unused_2538_; 
v_unused_2538_ = lean_ctor_get(v___x_2530_, 0);
lean_dec(v_unused_2538_);
v___x_2532_ = v___x_2530_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_dec(v___x_2530_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v_a_2528_);
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2528_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v_a_2528_);
v_a_2539_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2530_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2530_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
else
{
return v___x_2527_;
}
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
v_a_2548_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2506_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2506_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec(v___y_2556_);
return v_res_2568_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_nat_to_int(v___x_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object* v_k_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v_toRing_2598_; lean_object* v_type_2599_; lean_object* v_u_2600_; lean_object* v_semiringInst_2601_; lean_object* v___x_2602_; lean_object* v_n_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v_toRing_2598_ = lean_ctor_get(v_a_2597_, 0);
lean_inc_ref(v_toRing_2598_);
lean_dec(v_a_2597_);
v_type_2599_ = lean_ctor_get(v_toRing_2598_, 1);
lean_inc_ref_n(v_type_2599_, 2);
v_u_2600_ = lean_ctor_get(v_toRing_2598_, 2);
lean_inc(v_u_2600_);
v_semiringInst_2601_ = lean_ctor_get(v_toRing_2598_, 4);
lean_inc_ref(v_semiringInst_2601_);
lean_dec_ref(v_toRing_2598_);
v___x_2602_ = lean_nat_abs(v_k_2583_);
v_n_2603_ = l_Lean_mkRawNatLit(v___x_2602_);
v___x_2604_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1));
v___x_2605_ = lean_box(0);
v___x_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2606_, 0, v_u_2600_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
lean_inc_ref(v___x_2606_);
v___x_2607_ = l_Lean_mkConst(v___x_2604_, v___x_2606_);
lean_inc_ref(v_n_2603_);
v___x_2608_ = l_Lean_mkAppB(v___x_2607_, v_type_2599_, v_n_2603_);
v___x_2609_ = lean_box(0);
v___x_2610_ = l_Lean_Meta_synthInstance_x3f(v___x_2608_, v___x_2609_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2650_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2650_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2650_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v_ofNatInst_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; 
if (lean_obj_tag(v_a_2611_) == 1)
{
lean_object* v_val_2646_; 
lean_dec_ref(v_semiringInst_2601_);
v_val_2646_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_val_2646_);
lean_dec_ref_known(v_a_2611_, 1);
v_ofNatInst_2616_ = v_val_2646_;
v___y_2617_ = v___y_2584_;
v___y_2618_ = v___y_2585_;
v___y_2619_ = v___y_2586_;
v___y_2620_ = v___y_2587_;
v___y_2621_ = v___y_2588_;
v___y_2622_ = v___y_2589_;
v___y_2623_ = v___y_2590_;
v___y_2624_ = v___y_2591_;
v___y_2625_ = v___y_2592_;
v___y_2626_ = v___y_2593_;
v___y_2627_ = v___y_2594_;
goto v___jp_2615_;
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_dec(v_a_2611_);
v___x_2647_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5));
lean_inc_ref(v___x_2606_);
v___x_2648_ = l_Lean_mkConst(v___x_2647_, v___x_2606_);
lean_inc_ref(v_n_2603_);
lean_inc_ref(v_type_2599_);
v___x_2649_ = l_Lean_mkApp3(v___x_2648_, v_type_2599_, v_semiringInst_2601_, v_n_2603_);
v_ofNatInst_2616_ = v___x_2649_;
v___y_2617_ = v___y_2584_;
v___y_2618_ = v___y_2585_;
v___y_2619_ = v___y_2586_;
v___y_2620_ = v___y_2587_;
v___y_2621_ = v___y_2588_;
v___y_2622_ = v___y_2589_;
v___y_2623_ = v___y_2590_;
v___y_2624_ = v___y_2591_;
v___y_2625_ = v___y_2592_;
v___y_2626_ = v___y_2593_;
v___y_2627_ = v___y_2594_;
goto v___jp_2615_;
}
v___jp_2615_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v_n_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2628_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3));
v___x_2629_ = l_Lean_mkConst(v___x_2628_, v___x_2606_);
v_n_2630_ = l_Lean_mkApp3(v___x_2629_, v_type_2599_, v_n_2603_, v_ofNatInst_2616_);
v___x_2631_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4);
v___x_2632_ = lean_int_dec_lt(v_k_2583_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2634_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v_n_2630_);
v___x_2634_ = v___x_2613_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_n_2630_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
else
{
lean_object* v___x_2636_; 
lean_del_object(v___x_2613_);
v___x_2636_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2645_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2645_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2645_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2641_; lean_object* v___x_2643_; 
v___x_2641_ = l_Lean_Expr_app___override(v_a_2637_, v_n_2630_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v___x_2641_);
v___x_2643_ = v___x_2639_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
else
{
lean_dec_ref(v_n_2630_);
return v___x_2636_;
}
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec_ref_known(v___x_2606_, 2);
lean_dec_ref(v_n_2603_);
lean_dec_ref(v_semiringInst_2601_);
lean_dec_ref(v_type_2599_);
v_a_2651_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2610_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2610_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_a_2659_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2596_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2596_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object* v_k_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec(v_k_2667_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object* v_a_2681_, lean_object* v_s_2682_){
_start:
{
lean_object* v_toRing_2683_; lean_object* v_invFn_x3f_2684_; lean_object* v_semiringId_x3f_2685_; lean_object* v_commSemiringInst_2686_; lean_object* v_commRingInst_2687_; lean_object* v_noZeroDivInst_x3f_2688_; lean_object* v_fieldInst_x3f_2689_; lean_object* v_powIdentityInst_x3f_2690_; lean_object* v_denoteEntries_2691_; lean_object* v_nextId_2692_; lean_object* v_steps_2693_; lean_object* v_queue_2694_; lean_object* v_basis_2695_; lean_object* v_diseqs_2696_; uint8_t v_recheck_2697_; lean_object* v_invSet_2698_; lean_object* v_powIdentityVarCount_2699_; lean_object* v_numEq0_x3f_2700_; uint8_t v_numEq0Updated_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2733_; 
v_toRing_2683_ = lean_ctor_get(v_s_2682_, 0);
v_invFn_x3f_2684_ = lean_ctor_get(v_s_2682_, 1);
v_semiringId_x3f_2685_ = lean_ctor_get(v_s_2682_, 2);
v_commSemiringInst_2686_ = lean_ctor_get(v_s_2682_, 3);
v_commRingInst_2687_ = lean_ctor_get(v_s_2682_, 4);
v_noZeroDivInst_x3f_2688_ = lean_ctor_get(v_s_2682_, 5);
v_fieldInst_x3f_2689_ = lean_ctor_get(v_s_2682_, 6);
v_powIdentityInst_x3f_2690_ = lean_ctor_get(v_s_2682_, 7);
v_denoteEntries_2691_ = lean_ctor_get(v_s_2682_, 8);
v_nextId_2692_ = lean_ctor_get(v_s_2682_, 9);
v_steps_2693_ = lean_ctor_get(v_s_2682_, 10);
v_queue_2694_ = lean_ctor_get(v_s_2682_, 11);
v_basis_2695_ = lean_ctor_get(v_s_2682_, 12);
v_diseqs_2696_ = lean_ctor_get(v_s_2682_, 13);
v_recheck_2697_ = lean_ctor_get_uint8(v_s_2682_, sizeof(void*)*17);
v_invSet_2698_ = lean_ctor_get(v_s_2682_, 14);
v_powIdentityVarCount_2699_ = lean_ctor_get(v_s_2682_, 15);
v_numEq0_x3f_2700_ = lean_ctor_get(v_s_2682_, 16);
v_numEq0Updated_2701_ = lean_ctor_get_uint8(v_s_2682_, sizeof(void*)*17 + 1);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_s_2682_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2703_ = v_s_2682_;
v_isShared_2704_ = v_isSharedCheck_2733_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_numEq0_x3f_2700_);
lean_inc(v_powIdentityVarCount_2699_);
lean_inc(v_invSet_2698_);
lean_inc(v_diseqs_2696_);
lean_inc(v_basis_2695_);
lean_inc(v_queue_2694_);
lean_inc(v_steps_2693_);
lean_inc(v_nextId_2692_);
lean_inc(v_denoteEntries_2691_);
lean_inc(v_powIdentityInst_x3f_2690_);
lean_inc(v_fieldInst_x3f_2689_);
lean_inc(v_noZeroDivInst_x3f_2688_);
lean_inc(v_commRingInst_2687_);
lean_inc(v_commSemiringInst_2686_);
lean_inc(v_semiringId_x3f_2685_);
lean_inc(v_invFn_x3f_2684_);
lean_inc(v_toRing_2683_);
lean_dec(v_s_2682_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2733_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v_id_2705_; lean_object* v_type_2706_; lean_object* v_u_2707_; lean_object* v_ringInst_2708_; lean_object* v_semiringInst_2709_; lean_object* v_charInst_x3f_2710_; lean_object* v_addFn_x3f_2711_; lean_object* v_mulFn_x3f_2712_; lean_object* v_subFn_x3f_2713_; lean_object* v_negFn_x3f_2714_; lean_object* v_intCastFn_x3f_2715_; lean_object* v_natCastFn_x3f_2716_; lean_object* v_one_x3f_2717_; lean_object* v_vars_2718_; lean_object* v_varMap_2719_; lean_object* v_denote_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2731_; 
v_id_2705_ = lean_ctor_get(v_toRing_2683_, 0);
v_type_2706_ = lean_ctor_get(v_toRing_2683_, 1);
v_u_2707_ = lean_ctor_get(v_toRing_2683_, 2);
v_ringInst_2708_ = lean_ctor_get(v_toRing_2683_, 3);
v_semiringInst_2709_ = lean_ctor_get(v_toRing_2683_, 4);
v_charInst_x3f_2710_ = lean_ctor_get(v_toRing_2683_, 5);
v_addFn_x3f_2711_ = lean_ctor_get(v_toRing_2683_, 6);
v_mulFn_x3f_2712_ = lean_ctor_get(v_toRing_2683_, 7);
v_subFn_x3f_2713_ = lean_ctor_get(v_toRing_2683_, 8);
v_negFn_x3f_2714_ = lean_ctor_get(v_toRing_2683_, 9);
v_intCastFn_x3f_2715_ = lean_ctor_get(v_toRing_2683_, 11);
v_natCastFn_x3f_2716_ = lean_ctor_get(v_toRing_2683_, 12);
v_one_x3f_2717_ = lean_ctor_get(v_toRing_2683_, 13);
v_vars_2718_ = lean_ctor_get(v_toRing_2683_, 14);
v_varMap_2719_ = lean_ctor_get(v_toRing_2683_, 15);
v_denote_2720_ = lean_ctor_get(v_toRing_2683_, 16);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_toRing_2683_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; 
v_unused_2732_ = lean_ctor_get(v_toRing_2683_, 10);
lean_dec(v_unused_2732_);
v___x_2722_ = v_toRing_2683_;
v_isShared_2723_ = v_isSharedCheck_2731_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_denote_2720_);
lean_inc(v_varMap_2719_);
lean_inc(v_vars_2718_);
lean_inc(v_one_x3f_2717_);
lean_inc(v_natCastFn_x3f_2716_);
lean_inc(v_intCastFn_x3f_2715_);
lean_inc(v_negFn_x3f_2714_);
lean_inc(v_subFn_x3f_2713_);
lean_inc(v_mulFn_x3f_2712_);
lean_inc(v_addFn_x3f_2711_);
lean_inc(v_charInst_x3f_2710_);
lean_inc(v_semiringInst_2709_);
lean_inc(v_ringInst_2708_);
lean_inc(v_u_2707_);
lean_inc(v_type_2706_);
lean_inc(v_id_2705_);
lean_dec(v_toRing_2683_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2731_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v___x_2726_; 
v___x_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2724_, 0, v_a_2681_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 10, v___x_2724_);
v___x_2726_ = v___x_2722_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_id_2705_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_type_2706_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_u_2707_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v_ringInst_2708_);
lean_ctor_set(v_reuseFailAlloc_2730_, 4, v_semiringInst_2709_);
lean_ctor_set(v_reuseFailAlloc_2730_, 5, v_charInst_x3f_2710_);
lean_ctor_set(v_reuseFailAlloc_2730_, 6, v_addFn_x3f_2711_);
lean_ctor_set(v_reuseFailAlloc_2730_, 7, v_mulFn_x3f_2712_);
lean_ctor_set(v_reuseFailAlloc_2730_, 8, v_subFn_x3f_2713_);
lean_ctor_set(v_reuseFailAlloc_2730_, 9, v_negFn_x3f_2714_);
lean_ctor_set(v_reuseFailAlloc_2730_, 10, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2730_, 11, v_intCastFn_x3f_2715_);
lean_ctor_set(v_reuseFailAlloc_2730_, 12, v_natCastFn_x3f_2716_);
lean_ctor_set(v_reuseFailAlloc_2730_, 13, v_one_x3f_2717_);
lean_ctor_set(v_reuseFailAlloc_2730_, 14, v_vars_2718_);
lean_ctor_set(v_reuseFailAlloc_2730_, 15, v_varMap_2719_);
lean_ctor_set(v_reuseFailAlloc_2730_, 16, v_denote_2720_);
v___x_2726_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2728_; 
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v___x_2726_);
v___x_2728_ = v___x_2703_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_invFn_x3f_2684_);
lean_ctor_set(v_reuseFailAlloc_2729_, 2, v_semiringId_x3f_2685_);
lean_ctor_set(v_reuseFailAlloc_2729_, 3, v_commSemiringInst_2686_);
lean_ctor_set(v_reuseFailAlloc_2729_, 4, v_commRingInst_2687_);
lean_ctor_set(v_reuseFailAlloc_2729_, 5, v_noZeroDivInst_x3f_2688_);
lean_ctor_set(v_reuseFailAlloc_2729_, 6, v_fieldInst_x3f_2689_);
lean_ctor_set(v_reuseFailAlloc_2729_, 7, v_powIdentityInst_x3f_2690_);
lean_ctor_set(v_reuseFailAlloc_2729_, 8, v_denoteEntries_2691_);
lean_ctor_set(v_reuseFailAlloc_2729_, 9, v_nextId_2692_);
lean_ctor_set(v_reuseFailAlloc_2729_, 10, v_steps_2693_);
lean_ctor_set(v_reuseFailAlloc_2729_, 11, v_queue_2694_);
lean_ctor_set(v_reuseFailAlloc_2729_, 12, v_basis_2695_);
lean_ctor_set(v_reuseFailAlloc_2729_, 13, v_diseqs_2696_);
lean_ctor_set(v_reuseFailAlloc_2729_, 14, v_invSet_2698_);
lean_ctor_set(v_reuseFailAlloc_2729_, 15, v_powIdentityVarCount_2699_);
lean_ctor_set(v_reuseFailAlloc_2729_, 16, v_numEq0_x3f_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2729_, sizeof(void*)*17, v_recheck_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2729_, sizeof(void*)*17 + 1, v_numEq0Updated_2701_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_unsigned_to_nat(0u);
v___x_2738_ = l_Lean_Level_ofNat(v___x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(lean_object* v_u_2749_, lean_object* v_type_2750_, lean_object* v_semiringInst_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2764_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1));
v___x_2765_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2);
v___x_2766_ = lean_box(0);
lean_inc(v_u_2749_);
v___x_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_u_2749_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
lean_inc_ref(v___x_2767_);
v___x_2768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2765_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2769_, 0, v_u_2749_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
lean_inc_ref(v___x_2769_);
v___x_2770_ = l_Lean_mkConst(v___x_2764_, v___x_2769_);
v___x_2771_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2750_, 2);
v___x_2772_ = l_Lean_mkApp3(v___x_2770_, v_type_2750_, v___x_2771_, v_type_2750_);
v___x_2773_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2772_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v_inst_x27_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc_n(v_a_2774_, 2);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4));
v___x_2776_ = l_Lean_mkConst(v___x_2775_, v___x_2767_);
lean_inc_ref(v_type_2750_);
v_inst_x27_2777_ = l_Lean_mkAppB(v___x_2776_, v_type_2750_, v_semiringInst_2751_);
v___x_2778_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6));
v___x_2779_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_2778_, v_a_2774_, v_inst_x27_2777_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
lean_dec_ref_known(v___x_2779_, 1);
v___x_2780_ = l_Lean_mkConst(v___x_2778_, v___x_2769_);
lean_inc_ref(v_type_2750_);
v___x_2781_ = l_Lean_mkApp4(v___x_2780_, v_type_2750_, v___x_2771_, v_type_2750_, v_a_2774_);
v___x_2782_ = l_Lean_Meta_Sym_canon(v___x_2781_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v___x_2784_ = l_Lean_Meta_Sym_shareCommon(v_a_2783_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
return v___x_2784_;
}
else
{
return v___x_2782_;
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec(v_a_2774_);
lean_dec_ref_known(v___x_2769_, 2);
lean_dec_ref(v_type_2750_);
v_a_2785_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2779_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2779_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2769_, 2);
lean_dec_ref_known(v___x_2767_, 2);
lean_dec_ref(v_semiringInst_2751_);
lean_dec_ref(v_type_2750_);
return v___x_2773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___boxed(lean_object* v_u_2793_, lean_object* v_type_2794_, lean_object* v_semiringInst_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2793_, v_type_2794_, v_semiringInst_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec(v___y_2796_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2855_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2855_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2855_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v_toRing_2826_; lean_object* v_powFn_x3f_2827_; 
v_toRing_2826_ = lean_ctor_get(v_a_2822_, 0);
lean_inc_ref(v_toRing_2826_);
lean_dec(v_a_2822_);
v_powFn_x3f_2827_ = lean_ctor_get(v_toRing_2826_, 10);
if (lean_obj_tag(v_powFn_x3f_2827_) == 1)
{
lean_object* v_val_2828_; lean_object* v___x_2830_; 
lean_inc_ref(v_powFn_x3f_2827_);
lean_dec_ref(v_toRing_2826_);
v_val_2828_ = lean_ctor_get(v_powFn_x3f_2827_, 0);
lean_inc(v_val_2828_);
lean_dec_ref_known(v_powFn_x3f_2827_, 1);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v_val_2828_);
v___x_2830_ = v___x_2824_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_val_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
else
{
lean_object* v_type_2832_; lean_object* v_u_2833_; lean_object* v_semiringInst_2834_; lean_object* v___x_2835_; 
lean_del_object(v___x_2824_);
v_type_2832_ = lean_ctor_get(v_toRing_2826_, 1);
lean_inc_ref(v_type_2832_);
v_u_2833_ = lean_ctor_get(v_toRing_2826_, 2);
lean_inc(v_u_2833_);
v_semiringInst_2834_ = lean_ctor_get(v_toRing_2826_, 4);
lean_inc_ref(v_semiringInst_2834_);
lean_dec_ref(v_toRing_2826_);
v___x_2835_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2833_, v_type_2832_, v_semiringInst_2834_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___f_2837_; lean_object* v___x_2838_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc_n(v_a_2836_, 2);
lean_dec_ref_known(v___x_2835_, 1);
v___f_2837_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_2837_, 0, v_a_2836_);
v___x_2838_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2837_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v___x_2838_, 0);
lean_dec(v_unused_2846_);
v___x_2840_ = v___x_2838_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_dec(v___x_2838_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v_a_2836_);
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2836_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_a_2836_);
v_a_2847_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2838_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2838_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
return v___x_2835_;
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
v_a_2856_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2821_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2821_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
return v_res_2876_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2));
v___x_2881_ = lean_unsigned_to_nat(39u);
v___x_2882_ = lean_unsigned_to_nat(159u);
v___x_2883_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1));
v___x_2884_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0));
v___x_2885_ = l_mkPanicMessageWithDecl(v___x_2884_, v___x_2883_, v___x_2882_, v___x_2881_, v___x_2880_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
switch(lean_obj_tag(v_a_2886_))
{
case 0:
{
lean_object* v_k_2899_; lean_object* v___x_2900_; 
v_k_2899_ = lean_ctor_get(v_a_2886_, 0);
lean_inc(v_k_2899_);
lean_dec_ref_known(v_a_2886_, 1);
v___x_2900_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2899_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
lean_dec(v_k_2899_);
return v___x_2900_;
}
case 1:
{
lean_object* v_k_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_k_2901_ = lean_ctor_get(v_a_2886_, 0);
lean_inc(v_k_2901_);
lean_dec_ref_known(v_a_2886_, 1);
v___x_2902_ = lean_nat_to_int(v_k_2901_);
v___x_2903_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_2902_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
lean_dec(v___x_2902_);
return v___x_2903_;
}
case 3:
{
lean_object* v_i_2904_; lean_object* v___x_2905_; 
v_i_2904_ = lean_ctor_get(v_a_2886_, 0);
lean_inc(v_i_2904_);
lean_dec_ref_known(v_a_2886_, 1);
v___x_2905_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2925_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2910_ = v___x_2907_;
v_isShared_2911_ = v_isSharedCheck_2925_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2907_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2925_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___y_2913_; lean_object* v_toSemiring_2918_; lean_object* v_vars_2919_; lean_object* v_size_2920_; lean_object* v___x_2921_; uint8_t v___x_2922_; 
v_toSemiring_2918_ = lean_ctor_get(v_a_2908_, 0);
lean_inc_ref(v_toSemiring_2918_);
lean_dec(v_a_2908_);
v_vars_2919_ = lean_ctor_get(v_toSemiring_2918_, 9);
lean_inc_ref(v_vars_2919_);
lean_dec_ref(v_toSemiring_2918_);
v_size_2920_ = lean_ctor_get(v_vars_2919_, 2);
v___x_2921_ = l_Lean_instInhabitedExpr;
v___x_2922_ = lean_nat_dec_lt(v_i_2904_, v_size_2920_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; 
lean_dec_ref(v_vars_2919_);
lean_dec(v_i_2904_);
v___x_2923_ = l_outOfBounds___redArg(v___x_2921_);
v___y_2913_ = v___x_2923_;
goto v___jp_2912_;
}
else
{
lean_object* v___x_2924_; 
v___x_2924_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2921_, v_vars_2919_, v_i_2904_);
lean_dec(v_i_2904_);
lean_dec_ref(v_vars_2919_);
v___y_2913_ = v___x_2924_;
goto v___jp_2912_;
}
v___jp_2912_:
{
lean_object* v___x_2914_; lean_object* v___x_2916_; 
v___x_2914_ = l_Lean_Expr_app___override(v_a_2906_, v___y_2913_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 0, v___x_2914_);
v___x_2916_ = v___x_2910_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_a_2906_);
lean_dec(v_i_2904_);
v_a_2926_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2907_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2907_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
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
lean_dec(v_i_2904_);
return v___x_2905_;
}
}
case 5:
{
lean_object* v_a_2934_; lean_object* v_b_2935_; lean_object* v___x_2936_; 
v_a_2934_ = lean_ctor_get(v_a_2886_, 0);
lean_inc_ref(v_a_2934_);
v_b_2935_ = lean_ctor_get(v_a_2886_, 1);
lean_inc_ref(v_b_2935_);
lean_dec_ref_known(v_a_2886_, 2);
v___x_2936_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2938_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v___x_2938_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2934_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2935_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2949_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2949_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2949_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2945_ = l_Lean_mkAppB(v_a_2937_, v_a_2939_, v_a_2941_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2945_);
v___x_2947_ = v___x_2943_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
else
{
lean_dec(v_a_2939_);
lean_dec(v_a_2937_);
return v___x_2940_;
}
}
else
{
lean_dec(v_a_2937_);
lean_dec_ref(v_b_2935_);
return v___x_2938_;
}
}
else
{
lean_dec_ref(v_b_2935_);
lean_dec_ref(v_a_2934_);
return v___x_2936_;
}
}
case 7:
{
lean_object* v_a_2950_; lean_object* v_b_2951_; lean_object* v___x_2952_; 
v_a_2950_ = lean_ctor_get(v_a_2886_, 0);
lean_inc_ref(v_a_2950_);
v_b_2951_ = lean_ctor_get(v_a_2886_, 1);
lean_inc_ref(v_b_2951_);
lean_dec_ref_known(v_a_2886_, 2);
v___x_2952_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2954_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v___x_2954_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2950_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2956_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2954_, 1);
v___x_2956_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2951_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
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
case 8:
{
lean_object* v_a_2966_; lean_object* v_k_2967_; lean_object* v___x_2968_; 
v_a_2966_ = lean_ctor_get(v_a_2886_, 0);
lean_inc_ref(v_a_2966_);
v_k_2967_ = lean_ctor_get(v_a_2886_, 1);
lean_inc(v_k_2967_);
lean_dec_ref_known(v_a_2886_, 2);
v___x_2968_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2970_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 1);
v___x_2970_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2966_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2980_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2973_ = v___x_2970_;
v_isShared_2974_ = v_isSharedCheck_2980_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2970_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2980_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2975_ = l_Lean_mkNatLit(v_k_2967_);
v___x_2976_ = l_Lean_mkAppB(v_a_2969_, v_a_2971_, v___x_2975_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v___x_2976_);
v___x_2978_ = v___x_2973_;
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
lean_dec(v_a_2969_);
lean_dec(v_k_2967_);
return v___x_2970_;
}
}
else
{
lean_dec(v_k_2967_);
lean_dec_ref(v_a_2966_);
return v___x_2968_;
}
}
default: 
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_dec_ref(v_a_2886_);
v___x_2981_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
v___x_2982_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___x_2981_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
return v___x_2982_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec(v_a_2984_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(lean_object* v_type_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_2997_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(lean_object* v_type_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(v_type_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec(v___y_3013_);
lean_dec(v___y_3012_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object* v_e_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_e_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
v___x_3040_ = l_Lean_Meta_Sym_shareCommon(v_a_3039_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
return v___x_3040_;
}
else
{
return v___x_3038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object* v_e_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(v_e_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec(v_a_3043_);
lean_dec(v_a_3042_);
return v_res_3054_;
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
