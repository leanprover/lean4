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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_104_);
v___x_106_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_105_, v___y_98_);
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
v___x_134_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_e_121_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
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
lean_dec_ref(v___x_392_);
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
lean_dec_ref(v___x_500_);
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
lean_dec_ref(v_toQFn_x3f_643_);
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
lean_dec_ref(v___x_657_);
v___x_659_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_658_, v_a_610_);
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
lean_dec_ref(v___y_617_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(lean_object* v_u_690_, lean_object* v_type_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_add_701_; lean_object* v___x_702_; 
v___x_697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1));
v___x_698_ = lean_box(0);
v___x_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_699_, 0, v_u_690_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
lean_inc_ref(v___x_699_);
v___x_700_ = l_Lean_mkConst(v___x_697_, v___x_699_);
lean_inc_ref(v_type_691_);
v_add_701_ = l_Lean_Expr_app___override(v___x_700_, v_type_691_);
v___x_702_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_add_701_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_716_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_716_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_716_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_716_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
if (lean_obj_tag(v_a_703_) == 1)
{
lean_object* v_val_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_del_object(v___x_705_);
v_val_707_ = lean_ctor_get(v_a_703_, 0);
lean_inc(v_val_707_);
lean_dec_ref(v_a_703_);
v___x_708_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3));
v___x_709_ = l_Lean_mkConst(v___x_708_, v___x_699_);
v___x_710_ = l_Lean_mkAppB(v___x_709_, v_type_691_, v_val_707_);
v___x_711_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_710_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
return v___x_711_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_714_; 
lean_dec(v_a_703_);
lean_dec_ref(v___x_699_);
lean_dec_ref(v_type_691_);
v___x_712_ = lean_box(0);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_712_);
v___x_714_ = v___x_705_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_dec_ref(v___x_699_);
lean_dec_ref(v_type_691_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___boxed(lean_object* v_u_717_, lean_object* v_type_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_717_, v_type_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(lean_object* v_u_725_, lean_object* v_type_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_725_, v_type_726_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___boxed(lean_object* v_u_739_, lean_object* v_type_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(v_u_739_, v_type_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec(v_a_741_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_s_755_){
_start:
{
lean_object* v_rings_756_; lean_object* v_typeIdOf_757_; lean_object* v_exprToRingId_758_; lean_object* v_semirings_759_; lean_object* v_stypeIdOf_760_; lean_object* v_exprToSemiringId_761_; lean_object* v_ncRings_762_; lean_object* v_exprToNCRingId_763_; lean_object* v_nctypeIdOf_764_; lean_object* v_ncSemirings_765_; lean_object* v_exprToNCSemiringId_766_; lean_object* v_ncstypeIdOf_767_; lean_object* v_steps_768_; uint8_t v_reportedMaxDegreeIssue_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_rings_756_ = lean_ctor_get(v_s_755_, 0);
v_typeIdOf_757_ = lean_ctor_get(v_s_755_, 1);
v_exprToRingId_758_ = lean_ctor_get(v_s_755_, 2);
v_semirings_759_ = lean_ctor_get(v_s_755_, 3);
v_stypeIdOf_760_ = lean_ctor_get(v_s_755_, 4);
v_exprToSemiringId_761_ = lean_ctor_get(v_s_755_, 5);
v_ncRings_762_ = lean_ctor_get(v_s_755_, 6);
v_exprToNCRingId_763_ = lean_ctor_get(v_s_755_, 7);
v_nctypeIdOf_764_ = lean_ctor_get(v_s_755_, 8);
v_ncSemirings_765_ = lean_ctor_get(v_s_755_, 9);
v_exprToNCSemiringId_766_ = lean_ctor_get(v_s_755_, 10);
v_ncstypeIdOf_767_ = lean_ctor_get(v_s_755_, 11);
v_steps_768_ = lean_ctor_get(v_s_755_, 12);
v_reportedMaxDegreeIssue_769_ = lean_ctor_get_uint8(v_s_755_, sizeof(void*)*13);
v___x_770_ = lean_array_get_size(v_semirings_759_);
v___x_771_ = lean_nat_dec_lt(v_a_753_, v___x_770_);
if (v___x_771_ == 0)
{
lean_dec(v_a_754_);
return v_s_755_;
}
else
{
lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_795_; 
lean_inc(v_steps_768_);
lean_inc_ref(v_ncstypeIdOf_767_);
lean_inc_ref(v_exprToNCSemiringId_766_);
lean_inc_ref(v_ncSemirings_765_);
lean_inc_ref(v_nctypeIdOf_764_);
lean_inc_ref(v_exprToNCRingId_763_);
lean_inc_ref(v_ncRings_762_);
lean_inc_ref(v_exprToSemiringId_761_);
lean_inc_ref(v_stypeIdOf_760_);
lean_inc_ref(v_semirings_759_);
lean_inc_ref(v_exprToRingId_758_);
lean_inc_ref(v_typeIdOf_757_);
lean_inc_ref(v_rings_756_);
v_isSharedCheck_795_ = !lean_is_exclusive(v_s_755_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; lean_object* v_unused_797_; lean_object* v_unused_798_; lean_object* v_unused_799_; lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; lean_object* v_unused_804_; lean_object* v_unused_805_; lean_object* v_unused_806_; lean_object* v_unused_807_; lean_object* v_unused_808_; 
v_unused_796_ = lean_ctor_get(v_s_755_, 12);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_s_755_, 11);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_s_755_, 10);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_s_755_, 9);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_s_755_, 8);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_s_755_, 7);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_s_755_, 6);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_s_755_, 5);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_s_755_, 4);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_s_755_, 3);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_s_755_, 2);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_s_755_, 1);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_s_755_, 0);
lean_dec(v_unused_808_);
v___x_773_ = v_s_755_;
v_isShared_774_ = v_isSharedCheck_795_;
goto v_resetjp_772_;
}
else
{
lean_dec(v_s_755_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_795_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_v_775_; lean_object* v_toSemiring_776_; lean_object* v_ringId_777_; lean_object* v_commSemiringInst_778_; lean_object* v_toQFn_x3f_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_793_; 
v_v_775_ = lean_array_fget(v_semirings_759_, v_a_753_);
v_toSemiring_776_ = lean_ctor_get(v_v_775_, 0);
v_ringId_777_ = lean_ctor_get(v_v_775_, 1);
v_commSemiringInst_778_ = lean_ctor_get(v_v_775_, 2);
v_toQFn_x3f_779_ = lean_ctor_get(v_v_775_, 4);
v_isSharedCheck_793_ = !lean_is_exclusive(v_v_775_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_v_775_, 3);
lean_dec(v_unused_794_);
v___x_781_ = v_v_775_;
v_isShared_782_ = v_isSharedCheck_793_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_toQFn_x3f_779_);
lean_inc(v_commSemiringInst_778_);
lean_inc(v_ringId_777_);
lean_inc(v_toSemiring_776_);
lean_dec(v_v_775_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_793_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v_xs_x27_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_783_ = lean_box(0);
v_xs_x27_784_ = lean_array_fset(v_semirings_759_, v_a_753_, v___x_783_);
v___x_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_785_, 0, v_a_754_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 3, v___x_785_);
v___x_787_ = v___x_781_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_toSemiring_776_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_ringId_777_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_commSemiringInst_778_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v_toQFn_x3f_779_);
v___x_787_ = v_reuseFailAlloc_792_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_array_fset(v_xs_x27_784_, v_a_753_, v___x_787_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 3, v___x_788_);
v___x_790_ = v___x_773_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_rings_756_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_typeIdOf_757_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_exprToRingId_758_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_stypeIdOf_760_);
lean_ctor_set(v_reuseFailAlloc_791_, 5, v_exprToSemiringId_761_);
lean_ctor_set(v_reuseFailAlloc_791_, 6, v_ncRings_762_);
lean_ctor_set(v_reuseFailAlloc_791_, 7, v_exprToNCRingId_763_);
lean_ctor_set(v_reuseFailAlloc_791_, 8, v_nctypeIdOf_764_);
lean_ctor_set(v_reuseFailAlloc_791_, 9, v_ncSemirings_765_);
lean_ctor_set(v_reuseFailAlloc_791_, 10, v_exprToNCSemiringId_766_);
lean_ctor_set(v_reuseFailAlloc_791_, 11, v_ncstypeIdOf_767_);
lean_ctor_set(v_reuseFailAlloc_791_, 12, v_steps_768_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*13, v_reportedMaxDegreeIssue_769_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed(lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_s_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(v_a_809_, v_a_810_, v_s_811_);
lean_dec(v_a_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_859_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_859_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_859_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_859_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_addRightCancelInst_x3f_830_; 
v_addRightCancelInst_x3f_830_ = lean_ctor_get(v_a_826_, 3);
if (lean_obj_tag(v_addRightCancelInst_x3f_830_) == 1)
{
lean_object* v_val_831_; lean_object* v___x_833_; 
lean_inc_ref(v_addRightCancelInst_x3f_830_);
lean_dec(v_a_826_);
v_val_831_ = lean_ctor_get(v_addRightCancelInst_x3f_830_, 0);
lean_inc(v_val_831_);
lean_dec_ref(v_addRightCancelInst_x3f_830_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_val_831_);
v___x_833_ = v___x_828_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_val_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v_toSemiring_835_; lean_object* v_type_836_; lean_object* v_u_837_; lean_object* v___x_838_; 
lean_del_object(v___x_828_);
v_toSemiring_835_ = lean_ctor_get(v_a_826_, 0);
lean_inc_ref(v_toSemiring_835_);
lean_dec(v_a_826_);
v_type_836_ = lean_ctor_get(v_toSemiring_835_, 1);
lean_inc_ref(v_type_836_);
v_u_837_ = lean_ctor_get(v_toSemiring_835_, 2);
lean_inc(v_u_837_);
lean_dec_ref(v_toSemiring_835_);
v___x_838_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_837_, v_type_836_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc_n(v_a_839_, 2);
lean_dec_ref(v___x_838_);
lean_inc(v_a_813_);
v___f_840_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_840_, 0, v_a_813_);
lean_closure_set(v___f_840_, 1, v_a_839_);
v___x_841_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_842_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_841_, v___f_840_, v_a_814_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v___x_842_, 0);
lean_dec(v_unused_850_);
v___x_844_ = v___x_842_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_dec(v___x_842_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v_a_839_);
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_839_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v_a_839_);
v_a_851_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_842_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_842_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
v_a_860_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_825_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_825_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___boxed(lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec(v_a_869_);
lean_dec(v_a_868_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_881_, lean_object* v_s_882_){
_start:
{
lean_object* v_id_883_; lean_object* v_type_884_; lean_object* v_u_885_; lean_object* v_semiringInst_886_; lean_object* v_mulFn_x3f_887_; lean_object* v_powFn_x3f_888_; lean_object* v_natCastFn_x3f_889_; lean_object* v_denote_890_; lean_object* v_vars_891_; lean_object* v_varMap_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_900_; 
v_id_883_ = lean_ctor_get(v_s_882_, 0);
v_type_884_ = lean_ctor_get(v_s_882_, 1);
v_u_885_ = lean_ctor_get(v_s_882_, 2);
v_semiringInst_886_ = lean_ctor_get(v_s_882_, 3);
v_mulFn_x3f_887_ = lean_ctor_get(v_s_882_, 5);
v_powFn_x3f_888_ = lean_ctor_get(v_s_882_, 6);
v_natCastFn_x3f_889_ = lean_ctor_get(v_s_882_, 7);
v_denote_890_ = lean_ctor_get(v_s_882_, 8);
v_vars_891_ = lean_ctor_get(v_s_882_, 9);
v_varMap_892_ = lean_ctor_get(v_s_882_, 10);
v_isSharedCheck_900_ = !lean_is_exclusive(v_s_882_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v_s_882_, 4);
lean_dec(v_unused_901_);
v___x_894_ = v_s_882_;
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_varMap_892_);
lean_inc(v_vars_891_);
lean_inc(v_denote_890_);
lean_inc(v_natCastFn_x3f_889_);
lean_inc(v_powFn_x3f_888_);
lean_inc(v_mulFn_x3f_887_);
lean_inc(v_semiringInst_886_);
lean_inc(v_u_885_);
lean_inc(v_type_884_);
lean_inc(v_id_883_);
lean_dec(v_s_882_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_addFn_881_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 4, v___x_896_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_id_883_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_type_884_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_u_885_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_semiringInst_886_);
lean_ctor_set(v_reuseFailAlloc_899_, 4, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_899_, 5, v_mulFn_x3f_887_);
lean_ctor_set(v_reuseFailAlloc_899_, 6, v_powFn_x3f_888_);
lean_ctor_set(v_reuseFailAlloc_899_, 7, v_natCastFn_x3f_889_);
lean_ctor_set(v_reuseFailAlloc_899_, 8, v_denote_890_);
lean_ctor_set(v_reuseFailAlloc_899_, 9, v_vars_891_);
lean_ctor_set(v_reuseFailAlloc_899_, 10, v_varMap_892_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_902_, lean_object* v_addFn_903_, lean_object* v_____r_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = lean_apply_2(v_toPure_902_, lean_box(0), v_addFn_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_906_, lean_object* v_modifySemiring_907_, lean_object* v_toBind_908_, lean_object* v_addFn_909_){
_start:
{
lean_object* v___f_910_; lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_inc_ref(v_addFn_909_);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_910_, 0, v_addFn_909_);
v___f_911_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_911_, 0, v_toPure_906_);
lean_closure_set(v___f_911_, 1, v_addFn_909_);
v___x_912_ = lean_apply_1(v_modifySemiring_907_, v___f_910_);
v___x_913_ = lean_apply_4(v_toBind_908_, lean_box(0), lean_box(0), v___x_912_, v___f_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3(lean_object* v_toPure_931_, lean_object* v_inst_932_, lean_object* v_inst_933_, lean_object* v_inst_934_, lean_object* v_inst_935_, lean_object* v_toBind_936_, lean_object* v___f_937_, lean_object* v_s_938_){
_start:
{
lean_object* v_addFn_x3f_939_; 
v_addFn_x3f_939_ = lean_ctor_get(v_s_938_, 4);
if (lean_obj_tag(v_addFn_x3f_939_) == 1)
{
lean_object* v_val_940_; lean_object* v___x_941_; 
lean_inc_ref(v_addFn_x3f_939_);
lean_dec_ref(v_s_938_);
lean_dec(v___f_937_);
lean_dec(v_toBind_936_);
lean_dec_ref(v_inst_935_);
lean_dec_ref(v_inst_934_);
lean_dec_ref(v_inst_933_);
lean_dec(v_inst_932_);
v_val_940_ = lean_ctor_get(v_addFn_x3f_939_, 0);
lean_inc(v_val_940_);
lean_dec_ref(v_addFn_x3f_939_);
v___x_941_ = lean_apply_2(v_toPure_931_, lean_box(0), v_val_940_);
return v___x_941_;
}
else
{
lean_object* v_type_942_; lean_object* v_u_943_; lean_object* v_semiringInst_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_expectedInst_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v_toPure_931_);
v_type_942_ = lean_ctor_get(v_s_938_, 1);
lean_inc_ref_n(v_type_942_, 3);
v_u_943_ = lean_ctor_get(v_s_938_, 2);
lean_inc_n(v_u_943_, 2);
v_semiringInst_944_ = lean_ctor_get(v_s_938_, 3);
lean_inc_ref(v_semiringInst_944_);
lean_dec_ref(v_s_938_);
v___x_945_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_946_ = lean_box(0);
v___x_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_947_, 0, v_u_943_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
lean_inc_ref(v___x_947_);
v___x_948_ = l_Lean_mkConst(v___x_945_, v___x_947_);
v___x_949_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_950_ = l_Lean_mkConst(v___x_949_, v___x_947_);
v___x_951_ = l_Lean_mkAppB(v___x_950_, v_type_942_, v_semiringInst_944_);
v_expectedInst_952_ = l_Lean_mkAppB(v___x_948_, v_type_942_, v___x_951_);
v___x_953_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_954_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_955_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_932_, v_inst_933_, v_inst_934_, v_inst_935_, v_type_942_, v_u_943_, v___x_953_, v___x_954_, v_expectedInst_952_);
v___x_956_ = lean_apply_4(v_toBind_936_, lean_box(0), lean_box(0), v___x_955_, v___f_937_);
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_inst_961_){
_start:
{
lean_object* v_toApplicative_962_; lean_object* v_toBind_963_; lean_object* v_getSemiring_964_; lean_object* v_modifySemiring_965_; lean_object* v_toPure_966_; lean_object* v___f_967_; lean_object* v___f_968_; lean_object* v___x_969_; 
v_toApplicative_962_ = lean_ctor_get(v_inst_959_, 0);
v_toBind_963_ = lean_ctor_get(v_inst_959_, 1);
lean_inc_n(v_toBind_963_, 3);
v_getSemiring_964_ = lean_ctor_get(v_inst_961_, 0);
lean_inc(v_getSemiring_964_);
v_modifySemiring_965_ = lean_ctor_get(v_inst_961_, 1);
lean_inc(v_modifySemiring_965_);
lean_dec_ref(v_inst_961_);
v_toPure_966_ = lean_ctor_get(v_toApplicative_962_, 1);
lean_inc_n(v_toPure_966_, 2);
v___f_967_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_967_, 0, v_toPure_966_);
lean_closure_set(v___f_967_, 1, v_modifySemiring_965_);
lean_closure_set(v___f_967_, 2, v_toBind_963_);
v___f_968_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_968_, 0, v_toPure_966_);
lean_closure_set(v___f_968_, 1, v_inst_957_);
lean_closure_set(v___f_968_, 2, v_inst_958_);
lean_closure_set(v___f_968_, 3, v_inst_959_);
lean_closure_set(v___f_968_, 4, v_inst_960_);
lean_closure_set(v___f_968_, 5, v_toBind_963_);
lean_closure_set(v___f_968_, 6, v___f_967_);
v___x_969_ = lean_apply_4(v_toBind_963_, lean_box(0), lean_box(0), v_getSemiring_964_, v___f_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27(lean_object* v_m_970_, lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_inst_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(v_inst_971_, v_inst_972_, v_inst_973_, v_inst_974_, v_inst_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_977_, lean_object* v_s_978_){
_start:
{
lean_object* v_id_979_; lean_object* v_type_980_; lean_object* v_u_981_; lean_object* v_semiringInst_982_; lean_object* v_addFn_x3f_983_; lean_object* v_powFn_x3f_984_; lean_object* v_natCastFn_x3f_985_; lean_object* v_denote_986_; lean_object* v_vars_987_; lean_object* v_varMap_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_996_; 
v_id_979_ = lean_ctor_get(v_s_978_, 0);
v_type_980_ = lean_ctor_get(v_s_978_, 1);
v_u_981_ = lean_ctor_get(v_s_978_, 2);
v_semiringInst_982_ = lean_ctor_get(v_s_978_, 3);
v_addFn_x3f_983_ = lean_ctor_get(v_s_978_, 4);
v_powFn_x3f_984_ = lean_ctor_get(v_s_978_, 6);
v_natCastFn_x3f_985_ = lean_ctor_get(v_s_978_, 7);
v_denote_986_ = lean_ctor_get(v_s_978_, 8);
v_vars_987_ = lean_ctor_get(v_s_978_, 9);
v_varMap_988_ = lean_ctor_get(v_s_978_, 10);
v_isSharedCheck_996_ = !lean_is_exclusive(v_s_978_);
if (v_isSharedCheck_996_ == 0)
{
lean_object* v_unused_997_; 
v_unused_997_ = lean_ctor_get(v_s_978_, 5);
lean_dec(v_unused_997_);
v___x_990_ = v_s_978_;
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_varMap_988_);
lean_inc(v_vars_987_);
lean_inc(v_denote_986_);
lean_inc(v_natCastFn_x3f_985_);
lean_inc(v_powFn_x3f_984_);
lean_inc(v_addFn_x3f_983_);
lean_inc(v_semiringInst_982_);
lean_inc(v_u_981_);
lean_inc(v_type_980_);
lean_inc(v_id_979_);
lean_dec(v_s_978_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v_mulFn_977_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 5, v___x_992_);
v___x_994_ = v___x_990_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_id_979_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_type_980_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_u_981_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v_semiringInst_982_);
lean_ctor_set(v_reuseFailAlloc_995_, 4, v_addFn_x3f_983_);
lean_ctor_set(v_reuseFailAlloc_995_, 5, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_995_, 6, v_powFn_x3f_984_);
lean_ctor_set(v_reuseFailAlloc_995_, 7, v_natCastFn_x3f_985_);
lean_ctor_set(v_reuseFailAlloc_995_, 8, v_denote_986_);
lean_ctor_set(v_reuseFailAlloc_995_, 9, v_vars_987_);
lean_ctor_set(v_reuseFailAlloc_995_, 10, v_varMap_988_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_998_, lean_object* v_mulFn_999_, lean_object* v_____r_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_apply_2(v_toPure_998_, lean_box(0), v_mulFn_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_1002_, lean_object* v_modifySemiring_1003_, lean_object* v_toBind_1004_, lean_object* v_mulFn_1005_){
_start:
{
lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_inc_ref(v_mulFn_1005_);
v___f_1006_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1006_, 0, v_mulFn_1005_);
v___f_1007_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1007_, 0, v_toPure_1002_);
lean_closure_set(v___f_1007_, 1, v_mulFn_1005_);
v___x_1008_ = lean_apply_1(v_modifySemiring_1003_, v___f_1006_);
v___x_1009_ = lean_apply_4(v_toBind_1004_, lean_box(0), lean_box(0), v___x_1008_, v___f_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3(lean_object* v_toPure_1026_, lean_object* v_inst_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_toBind_1031_, lean_object* v___f_1032_, lean_object* v_s_1033_){
_start:
{
lean_object* v_mulFn_x3f_1034_; 
v_mulFn_x3f_1034_ = lean_ctor_get(v_s_1033_, 5);
if (lean_obj_tag(v_mulFn_x3f_1034_) == 1)
{
lean_object* v_val_1035_; lean_object* v___x_1036_; 
lean_inc_ref(v_mulFn_x3f_1034_);
lean_dec_ref(v_s_1033_);
lean_dec(v___f_1032_);
lean_dec(v_toBind_1031_);
lean_dec_ref(v_inst_1030_);
lean_dec_ref(v_inst_1029_);
lean_dec_ref(v_inst_1028_);
lean_dec(v_inst_1027_);
v_val_1035_ = lean_ctor_get(v_mulFn_x3f_1034_, 0);
lean_inc(v_val_1035_);
lean_dec_ref(v_mulFn_x3f_1034_);
v___x_1036_ = lean_apply_2(v_toPure_1026_, lean_box(0), v_val_1035_);
return v___x_1036_;
}
else
{
lean_object* v_type_1037_; lean_object* v_u_1038_; lean_object* v_semiringInst_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_expectedInst_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec(v_toPure_1026_);
v_type_1037_ = lean_ctor_get(v_s_1033_, 1);
lean_inc_ref_n(v_type_1037_, 3);
v_u_1038_ = lean_ctor_get(v_s_1033_, 2);
lean_inc_n(v_u_1038_, 2);
v_semiringInst_1039_ = lean_ctor_get(v_s_1033_, 3);
lean_inc_ref(v_semiringInst_1039_);
lean_dec_ref(v_s_1033_);
v___x_1040_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_1041_ = lean_box(0);
v___x_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_u_1038_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
lean_inc_ref(v___x_1042_);
v___x_1043_ = l_Lean_mkConst(v___x_1040_, v___x_1042_);
v___x_1044_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_1045_ = l_Lean_mkConst(v___x_1044_, v___x_1042_);
v___x_1046_ = l_Lean_mkAppB(v___x_1045_, v_type_1037_, v_semiringInst_1039_);
v_expectedInst_1047_ = l_Lean_mkAppB(v___x_1043_, v_type_1037_, v___x_1046_);
v___x_1048_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_1049_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_1050_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_1027_, v_inst_1028_, v_inst_1029_, v_inst_1030_, v_type_1037_, v_u_1038_, v___x_1048_, v___x_1049_, v_expectedInst_1047_);
v___x_1051_ = lean_apply_4(v_toBind_1031_, lean_box(0), lean_box(0), v___x_1050_, v___f_1032_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_){
_start:
{
lean_object* v_toApplicative_1057_; lean_object* v_toBind_1058_; lean_object* v_getSemiring_1059_; lean_object* v_modifySemiring_1060_; lean_object* v_toPure_1061_; lean_object* v___f_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; 
v_toApplicative_1057_ = lean_ctor_get(v_inst_1054_, 0);
v_toBind_1058_ = lean_ctor_get(v_inst_1054_, 1);
lean_inc_n(v_toBind_1058_, 3);
v_getSemiring_1059_ = lean_ctor_get(v_inst_1056_, 0);
lean_inc(v_getSemiring_1059_);
v_modifySemiring_1060_ = lean_ctor_get(v_inst_1056_, 1);
lean_inc(v_modifySemiring_1060_);
lean_dec_ref(v_inst_1056_);
v_toPure_1061_ = lean_ctor_get(v_toApplicative_1057_, 1);
lean_inc_n(v_toPure_1061_, 2);
v___f_1062_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1062_, 0, v_toPure_1061_);
lean_closure_set(v___f_1062_, 1, v_modifySemiring_1060_);
lean_closure_set(v___f_1062_, 2, v_toBind_1058_);
v___f_1063_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1063_, 0, v_toPure_1061_);
lean_closure_set(v___f_1063_, 1, v_inst_1052_);
lean_closure_set(v___f_1063_, 2, v_inst_1053_);
lean_closure_set(v___f_1063_, 3, v_inst_1054_);
lean_closure_set(v___f_1063_, 4, v_inst_1055_);
lean_closure_set(v___f_1063_, 5, v_toBind_1058_);
lean_closure_set(v___f_1063_, 6, v___f_1062_);
v___x_1064_ = lean_apply_4(v_toBind_1058_, lean_box(0), lean_box(0), v_getSemiring_1059_, v___f_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27(lean_object* v_m_1065_, lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(v_inst_1066_, v_inst_1067_, v_inst_1068_, v_inst_1069_, v_inst_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1072_, lean_object* v_s_1073_){
_start:
{
lean_object* v_id_1074_; lean_object* v_type_1075_; lean_object* v_u_1076_; lean_object* v_semiringInst_1077_; lean_object* v_addFn_x3f_1078_; lean_object* v_mulFn_x3f_1079_; lean_object* v_natCastFn_x3f_1080_; lean_object* v_denote_1081_; lean_object* v_vars_1082_; lean_object* v_varMap_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1091_; 
v_id_1074_ = lean_ctor_get(v_s_1073_, 0);
v_type_1075_ = lean_ctor_get(v_s_1073_, 1);
v_u_1076_ = lean_ctor_get(v_s_1073_, 2);
v_semiringInst_1077_ = lean_ctor_get(v_s_1073_, 3);
v_addFn_x3f_1078_ = lean_ctor_get(v_s_1073_, 4);
v_mulFn_x3f_1079_ = lean_ctor_get(v_s_1073_, 5);
v_natCastFn_x3f_1080_ = lean_ctor_get(v_s_1073_, 7);
v_denote_1081_ = lean_ctor_get(v_s_1073_, 8);
v_vars_1082_ = lean_ctor_get(v_s_1073_, 9);
v_varMap_1083_ = lean_ctor_get(v_s_1073_, 10);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_s_1073_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v_s_1073_, 6);
lean_dec(v_unused_1092_);
v___x_1085_ = v_s_1073_;
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_varMap_1083_);
lean_inc(v_vars_1082_);
lean_inc(v_denote_1081_);
lean_inc(v_natCastFn_x3f_1080_);
lean_inc(v_mulFn_x3f_1079_);
lean_inc(v_addFn_x3f_1078_);
lean_inc(v_semiringInst_1077_);
lean_inc(v_u_1076_);
lean_inc(v_type_1075_);
lean_inc(v_id_1074_);
lean_dec(v_s_1073_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_powFn_1072_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 6, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_id_1074_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_type_1075_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_u_1076_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_semiringInst_1077_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_addFn_x3f_1078_);
lean_ctor_set(v_reuseFailAlloc_1090_, 5, v_mulFn_x3f_1079_);
lean_ctor_set(v_reuseFailAlloc_1090_, 6, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1090_, 7, v_natCastFn_x3f_1080_);
lean_ctor_set(v_reuseFailAlloc_1090_, 8, v_denote_1081_);
lean_ctor_set(v_reuseFailAlloc_1090_, 9, v_vars_1082_);
lean_ctor_set(v_reuseFailAlloc_1090_, 10, v_varMap_1083_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1093_, lean_object* v_powFn_1094_, lean_object* v_____r_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_apply_2(v_toPure_1093_, lean_box(0), v_powFn_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1097_, lean_object* v_modifySemiring_1098_, lean_object* v_toBind_1099_, lean_object* v_powFn_1100_){
_start:
{
lean_object* v___f_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_inc_ref(v_powFn_1100_);
v___f_1101_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1101_, 0, v_powFn_1100_);
v___f_1102_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1102_, 0, v_toPure_1097_);
lean_closure_set(v___f_1102_, 1, v_powFn_1100_);
v___x_1103_ = lean_apply_1(v_modifySemiring_1098_, v___f_1101_);
v___x_1104_ = lean_apply_4(v_toBind_1099_, lean_box(0), lean_box(0), v___x_1103_, v___f_1102_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3(lean_object* v_toPure_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_toBind_1110_, lean_object* v___f_1111_, lean_object* v_s_1112_){
_start:
{
lean_object* v_powFn_x3f_1113_; 
v_powFn_x3f_1113_ = lean_ctor_get(v_s_1112_, 6);
if (lean_obj_tag(v_powFn_x3f_1113_) == 1)
{
lean_object* v_val_1114_; lean_object* v___x_1115_; 
lean_inc_ref(v_powFn_x3f_1113_);
lean_dec_ref(v_s_1112_);
lean_dec(v___f_1111_);
lean_dec(v_toBind_1110_);
lean_dec_ref(v_inst_1109_);
lean_dec_ref(v_inst_1108_);
lean_dec_ref(v_inst_1107_);
lean_dec(v_inst_1106_);
v_val_1114_ = lean_ctor_get(v_powFn_x3f_1113_, 0);
lean_inc(v_val_1114_);
lean_dec_ref(v_powFn_x3f_1113_);
v___x_1115_ = lean_apply_2(v_toPure_1105_, lean_box(0), v_val_1114_);
return v___x_1115_;
}
else
{
lean_object* v_type_1116_; lean_object* v_u_1117_; lean_object* v_semiringInst_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec(v_toPure_1105_);
v_type_1116_ = lean_ctor_get(v_s_1112_, 1);
lean_inc_ref(v_type_1116_);
v_u_1117_ = lean_ctor_get(v_s_1112_, 2);
lean_inc(v_u_1117_);
v_semiringInst_1118_ = lean_ctor_get(v_s_1112_, 3);
lean_inc_ref(v_semiringInst_1118_);
lean_dec_ref(v_s_1112_);
v___x_1119_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(v_inst_1106_, v_inst_1107_, v_inst_1108_, v_inst_1109_, v_u_1117_, v_type_1116_, v_semiringInst_1118_);
v___x_1120_ = lean_apply_4(v_toBind_1110_, lean_box(0), lean_box(0), v___x_1119_, v___f_1111_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_){
_start:
{
lean_object* v_toApplicative_1126_; lean_object* v_toBind_1127_; lean_object* v_getSemiring_1128_; lean_object* v_modifySemiring_1129_; lean_object* v_toPure_1130_; lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; 
v_toApplicative_1126_ = lean_ctor_get(v_inst_1123_, 0);
v_toBind_1127_ = lean_ctor_get(v_inst_1123_, 1);
lean_inc_n(v_toBind_1127_, 3);
v_getSemiring_1128_ = lean_ctor_get(v_inst_1125_, 0);
lean_inc(v_getSemiring_1128_);
v_modifySemiring_1129_ = lean_ctor_get(v_inst_1125_, 1);
lean_inc(v_modifySemiring_1129_);
lean_dec_ref(v_inst_1125_);
v_toPure_1130_ = lean_ctor_get(v_toApplicative_1126_, 1);
lean_inc_n(v_toPure_1130_, 2);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1131_, 0, v_toPure_1130_);
lean_closure_set(v___f_1131_, 1, v_modifySemiring_1129_);
lean_closure_set(v___f_1131_, 2, v_toBind_1127_);
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1132_, 0, v_toPure_1130_);
lean_closure_set(v___f_1132_, 1, v_inst_1121_);
lean_closure_set(v___f_1132_, 2, v_inst_1122_);
lean_closure_set(v___f_1132_, 3, v_inst_1123_);
lean_closure_set(v___f_1132_, 4, v_inst_1124_);
lean_closure_set(v___f_1132_, 5, v_toBind_1127_);
lean_closure_set(v___f_1132_, 6, v___f_1131_);
v___x_1133_ = lean_apply_4(v_toBind_1127_, lean_box(0), lean_box(0), v_getSemiring_1128_, v___f_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27(lean_object* v_m_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(v_inst_1135_, v_inst_1136_, v_inst_1137_, v_inst_1138_, v_inst_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1141_, lean_object* v_s_1142_){
_start:
{
lean_object* v_id_1143_; lean_object* v_type_1144_; lean_object* v_u_1145_; lean_object* v_semiringInst_1146_; lean_object* v_addFn_x3f_1147_; lean_object* v_mulFn_x3f_1148_; lean_object* v_powFn_x3f_1149_; lean_object* v_denote_1150_; lean_object* v_vars_1151_; lean_object* v_varMap_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1160_; 
v_id_1143_ = lean_ctor_get(v_s_1142_, 0);
v_type_1144_ = lean_ctor_get(v_s_1142_, 1);
v_u_1145_ = lean_ctor_get(v_s_1142_, 2);
v_semiringInst_1146_ = lean_ctor_get(v_s_1142_, 3);
v_addFn_x3f_1147_ = lean_ctor_get(v_s_1142_, 4);
v_mulFn_x3f_1148_ = lean_ctor_get(v_s_1142_, 5);
v_powFn_x3f_1149_ = lean_ctor_get(v_s_1142_, 6);
v_denote_1150_ = lean_ctor_get(v_s_1142_, 8);
v_vars_1151_ = lean_ctor_get(v_s_1142_, 9);
v_varMap_1152_ = lean_ctor_get(v_s_1142_, 10);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_s_1142_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v_s_1142_, 7);
lean_dec(v_unused_1161_);
v___x_1154_ = v_s_1142_;
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_varMap_1152_);
lean_inc(v_vars_1151_);
lean_inc(v_denote_1150_);
lean_inc(v_powFn_x3f_1149_);
lean_inc(v_mulFn_x3f_1148_);
lean_inc(v_addFn_x3f_1147_);
lean_inc(v_semiringInst_1146_);
lean_inc(v_u_1145_);
lean_inc(v_type_1144_);
lean_inc(v_id_1143_);
lean_dec(v_s_1142_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_natCastFn_1141_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 7, v___x_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_id_1143_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_type_1144_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_u_1145_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_semiringInst_1146_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_addFn_x3f_1147_);
lean_ctor_set(v_reuseFailAlloc_1159_, 5, v_mulFn_x3f_1148_);
lean_ctor_set(v_reuseFailAlloc_1159_, 6, v_powFn_x3f_1149_);
lean_ctor_set(v_reuseFailAlloc_1159_, 7, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1159_, 8, v_denote_1150_);
lean_ctor_set(v_reuseFailAlloc_1159_, 9, v_vars_1151_);
lean_ctor_set(v_reuseFailAlloc_1159_, 10, v_varMap_1152_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1162_, lean_object* v_natCastFn_1163_, lean_object* v_____r_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_apply_2(v_toPure_1162_, lean_box(0), v_natCastFn_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1166_, lean_object* v_modifySemiring_1167_, lean_object* v_toBind_1168_, lean_object* v_natCastFn_1169_){
_start:
{
lean_object* v___f_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_inc_ref(v_natCastFn_1169_);
v___f_1170_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1170_, 0, v_natCastFn_1169_);
v___f_1171_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1171_, 0, v_toPure_1166_);
lean_closure_set(v___f_1171_, 1, v_natCastFn_1169_);
v___x_1172_ = lean_apply_1(v_modifySemiring_1167_, v___f_1170_);
v___x_1173_ = lean_apply_4(v_toBind_1168_, lean_box(0), lean_box(0), v___x_1172_, v___f_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3(lean_object* v_toPure_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_toBind_1178_, lean_object* v___f_1179_, lean_object* v_s_1180_){
_start:
{
lean_object* v_natCastFn_x3f_1181_; 
v_natCastFn_x3f_1181_ = lean_ctor_get(v_s_1180_, 7);
if (lean_obj_tag(v_natCastFn_x3f_1181_) == 1)
{
lean_object* v_val_1182_; lean_object* v___x_1183_; 
lean_inc_ref(v_natCastFn_x3f_1181_);
lean_dec_ref(v_s_1180_);
lean_dec(v___f_1179_);
lean_dec(v_toBind_1178_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec(v_inst_1175_);
v_val_1182_ = lean_ctor_get(v_natCastFn_x3f_1181_, 0);
lean_inc(v_val_1182_);
lean_dec_ref(v_natCastFn_x3f_1181_);
v___x_1183_ = lean_apply_2(v_toPure_1174_, lean_box(0), v_val_1182_);
return v___x_1183_;
}
else
{
lean_object* v_type_1184_; lean_object* v_u_1185_; lean_object* v_semiringInst_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec(v_toPure_1174_);
v_type_1184_ = lean_ctor_get(v_s_1180_, 1);
lean_inc_ref(v_type_1184_);
v_u_1185_ = lean_ctor_get(v_s_1180_, 2);
lean_inc(v_u_1185_);
v_semiringInst_1186_ = lean_ctor_get(v_s_1180_, 3);
lean_inc_ref(v_semiringInst_1186_);
lean_dec_ref(v_s_1180_);
v___x_1187_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(v_inst_1175_, v_inst_1176_, v_inst_1177_, v_u_1185_, v_type_1184_, v_semiringInst_1186_);
v___x_1188_ = lean_apply_4(v_toBind_1178_, lean_box(0), lean_box(0), v___x_1187_, v___f_1179_);
return v___x_1188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_){
_start:
{
lean_object* v_toApplicative_1193_; lean_object* v_toBind_1194_; lean_object* v_getSemiring_1195_; lean_object* v_modifySemiring_1196_; lean_object* v_toPure_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___x_1200_; 
v_toApplicative_1193_ = lean_ctor_get(v_inst_1190_, 0);
v_toBind_1194_ = lean_ctor_get(v_inst_1190_, 1);
lean_inc_n(v_toBind_1194_, 3);
v_getSemiring_1195_ = lean_ctor_get(v_inst_1192_, 0);
lean_inc(v_getSemiring_1195_);
v_modifySemiring_1196_ = lean_ctor_get(v_inst_1192_, 1);
lean_inc(v_modifySemiring_1196_);
lean_dec_ref(v_inst_1192_);
v_toPure_1197_ = lean_ctor_get(v_toApplicative_1193_, 1);
lean_inc_n(v_toPure_1197_, 2);
v___f_1198_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1198_, 0, v_toPure_1197_);
lean_closure_set(v___f_1198_, 1, v_modifySemiring_1196_);
lean_closure_set(v___f_1198_, 2, v_toBind_1194_);
v___f_1199_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1199_, 0, v_toPure_1197_);
lean_closure_set(v___f_1199_, 1, v_inst_1189_);
lean_closure_set(v___f_1199_, 2, v_inst_1190_);
lean_closure_set(v___f_1199_, 3, v_inst_1191_);
lean_closure_set(v___f_1199_, 4, v_toBind_1194_);
lean_closure_set(v___f_1199_, 5, v___f_1198_);
v___x_1200_ = lean_apply_4(v_toBind_1194_, lean_box(0), lean_box(0), v_getSemiring_1195_, v___f_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27(lean_object* v_m_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(v_inst_1202_, v_inst_1203_, v_inst_1204_, v_inst_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1207_, lean_object* v_vals_1208_, lean_object* v_i_1209_, lean_object* v_k_1210_){
_start:
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_array_get_size(v_keys_1207_);
v___x_1212_ = lean_nat_dec_lt(v_i_1209_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec(v_i_1209_);
v___x_1213_ = lean_box(0);
return v___x_1213_;
}
else
{
lean_object* v_k_x27_1214_; uint8_t v___x_1215_; 
v_k_x27_1214_ = lean_array_fget_borrowed(v_keys_1207_, v_i_1209_);
v___x_1215_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_1210_, v_k_x27_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_unsigned_to_nat(1u);
v___x_1217_ = lean_nat_add(v_i_1209_, v___x_1216_);
lean_dec(v_i_1209_);
v_i_1209_ = v___x_1217_;
goto _start;
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_array_fget_borrowed(v_vals_1208_, v_i_1209_);
lean_dec(v_i_1209_);
lean_inc(v___x_1219_);
v___x_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1221_, lean_object* v_vals_1222_, lean_object* v_i_1223_, lean_object* v_k_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1221_, v_vals_1222_, v_i_1223_, v_k_1224_);
lean_dec_ref(v_k_1224_);
lean_dec_ref(v_vals_1222_);
lean_dec_ref(v_keys_1221_);
return v_res_1225_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; 
v___x_1226_ = ((size_t)5ULL);
v___x_1227_ = ((size_t)1ULL);
v___x_1228_ = lean_usize_shift_left(v___x_1227_, v___x_1226_);
return v___x_1228_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; 
v___x_1229_ = ((size_t)1ULL);
v___x_1230_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0);
v___x_1231_ = lean_usize_sub(v___x_1230_, v___x_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_1232_, size_t v_x_1233_, lean_object* v_x_1234_){
_start:
{
if (lean_obj_tag(v_x_1232_) == 0)
{
lean_object* v_es_1235_; lean_object* v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; lean_object* v_j_1240_; lean_object* v___x_1241_; 
v_es_1235_ = lean_ctor_get(v_x_1232_, 0);
v___x_1236_ = lean_box(2);
v___x_1237_ = ((size_t)5ULL);
v___x_1238_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1239_ = lean_usize_land(v_x_1233_, v___x_1238_);
v_j_1240_ = lean_usize_to_nat(v___x_1239_);
v___x_1241_ = lean_array_get_borrowed(v___x_1236_, v_es_1235_, v_j_1240_);
lean_dec(v_j_1240_);
switch(lean_obj_tag(v___x_1241_))
{
case 0:
{
lean_object* v_key_1242_; lean_object* v_val_1243_; uint8_t v___x_1244_; 
v_key_1242_ = lean_ctor_get(v___x_1241_, 0);
v_val_1243_ = lean_ctor_get(v___x_1241_, 1);
v___x_1244_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1234_, v_key_1242_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_box(0);
return v___x_1245_;
}
else
{
lean_object* v___x_1246_; 
lean_inc(v_val_1243_);
v___x_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1246_, 0, v_val_1243_);
return v___x_1246_;
}
}
case 1:
{
lean_object* v_node_1247_; size_t v___x_1248_; 
v_node_1247_ = lean_ctor_get(v___x_1241_, 0);
v___x_1248_ = lean_usize_shift_right(v_x_1233_, v___x_1237_);
v_x_1232_ = v_node_1247_;
v_x_1233_ = v___x_1248_;
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
v_ks_1251_ = lean_ctor_get(v_x_1232_, 0);
v_vs_1252_ = lean_ctor_get(v_x_1232_, 1);
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1251_, v_vs_1252_, v___x_1253_, v_x_1234_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
size_t v_x_867__boxed_1258_; lean_object* v_res_1259_; 
v_x_867__boxed_1258_ = lean_unbox_usize(v_x_1256_);
lean_dec(v_x_1256_);
v_res_1259_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1255_, v_x_867__boxed_1258_, v_x_1257_);
lean_dec_ref(v_x_1257_);
lean_dec_ref(v_x_1255_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
uint64_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1261_);
v___x_1263_ = lean_uint64_to_usize(v___x_1262_);
v___x_1264_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1260_, v___x_1263_, v_x_1261_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_1265_, v_x_1266_);
lean_dec_ref(v_x_1266_);
lean_dec_ref(v_x_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(lean_object* v_e_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1282_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1282_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1282_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_exprToSemiringId_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v_exprToSemiringId_1277_ = lean_ctor_get(v_a_1273_, 5);
lean_inc_ref(v_exprToSemiringId_1277_);
lean_dec(v_a_1273_);
v___x_1278_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_exprToSemiringId_1277_, v_e_1268_);
lean_dec_ref(v_exprToSemiringId_1277_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1278_);
v___x_1280_ = v___x_1275_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
v_a_1283_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1272_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1272_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(lean_object* v_e_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1291_, v_a_1292_, v_a_1293_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_e_1291_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(lean_object* v_e_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1296_, v_a_1297_, v_a_1305_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(lean_object* v_e_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(v_e_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_e_1309_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(lean_object* v_00_u03b2_1322_, lean_object* v_x_1323_, lean_object* v_x_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_1323_, v_x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1326_, lean_object* v_x_1327_, lean_object* v_x_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(v_00_u03b2_1326_, v_x_1327_, v_x_1328_);
lean_dec_ref(v_x_1328_);
lean_dec_ref(v_x_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1330_, lean_object* v_x_1331_, size_t v_x_1332_, lean_object* v_x_1333_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1331_, v_x_1332_, v_x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1335_, lean_object* v_x_1336_, lean_object* v_x_1337_, lean_object* v_x_1338_){
_start:
{
size_t v_x_984__boxed_1339_; lean_object* v_res_1340_; 
v_x_984__boxed_1339_ = lean_unbox_usize(v_x_1337_);
lean_dec(v_x_1337_);
v_res_1340_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(v_00_u03b2_1335_, v_x_1336_, v_x_984__boxed_1339_, v_x_1338_);
lean_dec_ref(v_x_1338_);
lean_dec_ref(v_x_1336_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1341_, lean_object* v_keys_1342_, lean_object* v_vals_1343_, lean_object* v_heq_1344_, lean_object* v_i_1345_, lean_object* v_k_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1342_, v_vals_1343_, v_i_1345_, v_k_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1348_, lean_object* v_keys_1349_, lean_object* v_vals_1350_, lean_object* v_heq_1351_, lean_object* v_i_1352_, lean_object* v_k_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1348_, v_keys_1349_, v_vals_1350_, v_heq_1351_, v_i_1352_, v_k_1353_);
lean_dec_ref(v_k_1353_);
lean_dec_ref(v_vals_1350_);
lean_dec_ref(v_keys_1349_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1355_, lean_object* v_x_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
lean_object* v_ks_1359_; lean_object* v_vs_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1384_; 
v_ks_1359_ = lean_ctor_get(v_x_1355_, 0);
v_vs_1360_ = lean_ctor_get(v_x_1355_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_x_1355_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1362_ = v_x_1355_;
v_isShared_1363_ = v_isSharedCheck_1384_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_vs_1360_);
lean_inc(v_ks_1359_);
lean_dec(v_x_1355_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1384_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = lean_array_get_size(v_ks_1359_);
v___x_1365_ = lean_nat_dec_lt(v_x_1356_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
lean_dec(v_x_1356_);
v___x_1366_ = lean_array_push(v_ks_1359_, v_x_1357_);
v___x_1367_ = lean_array_push(v_vs_1360_, v_x_1358_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 1, v___x_1367_);
lean_ctor_set(v___x_1362_, 0, v___x_1366_);
v___x_1369_ = v___x_1362_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
else
{
lean_object* v_k_x27_1371_; uint8_t v___x_1372_; 
v_k_x27_1371_ = lean_array_fget_borrowed(v_ks_1359_, v_x_1356_);
v___x_1372_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1357_, v_k_x27_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1374_; 
if (v_isShared_1363_ == 0)
{
v___x_1374_ = v___x_1362_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_ks_1359_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_vs_1360_);
v___x_1374_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_unsigned_to_nat(1u);
v___x_1376_ = lean_nat_add(v_x_1356_, v___x_1375_);
lean_dec(v_x_1356_);
v_x_1355_ = v___x_1374_;
v_x_1356_ = v___x_1376_;
goto _start;
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1379_ = lean_array_fset(v_ks_1359_, v_x_1356_, v_x_1357_);
v___x_1380_ = lean_array_fset(v_vs_1360_, v_x_1356_, v_x_1358_);
lean_dec(v_x_1356_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 1, v___x_1380_);
lean_ctor_set(v___x_1362_, 0, v___x_1379_);
v___x_1382_ = v___x_1362_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1385_, lean_object* v_k_1386_, lean_object* v_v_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1385_, v___x_1388_, v_k_1386_, v_v_1387_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(lean_object* v_x_1391_, size_t v_x_1392_, size_t v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 0)
{
lean_object* v_es_1396_; size_t v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; lean_object* v_j_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_es_1396_ = lean_ctor_get(v_x_1391_, 0);
v___x_1397_ = ((size_t)5ULL);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1400_ = lean_usize_land(v_x_1392_, v___x_1399_);
v_j_1401_ = lean_usize_to_nat(v___x_1400_);
v___x_1402_ = lean_array_get_size(v_es_1396_);
v___x_1403_ = lean_nat_dec_lt(v_j_1401_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_dec(v_j_1401_);
lean_dec(v_x_1395_);
lean_dec_ref(v_x_1394_);
return v_x_1391_;
}
else
{
lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1440_; 
lean_inc_ref(v_es_1396_);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_x_1391_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v_x_1391_, 0);
lean_dec(v_unused_1441_);
v___x_1405_ = v_x_1391_;
v_isShared_1406_ = v_isSharedCheck_1440_;
goto v_resetjp_1404_;
}
else
{
lean_dec(v_x_1391_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1440_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v_v_1407_; lean_object* v___x_1408_; lean_object* v_xs_x27_1409_; lean_object* v___y_1411_; 
v_v_1407_ = lean_array_fget(v_es_1396_, v_j_1401_);
v___x_1408_ = lean_box(0);
v_xs_x27_1409_ = lean_array_fset(v_es_1396_, v_j_1401_, v___x_1408_);
switch(lean_obj_tag(v_v_1407_))
{
case 0:
{
lean_object* v_key_1416_; lean_object* v_val_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1427_; 
v_key_1416_ = lean_ctor_get(v_v_1407_, 0);
v_val_1417_ = lean_ctor_get(v_v_1407_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_v_1407_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1419_ = v_v_1407_;
v_isShared_1420_ = v_isSharedCheck_1427_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_val_1417_);
lean_inc(v_key_1416_);
lean_dec(v_v_1407_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1427_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
uint8_t v___x_1421_; 
v___x_1421_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1394_, v_key_1416_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_del_object(v___x_1419_);
v___x_1422_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1416_, v_val_1417_, v_x_1394_, v_x_1395_);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
v___y_1411_ = v___x_1423_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_val_1417_);
lean_dec(v_key_1416_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 1, v_x_1395_);
lean_ctor_set(v___x_1419_, 0, v_x_1394_);
v___x_1425_ = v___x_1419_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_x_1394_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_x_1395_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
v___y_1411_ = v___x_1425_;
goto v___jp_1410_;
}
}
}
}
case 1:
{
lean_object* v_node_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1438_; 
v_node_1428_ = lean_ctor_get(v_v_1407_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_v_1407_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1430_ = v_v_1407_;
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_node_1428_);
lean_dec(v_v_1407_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
size_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1432_ = lean_usize_shift_right(v_x_1392_, v___x_1397_);
v___x_1433_ = lean_usize_add(v_x_1393_, v___x_1398_);
v___x_1434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_node_1428_, v___x_1432_, v___x_1433_, v_x_1394_, v_x_1395_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1434_);
v___x_1436_ = v___x_1430_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
v___y_1411_ = v___x_1436_;
goto v___jp_1410_;
}
}
}
default: 
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v_x_1394_);
lean_ctor_set(v___x_1439_, 1, v_x_1395_);
v___y_1411_ = v___x_1439_;
goto v___jp_1410_;
}
}
v___jp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_array_fset(v_xs_x27_1409_, v_j_1401_, v___y_1411_);
lean_dec(v_j_1401_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1412_);
v___x_1414_ = v___x_1405_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
else
{
lean_object* v_ks_1442_; lean_object* v_vs_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1463_; 
v_ks_1442_ = lean_ctor_get(v_x_1391_, 0);
v_vs_1443_ = lean_ctor_get(v_x_1391_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1391_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1445_ = v_x_1391_;
v_isShared_1446_ = v_isSharedCheck_1463_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_vs_1443_);
lean_inc(v_ks_1442_);
lean_dec(v_x_1391_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1463_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_ks_1442_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_vs_1443_);
v___x_1448_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v_newNode_1449_; uint8_t v___y_1451_; size_t v___x_1457_; uint8_t v___x_1458_; 
v_newNode_1449_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v___x_1448_, v_x_1394_, v_x_1395_);
v___x_1457_ = ((size_t)7ULL);
v___x_1458_ = lean_usize_dec_le(v___x_1457_, v_x_1393_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1459_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1449_);
v___x_1460_ = lean_unsigned_to_nat(4u);
v___x_1461_ = lean_nat_dec_lt(v___x_1459_, v___x_1460_);
lean_dec(v___x_1459_);
v___y_1451_ = v___x_1461_;
goto v___jp_1450_;
}
else
{
v___y_1451_ = v___x_1458_;
goto v___jp_1450_;
}
v___jp_1450_:
{
if (v___y_1451_ == 0)
{
lean_object* v_ks_1452_; lean_object* v_vs_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_ks_1452_ = lean_ctor_get(v_newNode_1449_, 0);
lean_inc_ref(v_ks_1452_);
v_vs_1453_ = lean_ctor_get(v_newNode_1449_, 1);
lean_inc_ref(v_vs_1453_);
lean_dec_ref(v_newNode_1449_);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_1456_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_x_1393_, v_ks_1452_, v_vs_1453_, v___x_1454_, v___x_1455_);
lean_dec_ref(v_vs_1453_);
lean_dec_ref(v_ks_1452_);
return v___x_1456_;
}
else
{
return v_newNode_1449_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1464_, lean_object* v_keys_1465_, lean_object* v_vals_1466_, lean_object* v_i_1467_, lean_object* v_entries_1468_){
_start:
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = lean_array_get_size(v_keys_1465_);
v___x_1470_ = lean_nat_dec_lt(v_i_1467_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_dec(v_i_1467_);
return v_entries_1468_;
}
else
{
lean_object* v_k_1471_; lean_object* v_v_1472_; uint64_t v___x_1473_; size_t v_h_1474_; size_t v___x_1475_; lean_object* v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; size_t v_h_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_k_1471_ = lean_array_fget_borrowed(v_keys_1465_, v_i_1467_);
v_v_1472_ = lean_array_fget_borrowed(v_vals_1466_, v_i_1467_);
v___x_1473_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1471_);
v_h_1474_ = lean_uint64_to_usize(v___x_1473_);
v___x_1475_ = ((size_t)5ULL);
v___x_1476_ = lean_unsigned_to_nat(1u);
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_sub(v_depth_1464_, v___x_1477_);
v___x_1479_ = lean_usize_mul(v___x_1475_, v___x_1478_);
v_h_1480_ = lean_usize_shift_right(v_h_1474_, v___x_1479_);
v___x_1481_ = lean_nat_add(v_i_1467_, v___x_1476_);
lean_dec(v_i_1467_);
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
v___x_1482_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_entries_1468_, v_h_1480_, v_depth_1464_, v_k_1471_, v_v_1472_);
v_i_1467_ = v___x_1481_;
v_entries_1468_ = v___x_1482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1484_, lean_object* v_keys_1485_, lean_object* v_vals_1486_, lean_object* v_i_1487_, lean_object* v_entries_1488_){
_start:
{
size_t v_depth_boxed_1489_; lean_object* v_res_1490_; 
v_depth_boxed_1489_ = lean_unbox_usize(v_depth_1484_);
lean_dec(v_depth_1484_);
v_res_1490_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1489_, v_keys_1485_, v_vals_1486_, v_i_1487_, v_entries_1488_);
lean_dec_ref(v_vals_1486_);
lean_dec_ref(v_keys_1485_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_){
_start:
{
size_t v_x_7240__boxed_1496_; size_t v_x_7241__boxed_1497_; lean_object* v_res_1498_; 
v_x_7240__boxed_1496_ = lean_unbox_usize(v_x_1492_);
lean_dec(v_x_1492_);
v_x_7241__boxed_1497_ = lean_unbox_usize(v_x_1493_);
lean_dec(v_x_1493_);
v_res_1498_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1491_, v_x_7240__boxed_1496_, v_x_7241__boxed_1497_, v_x_1494_, v_x_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object* v_x_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
uint64_t v___x_1502_; size_t v___x_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1502_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1500_);
v___x_1503_ = lean_uint64_to_usize(v___x_1502_);
v___x_1504_ = ((size_t)1ULL);
v___x_1505_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1499_, v___x_1503_, v___x_1504_, v_x_1500_, v_x_1501_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object* v_e_1506_, lean_object* v_a_1507_, lean_object* v_s_1508_){
_start:
{
lean_object* v_rings_1509_; lean_object* v_typeIdOf_1510_; lean_object* v_exprToRingId_1511_; lean_object* v_semirings_1512_; lean_object* v_stypeIdOf_1513_; lean_object* v_exprToSemiringId_1514_; lean_object* v_ncRings_1515_; lean_object* v_exprToNCRingId_1516_; lean_object* v_nctypeIdOf_1517_; lean_object* v_ncSemirings_1518_; lean_object* v_exprToNCSemiringId_1519_; lean_object* v_ncstypeIdOf_1520_; lean_object* v_steps_1521_; uint8_t v_reportedMaxDegreeIssue_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1530_; 
v_rings_1509_ = lean_ctor_get(v_s_1508_, 0);
v_typeIdOf_1510_ = lean_ctor_get(v_s_1508_, 1);
v_exprToRingId_1511_ = lean_ctor_get(v_s_1508_, 2);
v_semirings_1512_ = lean_ctor_get(v_s_1508_, 3);
v_stypeIdOf_1513_ = lean_ctor_get(v_s_1508_, 4);
v_exprToSemiringId_1514_ = lean_ctor_get(v_s_1508_, 5);
v_ncRings_1515_ = lean_ctor_get(v_s_1508_, 6);
v_exprToNCRingId_1516_ = lean_ctor_get(v_s_1508_, 7);
v_nctypeIdOf_1517_ = lean_ctor_get(v_s_1508_, 8);
v_ncSemirings_1518_ = lean_ctor_get(v_s_1508_, 9);
v_exprToNCSemiringId_1519_ = lean_ctor_get(v_s_1508_, 10);
v_ncstypeIdOf_1520_ = lean_ctor_get(v_s_1508_, 11);
v_steps_1521_ = lean_ctor_get(v_s_1508_, 12);
v_reportedMaxDegreeIssue_1522_ = lean_ctor_get_uint8(v_s_1508_, sizeof(void*)*13);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_s_1508_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1524_ = v_s_1508_;
v_isShared_1525_ = v_isSharedCheck_1530_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_steps_1521_);
lean_inc(v_ncstypeIdOf_1520_);
lean_inc(v_exprToNCSemiringId_1519_);
lean_inc(v_ncSemirings_1518_);
lean_inc(v_nctypeIdOf_1517_);
lean_inc(v_exprToNCRingId_1516_);
lean_inc(v_ncRings_1515_);
lean_inc(v_exprToSemiringId_1514_);
lean_inc(v_stypeIdOf_1513_);
lean_inc(v_semirings_1512_);
lean_inc(v_exprToRingId_1511_);
lean_inc(v_typeIdOf_1510_);
lean_inc(v_rings_1509_);
lean_dec(v_s_1508_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1530_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
lean_inc(v_a_1507_);
v___x_1526_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_exprToSemiringId_1514_, v_e_1506_, v_a_1507_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 5, v___x_1526_);
v___x_1528_ = v___x_1524_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_rings_1509_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_typeIdOf_1510_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_exprToRingId_1511_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_semirings_1512_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_stypeIdOf_1513_);
lean_ctor_set(v_reuseFailAlloc_1529_, 5, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1529_, 6, v_ncRings_1515_);
lean_ctor_set(v_reuseFailAlloc_1529_, 7, v_exprToNCRingId_1516_);
lean_ctor_set(v_reuseFailAlloc_1529_, 8, v_nctypeIdOf_1517_);
lean_ctor_set(v_reuseFailAlloc_1529_, 9, v_ncSemirings_1518_);
lean_ctor_set(v_reuseFailAlloc_1529_, 10, v_exprToNCSemiringId_1519_);
lean_ctor_set(v_reuseFailAlloc_1529_, 11, v_ncstypeIdOf_1520_);
lean_ctor_set(v_reuseFailAlloc_1529_, 12, v_steps_1521_);
lean_ctor_set_uint8(v_reuseFailAlloc_1529_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1522_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object* v_e_1531_, lean_object* v_a_1532_, lean_object* v_s_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(v_e_1531_, v_a_1532_, v_s_1533_);
lean_dec(v_a_1532_);
return v_res_1534_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0));
v___x_1537_ = l_Lean_stringToMessageData(v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object* v_e_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1538_, v_a_1540_, v_a_1545_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
if (lean_obj_tag(v_a_1552_) == 1)
{
lean_object* v_val_1553_; uint8_t v___x_1554_; 
v_val_1553_ = lean_ctor_get(v_a_1552_, 0);
lean_inc(v_val_1553_);
lean_dec_ref(v_a_1552_);
v___x_1554_ = lean_nat_dec_eq(v_val_1553_, v_a_1539_);
lean_dec(v_val_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1541_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; uint8_t v___x_1557_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1555_);
v___x_1557_ = lean_unbox(v_a_1556_);
lean_dec(v_a_1556_);
if (v___x_1557_ == 0)
{
lean_dec_ref(v_e_1538_);
goto v___jp_1548_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1558_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1);
v___x_1559_ = l_Lean_indentExpr(v_e_1538_);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = l_Lean_Meta_Sym_reportIssue(v___x_1560_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_dec_ref(v___x_1561_);
goto v___jp_1548_;
}
else
{
return v___x_1561_;
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec_ref(v_e_1538_);
v_a_1562_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1555_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1555_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_dec_ref(v_e_1538_);
goto v___jp_1548_;
}
}
else
{
lean_object* v___f_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec(v_a_1552_);
lean_inc(v_a_1539_);
v___f_1570_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1570_, 0, v_e_1538_);
lean_closure_set(v___f_1570_, 1, v_a_1539_);
v___x_1571_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1572_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1571_, v___f_1570_, v_a_1540_);
return v___x_1572_;
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v_e_1538_);
v_a_1573_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1551_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1551_);
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
v___jp_1548_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_box(0);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object* v_e_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec(v_a_1582_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object* v_e_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1592_, v_a_1593_, v_a_1594_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object* v_e_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec(v_a_1607_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object* v_00_u03b2_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_, lean_object* v_x_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_1621_, v_x_1622_, v_x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_1625_, lean_object* v_x_1626_, size_t v_x_1627_, size_t v_x_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1626_, v_x_1627_, v_x_1628_, v_x_1629_, v_x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_){
_start:
{
size_t v_x_7519__boxed_1638_; size_t v_x_7520__boxed_1639_; lean_object* v_res_1640_; 
v_x_7519__boxed_1638_ = lean_unbox_usize(v_x_1634_);
lean_dec(v_x_1634_);
v_x_7520__boxed_1639_ = lean_unbox_usize(v_x_1635_);
lean_dec(v_x_1635_);
v_res_1640_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_1632_, v_x_1633_, v_x_7519__boxed_1638_, v_x_7520__boxed_1639_, v_x_1636_, v_x_1637_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1641_, lean_object* v_n_1642_, lean_object* v_k_1643_, lean_object* v_v_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_1642_, v_k_1643_, v_v_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1646_, size_t v_depth_1647_, lean_object* v_keys_1648_, lean_object* v_vals_1649_, lean_object* v_heq_1650_, lean_object* v_i_1651_, lean_object* v_entries_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_1647_, v_keys_1648_, v_vals_1649_, v_i_1651_, v_entries_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1654_, lean_object* v_depth_1655_, lean_object* v_keys_1656_, lean_object* v_vals_1657_, lean_object* v_heq_1658_, lean_object* v_i_1659_, lean_object* v_entries_1660_){
_start:
{
size_t v_depth_boxed_1661_; lean_object* v_res_1662_; 
v_depth_boxed_1661_ = lean_unbox_usize(v_depth_1655_);
lean_dec(v_depth_1655_);
v_res_1662_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_1654_, v_depth_boxed_1661_, v_keys_1656_, v_vals_1657_, v_heq_1658_, v_i_1659_, v_entries_1660_);
lean_dec_ref(v_vals_1657_);
lean_dec_ref(v_keys_1656_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1663_, lean_object* v_x_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1664_, v_x_1665_, v_x_1666_, v_x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object* v_e_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1669_, v___y_1670_, v___y_1671_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object* v_e_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(v_e_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec(v___y_1684_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object* v_e_1699_, lean_object* v___f_1700_, lean_object* v___f_1701_, lean_object* v_size_1702_, lean_object* v_s_1703_){
_start:
{
lean_object* v_id_1704_; lean_object* v_type_1705_; lean_object* v_u_1706_; lean_object* v_semiringInst_1707_; lean_object* v_addFn_x3f_1708_; lean_object* v_mulFn_x3f_1709_; lean_object* v_powFn_x3f_1710_; lean_object* v_natCastFn_x3f_1711_; lean_object* v_denote_1712_; lean_object* v_vars_1713_; lean_object* v_varMap_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1723_; 
v_id_1704_ = lean_ctor_get(v_s_1703_, 0);
v_type_1705_ = lean_ctor_get(v_s_1703_, 1);
v_u_1706_ = lean_ctor_get(v_s_1703_, 2);
v_semiringInst_1707_ = lean_ctor_get(v_s_1703_, 3);
v_addFn_x3f_1708_ = lean_ctor_get(v_s_1703_, 4);
v_mulFn_x3f_1709_ = lean_ctor_get(v_s_1703_, 5);
v_powFn_x3f_1710_ = lean_ctor_get(v_s_1703_, 6);
v_natCastFn_x3f_1711_ = lean_ctor_get(v_s_1703_, 7);
v_denote_1712_ = lean_ctor_get(v_s_1703_, 8);
v_vars_1713_ = lean_ctor_get(v_s_1703_, 9);
v_varMap_1714_ = lean_ctor_get(v_s_1703_, 10);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_s_1703_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1716_ = v_s_1703_;
v_isShared_1717_ = v_isSharedCheck_1723_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_varMap_1714_);
lean_inc(v_vars_1713_);
lean_inc(v_denote_1712_);
lean_inc(v_natCastFn_x3f_1711_);
lean_inc(v_powFn_x3f_1710_);
lean_inc(v_mulFn_x3f_1709_);
lean_inc(v_addFn_x3f_1708_);
lean_inc(v_semiringInst_1707_);
lean_inc(v_u_1706_);
lean_inc(v_type_1705_);
lean_inc(v_id_1704_);
lean_dec(v_s_1703_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1723_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
lean_inc_ref(v_e_1699_);
v___x_1718_ = l_Lean_PersistentArray_push___redArg(v_vars_1713_, v_e_1699_);
v___x_1719_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1700_, v___f_1701_, v_varMap_1714_, v_e_1699_, v_size_1702_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 10, v___x_1719_);
lean_ctor_set(v___x_1716_, 9, v___x_1718_);
v___x_1721_ = v___x_1716_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_id_1704_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_type_1705_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_u_1706_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_semiringInst_1707_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_addFn_x3f_1708_);
lean_ctor_set(v_reuseFailAlloc_1722_, 5, v_mulFn_x3f_1709_);
lean_ctor_set(v_reuseFailAlloc_1722_, 6, v_powFn_x3f_1710_);
lean_ctor_set(v_reuseFailAlloc_1722_, 7, v_natCastFn_x3f_1711_);
lean_ctor_set(v_reuseFailAlloc_1722_, 8, v_denote_1712_);
lean_ctor_set(v_reuseFailAlloc_1722_, 9, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1722_, 10, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object* v_toPure_1724_, lean_object* v_size_1725_, lean_object* v_____r_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_apply_2(v_toPure_1724_, lean_box(0), v_size_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object* v_e_1728_, lean_object* v_inst_1729_, lean_object* v_toBind_1730_, lean_object* v___f_1731_, lean_object* v_____r_1732_){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1733_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1734_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_1734_, 0, lean_box(0));
lean_closure_set(v___x_1734_, 1, v___x_1733_);
lean_closure_set(v___x_1734_, 2, v_e_1728_);
v___x_1735_ = lean_apply_2(v_inst_1729_, lean_box(0), v___x_1734_);
v___x_1736_ = lean_apply_4(v_toBind_1730_, lean_box(0), lean_box(0), v___x_1735_, v___f_1731_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object* v_inst_1737_, lean_object* v_e_1738_, lean_object* v_toBind_1739_, lean_object* v___f_1740_, lean_object* v_____r_1741_){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_apply_1(v_inst_1737_, v_e_1738_);
v___x_1743_ = lean_apply_4(v_toBind_1739_, lean_box(0), lean_box(0), v___x_1742_, v___f_1740_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object* v___f_1744_, lean_object* v___f_1745_, lean_object* v_e_1746_, lean_object* v_toPure_1747_, lean_object* v_inst_1748_, lean_object* v_toBind_1749_, lean_object* v_inst_1750_, lean_object* v_modifySemiring_1751_, lean_object* v_s_1752_){
_start:
{
lean_object* v_vars_1753_; lean_object* v_varMap_1754_; lean_object* v___x_1755_; 
v_vars_1753_ = lean_ctor_get(v_s_1752_, 9);
lean_inc_ref(v_vars_1753_);
v_varMap_1754_ = lean_ctor_get(v_s_1752_, 10);
lean_inc_ref(v_varMap_1754_);
lean_dec_ref(v_s_1752_);
lean_inc_ref(v_e_1746_);
lean_inc_ref(v___f_1745_);
lean_inc_ref(v___f_1744_);
v___x_1755_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_1744_, v___f_1745_, v_varMap_1754_, v_e_1746_);
lean_dec_ref(v_varMap_1754_);
if (lean_obj_tag(v___x_1755_) == 1)
{
lean_object* v_val_1756_; lean_object* v___x_1757_; 
lean_dec_ref(v_vars_1753_);
lean_dec(v_modifySemiring_1751_);
lean_dec(v_inst_1750_);
lean_dec(v_toBind_1749_);
lean_dec(v_inst_1748_);
lean_dec_ref(v_e_1746_);
lean_dec_ref(v___f_1745_);
lean_dec_ref(v___f_1744_);
v_val_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_val_1756_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = lean_apply_2(v_toPure_1747_, lean_box(0), v_val_1756_);
return v___x_1757_;
}
else
{
lean_object* v_size_1758_; lean_object* v___f_1759_; lean_object* v___f_1760_; lean_object* v___f_1761_; lean_object* v___f_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_dec(v___x_1755_);
v_size_1758_ = lean_ctor_get(v_vars_1753_, 2);
lean_inc_n(v_size_1758_, 2);
lean_dec_ref(v_vars_1753_);
lean_inc_ref_n(v_e_1746_, 2);
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1759_, 0, v_e_1746_);
lean_closure_set(v___f_1759_, 1, v___f_1744_);
lean_closure_set(v___f_1759_, 2, v___f_1745_);
lean_closure_set(v___f_1759_, 3, v_size_1758_);
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1760_, 0, v_toPure_1747_);
lean_closure_set(v___f_1760_, 1, v_size_1758_);
lean_inc_n(v_toBind_1749_, 2);
v___f_1761_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1761_, 0, v_e_1746_);
lean_closure_set(v___f_1761_, 1, v_inst_1748_);
lean_closure_set(v___f_1761_, 2, v_toBind_1749_);
lean_closure_set(v___f_1761_, 3, v___f_1760_);
v___f_1762_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1762_, 0, v_inst_1750_);
lean_closure_set(v___f_1762_, 1, v_e_1746_);
lean_closure_set(v___f_1762_, 2, v_toBind_1749_);
lean_closure_set(v___f_1762_, 3, v___f_1761_);
v___x_1763_ = lean_apply_1(v_modifySemiring_1751_, v___f_1759_);
v___x_1764_ = lean_apply_4(v_toBind_1749_, lean_box(0), lean_box(0), v___x_1763_, v___f_1762_);
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_inst_1769_, lean_object* v_inst_1770_, lean_object* v_e_1771_){
_start:
{
lean_object* v_toApplicative_1772_; lean_object* v_toBind_1773_; lean_object* v_getSemiring_1774_; lean_object* v_modifySemiring_1775_; lean_object* v_toPure_1776_; lean_object* v___f_1777_; lean_object* v___f_1778_; lean_object* v___f_1779_; lean_object* v___x_1780_; 
v_toApplicative_1772_ = lean_ctor_get(v_inst_1768_, 0);
lean_inc_ref(v_toApplicative_1772_);
v_toBind_1773_ = lean_ctor_get(v_inst_1768_, 1);
lean_inc_n(v_toBind_1773_, 2);
lean_dec_ref(v_inst_1768_);
v_getSemiring_1774_ = lean_ctor_get(v_inst_1769_, 0);
lean_inc(v_getSemiring_1774_);
v_modifySemiring_1775_ = lean_ctor_get(v_inst_1769_, 1);
lean_inc(v_modifySemiring_1775_);
lean_dec_ref(v_inst_1769_);
v_toPure_1776_ = lean_ctor_get(v_toApplicative_1772_, 1);
lean_inc(v_toPure_1776_);
lean_dec_ref(v_toApplicative_1772_);
v___f_1777_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0));
v___f_1778_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1));
v___f_1779_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1779_, 0, v___f_1777_);
lean_closure_set(v___f_1779_, 1, v___f_1778_);
lean_closure_set(v___f_1779_, 2, v_e_1771_);
lean_closure_set(v___f_1779_, 3, v_toPure_1776_);
lean_closure_set(v___f_1779_, 4, v_inst_1767_);
lean_closure_set(v___f_1779_, 5, v_toBind_1773_);
lean_closure_set(v___f_1779_, 6, v_inst_1770_);
lean_closure_set(v___f_1779_, 7, v_modifySemiring_1775_);
v___x_1780_ = lean_apply_4(v_toBind_1773_, lean_box(0), lean_box(0), v_getSemiring_1774_, v___f_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object* v_m_1781_, lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_e_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v_inst_1782_, v_inst_1783_, v_inst_1784_, v_inst_1785_, v_e_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(lean_object* v___y_1788_, lean_object* v_e_1789_, lean_object* v_size_1790_, lean_object* v_s_1791_){
_start:
{
lean_object* v_rings_1792_; lean_object* v_typeIdOf_1793_; lean_object* v_exprToRingId_1794_; lean_object* v_semirings_1795_; lean_object* v_stypeIdOf_1796_; lean_object* v_exprToSemiringId_1797_; lean_object* v_ncRings_1798_; lean_object* v_exprToNCRingId_1799_; lean_object* v_nctypeIdOf_1800_; lean_object* v_ncSemirings_1801_; lean_object* v_exprToNCSemiringId_1802_; lean_object* v_ncstypeIdOf_1803_; lean_object* v_steps_1804_; uint8_t v_reportedMaxDegreeIssue_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_rings_1792_ = lean_ctor_get(v_s_1791_, 0);
v_typeIdOf_1793_ = lean_ctor_get(v_s_1791_, 1);
v_exprToRingId_1794_ = lean_ctor_get(v_s_1791_, 2);
v_semirings_1795_ = lean_ctor_get(v_s_1791_, 3);
v_stypeIdOf_1796_ = lean_ctor_get(v_s_1791_, 4);
v_exprToSemiringId_1797_ = lean_ctor_get(v_s_1791_, 5);
v_ncRings_1798_ = lean_ctor_get(v_s_1791_, 6);
v_exprToNCRingId_1799_ = lean_ctor_get(v_s_1791_, 7);
v_nctypeIdOf_1800_ = lean_ctor_get(v_s_1791_, 8);
v_ncSemirings_1801_ = lean_ctor_get(v_s_1791_, 9);
v_exprToNCSemiringId_1802_ = lean_ctor_get(v_s_1791_, 10);
v_ncstypeIdOf_1803_ = lean_ctor_get(v_s_1791_, 11);
v_steps_1804_ = lean_ctor_get(v_s_1791_, 12);
v_reportedMaxDegreeIssue_1805_ = lean_ctor_get_uint8(v_s_1791_, sizeof(void*)*13);
v___x_1806_ = lean_array_get_size(v_semirings_1795_);
v___x_1807_ = lean_nat_dec_lt(v___y_1788_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_dec(v_size_1790_);
lean_dec_ref(v_e_1789_);
return v_s_1791_;
}
else
{
lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1850_; 
lean_inc(v_steps_1804_);
lean_inc_ref(v_ncstypeIdOf_1803_);
lean_inc_ref(v_exprToNCSemiringId_1802_);
lean_inc_ref(v_ncSemirings_1801_);
lean_inc_ref(v_nctypeIdOf_1800_);
lean_inc_ref(v_exprToNCRingId_1799_);
lean_inc_ref(v_ncRings_1798_);
lean_inc_ref(v_exprToSemiringId_1797_);
lean_inc_ref(v_stypeIdOf_1796_);
lean_inc_ref(v_semirings_1795_);
lean_inc_ref(v_exprToRingId_1794_);
lean_inc_ref(v_typeIdOf_1793_);
lean_inc_ref(v_rings_1792_);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_s_1791_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; lean_object* v_unused_1861_; lean_object* v_unused_1862_; lean_object* v_unused_1863_; 
v_unused_1851_ = lean_ctor_get(v_s_1791_, 12);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_s_1791_, 11);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v_s_1791_, 10);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_s_1791_, 9);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v_s_1791_, 8);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_s_1791_, 7);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_s_1791_, 6);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_s_1791_, 5);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_s_1791_, 4);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_s_1791_, 3);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v_s_1791_, 2);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v_s_1791_, 1);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v_s_1791_, 0);
lean_dec(v_unused_1863_);
v___x_1809_ = v_s_1791_;
v_isShared_1810_ = v_isSharedCheck_1850_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v_s_1791_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1850_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v_v_1811_; lean_object* v_toSemiring_1812_; lean_object* v_ringId_1813_; lean_object* v_commSemiringInst_1814_; lean_object* v_addRightCancelInst_x3f_1815_; lean_object* v_toQFn_x3f_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1849_; 
v_v_1811_ = lean_array_fget(v_semirings_1795_, v___y_1788_);
v_toSemiring_1812_ = lean_ctor_get(v_v_1811_, 0);
v_ringId_1813_ = lean_ctor_get(v_v_1811_, 1);
v_commSemiringInst_1814_ = lean_ctor_get(v_v_1811_, 2);
v_addRightCancelInst_x3f_1815_ = lean_ctor_get(v_v_1811_, 3);
v_toQFn_x3f_1816_ = lean_ctor_get(v_v_1811_, 4);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_v_1811_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1818_ = v_v_1811_;
v_isShared_1819_ = v_isSharedCheck_1849_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_toQFn_x3f_1816_);
lean_inc(v_addRightCancelInst_x3f_1815_);
lean_inc(v_commSemiringInst_1814_);
lean_inc(v_ringId_1813_);
lean_inc(v_toSemiring_1812_);
lean_dec(v_v_1811_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1849_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_id_1820_; lean_object* v_type_1821_; lean_object* v_u_1822_; lean_object* v_semiringInst_1823_; lean_object* v_addFn_x3f_1824_; lean_object* v_mulFn_x3f_1825_; lean_object* v_powFn_x3f_1826_; lean_object* v_natCastFn_x3f_1827_; lean_object* v_denote_1828_; lean_object* v_vars_1829_; lean_object* v_varMap_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1848_; 
v_id_1820_ = lean_ctor_get(v_toSemiring_1812_, 0);
v_type_1821_ = lean_ctor_get(v_toSemiring_1812_, 1);
v_u_1822_ = lean_ctor_get(v_toSemiring_1812_, 2);
v_semiringInst_1823_ = lean_ctor_get(v_toSemiring_1812_, 3);
v_addFn_x3f_1824_ = lean_ctor_get(v_toSemiring_1812_, 4);
v_mulFn_x3f_1825_ = lean_ctor_get(v_toSemiring_1812_, 5);
v_powFn_x3f_1826_ = lean_ctor_get(v_toSemiring_1812_, 6);
v_natCastFn_x3f_1827_ = lean_ctor_get(v_toSemiring_1812_, 7);
v_denote_1828_ = lean_ctor_get(v_toSemiring_1812_, 8);
v_vars_1829_ = lean_ctor_get(v_toSemiring_1812_, 9);
v_varMap_1830_ = lean_ctor_get(v_toSemiring_1812_, 10);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_toSemiring_1812_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1832_ = v_toSemiring_1812_;
v_isShared_1833_ = v_isSharedCheck_1848_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_varMap_1830_);
lean_inc(v_vars_1829_);
lean_inc(v_denote_1828_);
lean_inc(v_natCastFn_x3f_1827_);
lean_inc(v_powFn_x3f_1826_);
lean_inc(v_mulFn_x3f_1825_);
lean_inc(v_addFn_x3f_1824_);
lean_inc(v_semiringInst_1823_);
lean_inc(v_u_1822_);
lean_inc(v_type_1821_);
lean_inc(v_id_1820_);
lean_dec(v_toSemiring_1812_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1848_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v_xs_x27_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1834_ = lean_box(0);
v_xs_x27_1835_ = lean_array_fset(v_semirings_1795_, v___y_1788_, v___x_1834_);
lean_inc_ref(v_e_1789_);
v___x_1836_ = l_Lean_PersistentArray_push___redArg(v_vars_1829_, v_e_1789_);
v___x_1837_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_varMap_1830_, v_e_1789_, v_size_1790_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 10, v___x_1837_);
lean_ctor_set(v___x_1832_, 9, v___x_1836_);
v___x_1839_ = v___x_1832_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_id_1820_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_type_1821_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_u_1822_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_semiringInst_1823_);
lean_ctor_set(v_reuseFailAlloc_1847_, 4, v_addFn_x3f_1824_);
lean_ctor_set(v_reuseFailAlloc_1847_, 5, v_mulFn_x3f_1825_);
lean_ctor_set(v_reuseFailAlloc_1847_, 6, v_powFn_x3f_1826_);
lean_ctor_set(v_reuseFailAlloc_1847_, 7, v_natCastFn_x3f_1827_);
lean_ctor_set(v_reuseFailAlloc_1847_, 8, v_denote_1828_);
lean_ctor_set(v_reuseFailAlloc_1847_, 9, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1847_, 10, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1839_);
v___x_1841_ = v___x_1818_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_ringId_1813_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_commSemiringInst_1814_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_addRightCancelInst_x3f_1815_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v_toQFn_x3f_1816_);
v___x_1841_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_array_fset(v_xs_x27_1835_, v___y_1788_, v___x_1841_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 3, v___x_1842_);
v___x_1844_ = v___x_1809_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_rings_1792_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_typeIdOf_1793_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v_exprToRingId_1794_);
lean_ctor_set(v_reuseFailAlloc_1845_, 3, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1845_, 4, v_stypeIdOf_1796_);
lean_ctor_set(v_reuseFailAlloc_1845_, 5, v_exprToSemiringId_1797_);
lean_ctor_set(v_reuseFailAlloc_1845_, 6, v_ncRings_1798_);
lean_ctor_set(v_reuseFailAlloc_1845_, 7, v_exprToNCRingId_1799_);
lean_ctor_set(v_reuseFailAlloc_1845_, 8, v_nctypeIdOf_1800_);
lean_ctor_set(v_reuseFailAlloc_1845_, 9, v_ncSemirings_1801_);
lean_ctor_set(v_reuseFailAlloc_1845_, 10, v_exprToNCSemiringId_1802_);
lean_ctor_set(v_reuseFailAlloc_1845_, 11, v_ncstypeIdOf_1803_);
lean_ctor_set(v_reuseFailAlloc_1845_, 12, v_steps_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1845_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1805_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed(lean_object* v___y_1864_, lean_object* v_e_1865_, lean_object* v_size_1866_, lean_object* v_s_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(v___y_1864_, v_e_1865_, v_size_1866_, v_s_1867_);
lean_dec(v___y_1864_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(lean_object* v_e_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1933_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1933_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1933_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_toSemiring_1887_; lean_object* v_vars_1888_; lean_object* v_varMap_1889_; lean_object* v___x_1890_; 
v_toSemiring_1887_ = lean_ctor_get(v_a_1883_, 0);
lean_inc_ref(v_toSemiring_1887_);
lean_dec(v_a_1883_);
v_vars_1888_ = lean_ctor_get(v_toSemiring_1887_, 9);
lean_inc_ref(v_vars_1888_);
v_varMap_1889_ = lean_ctor_get(v_toSemiring_1887_, 10);
lean_inc_ref(v_varMap_1889_);
lean_dec_ref(v_toSemiring_1887_);
v___x_1890_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_varMap_1889_, v_e_1869_);
lean_dec_ref(v_varMap_1889_);
if (lean_obj_tag(v___x_1890_) == 1)
{
lean_object* v_val_1891_; lean_object* v___x_1893_; 
lean_dec_ref(v_vars_1888_);
lean_dec_ref(v_e_1869_);
v_val_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_val_1891_);
lean_dec_ref(v___x_1890_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v_val_1891_);
v___x_1893_ = v___x_1885_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_val_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
else
{
lean_object* v_size_1895_; lean_object* v___f_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec(v___x_1890_);
lean_del_object(v___x_1885_);
v_size_1895_ = lean_ctor_get(v_vars_1888_, 2);
lean_inc_n(v_size_1895_, 2);
lean_dec_ref(v_vars_1888_);
lean_inc_ref(v_e_1869_);
lean_inc(v___y_1870_);
v___f_1896_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1896_, 0, v___y_1870_);
lean_closure_set(v___f_1896_, 1, v_e_1869_);
lean_closure_set(v___f_1896_, 2, v_size_1895_);
v___x_1897_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1898_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1897_, v___f_1896_, v___y_1871_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v___x_1899_; 
lean_dec_ref(v___x_1898_);
lean_inc_ref(v_e_1869_);
v___x_1899_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1869_, v___y_1870_, v___y_1871_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v___x_1900_; 
lean_dec_ref(v___x_1899_);
v___x_1900_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1897_, v_e_1869_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1907_ == 0)
{
lean_object* v_unused_1908_; 
v_unused_1908_ = lean_ctor_get(v___x_1900_, 0);
lean_dec(v_unused_1908_);
v___x_1902_ = v___x_1900_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_dec(v___x_1900_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v_size_1895_);
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_size_1895_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_size_1895_);
v_a_1909_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1900_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1900_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_size_1895_);
lean_dec_ref(v_e_1869_);
v_a_1917_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1899_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1899_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v_size_1895_);
lean_dec_ref(v_e_1869_);
v_a_1925_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1898_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1898_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec_ref(v_e_1869_);
v_a_1934_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1882_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1882_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___boxed(lean_object* v_e_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec(v___y_1943_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object* v_e_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar___boxed(lean_object* v_e_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVar(v_e_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec(v_a_1971_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_nat_to_int(v_a_1984_);
return v___x_1985_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object* v_msg_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; lean_object* v___f_2001_; lean_object* v___x_40218__overap_2002_; lean_object* v___x_2003_; 
v___x_2000_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0);
v___f_2001_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2001_, 0, v___x_2000_);
v___x_40218__overap_2002_ = lean_panic_fn_borrowed(v___f_2001_, v_msg_1987_);
lean_dec_ref(v___f_2001_);
lean_inc(v___y_1998_);
lean_inc_ref(v___y_1997_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1995_);
lean_inc(v___y_1994_);
lean_inc_ref(v___y_1993_);
lean_inc(v___y_1992_);
lean_inc_ref(v___y_1991_);
lean_inc(v___y_1990_);
lean_inc(v___y_1989_);
lean_inc(v___y_1988_);
v___x_2003_ = lean_apply_12(v___x_40218__overap_2002_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, lean_box(0));
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object* v_msg_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_msg_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec(v___y_2005_);
return v_res_2017_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0));
v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(lean_object* v_type_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2027_; 
lean_inc_ref(v_type_2021_);
v___x_2027_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2040_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2040_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2040_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
if (lean_obj_tag(v_a_2028_) == 1)
{
lean_object* v_val_2032_; lean_object* v___x_2034_; 
lean_dec_ref(v_type_2021_);
v_val_2032_ = lean_ctor_get(v_a_2028_, 0);
lean_inc(v_val_2032_);
lean_dec_ref(v_a_2028_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v_val_2032_);
v___x_2034_ = v___x_2030_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_val_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_del_object(v___x_2030_);
lean_dec(v_a_2028_);
v___x_2036_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1);
v___x_2037_ = l_Lean_indentExpr(v_type_2021_);
v___x_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_2038_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
return v___x_2039_;
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v_type_2021_);
v_a_2041_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2027_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2027_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_type_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(lean_object* v_type_2056_, lean_object* v_u_2057_, lean_object* v_instDeclName_2058_, lean_object* v_declName_2059_, lean_object* v_expectedInst_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2073_ = lean_box(0);
lean_inc_n(v_u_2057_, 2);
v___x_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_u_2057_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_u_2057_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_u_2057_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
lean_inc_ref(v___x_2076_);
v___x_2077_ = l_Lean_mkConst(v_instDeclName_2058_, v___x_2076_);
lean_inc_ref_n(v_type_2056_, 3);
v___x_2078_ = l_Lean_mkApp3(v___x_2077_, v_type_2056_, v_type_2056_, v_type_2056_);
v___x_2079_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2078_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2081_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc_n(v_a_2080_, 2);
lean_dec_ref(v___x_2079_);
lean_inc(v_declName_2059_);
v___x_2081_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2059_, v_a_2080_, v_expectedInst_2060_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec_ref(v___x_2081_);
v___x_2082_ = l_Lean_mkConst(v_declName_2059_, v___x_2076_);
lean_inc_ref_n(v_type_2056_, 2);
v___x_2083_ = l_Lean_mkApp4(v___x_2082_, v_type_2056_, v_type_2056_, v_type_2056_, v_a_2080_);
v___x_2084_ = l_Lean_Meta_Sym_canon(v___x_2083_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2084_);
v___x_2086_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2085_, v___y_2067_);
return v___x_2086_;
}
else
{
return v___x_2084_;
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_a_2080_);
lean_dec_ref(v___x_2076_);
lean_dec(v_declName_2059_);
lean_dec_ref(v_type_2056_);
v_a_2087_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2081_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2081_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_expectedInst_2060_);
lean_dec(v_declName_2059_);
lean_dec_ref(v_type_2056_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_type_2095_ = _args[0];
lean_object* v_u_2096_ = _args[1];
lean_object* v_instDeclName_2097_ = _args[2];
lean_object* v_declName_2098_ = _args[3];
lean_object* v_expectedInst_2099_ = _args[4];
lean_object* v___y_2100_ = _args[5];
lean_object* v___y_2101_ = _args[6];
lean_object* v___y_2102_ = _args[7];
lean_object* v___y_2103_ = _args[8];
lean_object* v___y_2104_ = _args[9];
lean_object* v___y_2105_ = _args[10];
lean_object* v___y_2106_ = _args[11];
lean_object* v___y_2107_ = _args[12];
lean_object* v___y_2108_ = _args[13];
lean_object* v___y_2109_ = _args[14];
lean_object* v___y_2110_ = _args[15];
lean_object* v___y_2111_ = _args[16];
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2095_, v_u_2096_, v_instDeclName_2097_, v_declName_2098_, v_expectedInst_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec(v___y_2100_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object* v_a_2113_, lean_object* v_s_2114_){
_start:
{
lean_object* v_toRing_2115_; lean_object* v_invFn_x3f_2116_; lean_object* v_semiringId_x3f_2117_; lean_object* v_commSemiringInst_2118_; lean_object* v_commRingInst_2119_; lean_object* v_noZeroDivInst_x3f_2120_; lean_object* v_fieldInst_x3f_2121_; lean_object* v_powIdentityInst_x3f_2122_; lean_object* v_denoteEntries_2123_; lean_object* v_nextId_2124_; lean_object* v_steps_2125_; lean_object* v_queue_2126_; lean_object* v_basis_2127_; lean_object* v_diseqs_2128_; uint8_t v_recheck_2129_; lean_object* v_invSet_2130_; lean_object* v_powIdentityVarCount_2131_; lean_object* v_numEq0_x3f_2132_; uint8_t v_numEq0Updated_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2165_; 
v_toRing_2115_ = lean_ctor_get(v_s_2114_, 0);
v_invFn_x3f_2116_ = lean_ctor_get(v_s_2114_, 1);
v_semiringId_x3f_2117_ = lean_ctor_get(v_s_2114_, 2);
v_commSemiringInst_2118_ = lean_ctor_get(v_s_2114_, 3);
v_commRingInst_2119_ = lean_ctor_get(v_s_2114_, 4);
v_noZeroDivInst_x3f_2120_ = lean_ctor_get(v_s_2114_, 5);
v_fieldInst_x3f_2121_ = lean_ctor_get(v_s_2114_, 6);
v_powIdentityInst_x3f_2122_ = lean_ctor_get(v_s_2114_, 7);
v_denoteEntries_2123_ = lean_ctor_get(v_s_2114_, 8);
v_nextId_2124_ = lean_ctor_get(v_s_2114_, 9);
v_steps_2125_ = lean_ctor_get(v_s_2114_, 10);
v_queue_2126_ = lean_ctor_get(v_s_2114_, 11);
v_basis_2127_ = lean_ctor_get(v_s_2114_, 12);
v_diseqs_2128_ = lean_ctor_get(v_s_2114_, 13);
v_recheck_2129_ = lean_ctor_get_uint8(v_s_2114_, sizeof(void*)*17);
v_invSet_2130_ = lean_ctor_get(v_s_2114_, 14);
v_powIdentityVarCount_2131_ = lean_ctor_get(v_s_2114_, 15);
v_numEq0_x3f_2132_ = lean_ctor_get(v_s_2114_, 16);
v_numEq0Updated_2133_ = lean_ctor_get_uint8(v_s_2114_, sizeof(void*)*17 + 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_s_2114_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2135_ = v_s_2114_;
v_isShared_2136_ = v_isSharedCheck_2165_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_numEq0_x3f_2132_);
lean_inc(v_powIdentityVarCount_2131_);
lean_inc(v_invSet_2130_);
lean_inc(v_diseqs_2128_);
lean_inc(v_basis_2127_);
lean_inc(v_queue_2126_);
lean_inc(v_steps_2125_);
lean_inc(v_nextId_2124_);
lean_inc(v_denoteEntries_2123_);
lean_inc(v_powIdentityInst_x3f_2122_);
lean_inc(v_fieldInst_x3f_2121_);
lean_inc(v_noZeroDivInst_x3f_2120_);
lean_inc(v_commRingInst_2119_);
lean_inc(v_commSemiringInst_2118_);
lean_inc(v_semiringId_x3f_2117_);
lean_inc(v_invFn_x3f_2116_);
lean_inc(v_toRing_2115_);
lean_dec(v_s_2114_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2165_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_id_2137_; lean_object* v_type_2138_; lean_object* v_u_2139_; lean_object* v_ringInst_2140_; lean_object* v_semiringInst_2141_; lean_object* v_charInst_x3f_2142_; lean_object* v_addFn_x3f_2143_; lean_object* v_subFn_x3f_2144_; lean_object* v_negFn_x3f_2145_; lean_object* v_powFn_x3f_2146_; lean_object* v_intCastFn_x3f_2147_; lean_object* v_natCastFn_x3f_2148_; lean_object* v_one_x3f_2149_; lean_object* v_vars_2150_; lean_object* v_varMap_2151_; lean_object* v_denote_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2163_; 
v_id_2137_ = lean_ctor_get(v_toRing_2115_, 0);
v_type_2138_ = lean_ctor_get(v_toRing_2115_, 1);
v_u_2139_ = lean_ctor_get(v_toRing_2115_, 2);
v_ringInst_2140_ = lean_ctor_get(v_toRing_2115_, 3);
v_semiringInst_2141_ = lean_ctor_get(v_toRing_2115_, 4);
v_charInst_x3f_2142_ = lean_ctor_get(v_toRing_2115_, 5);
v_addFn_x3f_2143_ = lean_ctor_get(v_toRing_2115_, 6);
v_subFn_x3f_2144_ = lean_ctor_get(v_toRing_2115_, 8);
v_negFn_x3f_2145_ = lean_ctor_get(v_toRing_2115_, 9);
v_powFn_x3f_2146_ = lean_ctor_get(v_toRing_2115_, 10);
v_intCastFn_x3f_2147_ = lean_ctor_get(v_toRing_2115_, 11);
v_natCastFn_x3f_2148_ = lean_ctor_get(v_toRing_2115_, 12);
v_one_x3f_2149_ = lean_ctor_get(v_toRing_2115_, 13);
v_vars_2150_ = lean_ctor_get(v_toRing_2115_, 14);
v_varMap_2151_ = lean_ctor_get(v_toRing_2115_, 15);
v_denote_2152_ = lean_ctor_get(v_toRing_2115_, 16);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_toRing_2115_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; 
v_unused_2164_ = lean_ctor_get(v_toRing_2115_, 7);
lean_dec(v_unused_2164_);
v___x_2154_ = v_toRing_2115_;
v_isShared_2155_ = v_isSharedCheck_2163_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_denote_2152_);
lean_inc(v_varMap_2151_);
lean_inc(v_vars_2150_);
lean_inc(v_one_x3f_2149_);
lean_inc(v_natCastFn_x3f_2148_);
lean_inc(v_intCastFn_x3f_2147_);
lean_inc(v_powFn_x3f_2146_);
lean_inc(v_negFn_x3f_2145_);
lean_inc(v_subFn_x3f_2144_);
lean_inc(v_addFn_x3f_2143_);
lean_inc(v_charInst_x3f_2142_);
lean_inc(v_semiringInst_2141_);
lean_inc(v_ringInst_2140_);
lean_inc(v_u_2139_);
lean_inc(v_type_2138_);
lean_inc(v_id_2137_);
lean_dec(v_toRing_2115_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2163_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v_a_2113_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 7, v___x_2156_);
v___x_2158_ = v___x_2154_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_id_2137_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_type_2138_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_u_2139_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_ringInst_2140_);
lean_ctor_set(v_reuseFailAlloc_2162_, 4, v_semiringInst_2141_);
lean_ctor_set(v_reuseFailAlloc_2162_, 5, v_charInst_x3f_2142_);
lean_ctor_set(v_reuseFailAlloc_2162_, 6, v_addFn_x3f_2143_);
lean_ctor_set(v_reuseFailAlloc_2162_, 7, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2162_, 8, v_subFn_x3f_2144_);
lean_ctor_set(v_reuseFailAlloc_2162_, 9, v_negFn_x3f_2145_);
lean_ctor_set(v_reuseFailAlloc_2162_, 10, v_powFn_x3f_2146_);
lean_ctor_set(v_reuseFailAlloc_2162_, 11, v_intCastFn_x3f_2147_);
lean_ctor_set(v_reuseFailAlloc_2162_, 12, v_natCastFn_x3f_2148_);
lean_ctor_set(v_reuseFailAlloc_2162_, 13, v_one_x3f_2149_);
lean_ctor_set(v_reuseFailAlloc_2162_, 14, v_vars_2150_);
lean_ctor_set(v_reuseFailAlloc_2162_, 15, v_varMap_2151_);
lean_ctor_set(v_reuseFailAlloc_2162_, 16, v_denote_2152_);
v___x_2158_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2160_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2158_);
v___x_2160_ = v___x_2135_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_invFn_x3f_2116_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_semiringId_x3f_2117_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_commSemiringInst_2118_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v_commRingInst_2119_);
lean_ctor_set(v_reuseFailAlloc_2161_, 5, v_noZeroDivInst_x3f_2120_);
lean_ctor_set(v_reuseFailAlloc_2161_, 6, v_fieldInst_x3f_2121_);
lean_ctor_set(v_reuseFailAlloc_2161_, 7, v_powIdentityInst_x3f_2122_);
lean_ctor_set(v_reuseFailAlloc_2161_, 8, v_denoteEntries_2123_);
lean_ctor_set(v_reuseFailAlloc_2161_, 9, v_nextId_2124_);
lean_ctor_set(v_reuseFailAlloc_2161_, 10, v_steps_2125_);
lean_ctor_set(v_reuseFailAlloc_2161_, 11, v_queue_2126_);
lean_ctor_set(v_reuseFailAlloc_2161_, 12, v_basis_2127_);
lean_ctor_set(v_reuseFailAlloc_2161_, 13, v_diseqs_2128_);
lean_ctor_set(v_reuseFailAlloc_2161_, 14, v_invSet_2130_);
lean_ctor_set(v_reuseFailAlloc_2161_, 15, v_powIdentityVarCount_2131_);
lean_ctor_set(v_reuseFailAlloc_2161_, 16, v_numEq0_x3f_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2161_, sizeof(void*)*17, v_recheck_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2161_, sizeof(void*)*17 + 1, v_numEq0Updated_2133_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2222_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2222_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2222_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v_toRing_2183_; lean_object* v_mulFn_x3f_2184_; 
v_toRing_2183_ = lean_ctor_get(v_a_2179_, 0);
lean_inc_ref(v_toRing_2183_);
lean_dec(v_a_2179_);
v_mulFn_x3f_2184_ = lean_ctor_get(v_toRing_2183_, 7);
if (lean_obj_tag(v_mulFn_x3f_2184_) == 1)
{
lean_object* v_val_2185_; lean_object* v___x_2187_; 
lean_inc_ref(v_mulFn_x3f_2184_);
lean_dec_ref(v_toRing_2183_);
v_val_2185_ = lean_ctor_get(v_mulFn_x3f_2184_, 0);
lean_inc(v_val_2185_);
lean_dec_ref(v_mulFn_x3f_2184_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v_val_2185_);
v___x_2187_ = v___x_2181_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_val_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
else
{
lean_object* v_type_2189_; lean_object* v_u_2190_; lean_object* v_semiringInst_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v_expectedInst_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_del_object(v___x_2181_);
v_type_2189_ = lean_ctor_get(v_toRing_2183_, 1);
lean_inc_ref_n(v_type_2189_, 3);
v_u_2190_ = lean_ctor_get(v_toRing_2183_, 2);
lean_inc_n(v_u_2190_, 2);
v_semiringInst_2191_ = lean_ctor_get(v_toRing_2183_, 4);
lean_inc_ref(v_semiringInst_2191_);
lean_dec_ref(v_toRing_2183_);
v___x_2192_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_2193_ = lean_box(0);
v___x_2194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2194_, 0, v_u_2190_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
lean_inc_ref(v___x_2194_);
v___x_2195_ = l_Lean_mkConst(v___x_2192_, v___x_2194_);
v___x_2196_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_2197_ = l_Lean_mkConst(v___x_2196_, v___x_2194_);
v___x_2198_ = l_Lean_mkAppB(v___x_2197_, v_type_2189_, v_semiringInst_2191_);
v_expectedInst_2199_ = l_Lean_mkAppB(v___x_2195_, v_type_2189_, v___x_2198_);
v___x_2200_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_2201_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_2202_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2189_, v_u_2190_, v___x_2200_, v___x_2201_, v_expectedInst_2199_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc_n(v_a_2203_, 2);
lean_dec_ref(v___x_2202_);
v___f_2204_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2204_, 0, v_a_2203_);
v___x_2205_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2204_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v___x_2205_, 0);
lean_dec(v_unused_2213_);
v___x_2207_ = v___x_2205_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_dec(v___x_2205_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v_a_2203_);
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2203_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_a_2203_);
v_a_2214_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2205_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2205_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
v_a_2223_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2178_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2178_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec(v___y_2231_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object* v_a_2244_, lean_object* v_s_2245_){
_start:
{
lean_object* v_toRing_2246_; lean_object* v_invFn_x3f_2247_; lean_object* v_semiringId_x3f_2248_; lean_object* v_commSemiringInst_2249_; lean_object* v_commRingInst_2250_; lean_object* v_noZeroDivInst_x3f_2251_; lean_object* v_fieldInst_x3f_2252_; lean_object* v_powIdentityInst_x3f_2253_; lean_object* v_denoteEntries_2254_; lean_object* v_nextId_2255_; lean_object* v_steps_2256_; lean_object* v_queue_2257_; lean_object* v_basis_2258_; lean_object* v_diseqs_2259_; uint8_t v_recheck_2260_; lean_object* v_invSet_2261_; lean_object* v_powIdentityVarCount_2262_; lean_object* v_numEq0_x3f_2263_; uint8_t v_numEq0Updated_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2296_; 
v_toRing_2246_ = lean_ctor_get(v_s_2245_, 0);
v_invFn_x3f_2247_ = lean_ctor_get(v_s_2245_, 1);
v_semiringId_x3f_2248_ = lean_ctor_get(v_s_2245_, 2);
v_commSemiringInst_2249_ = lean_ctor_get(v_s_2245_, 3);
v_commRingInst_2250_ = lean_ctor_get(v_s_2245_, 4);
v_noZeroDivInst_x3f_2251_ = lean_ctor_get(v_s_2245_, 5);
v_fieldInst_x3f_2252_ = lean_ctor_get(v_s_2245_, 6);
v_powIdentityInst_x3f_2253_ = lean_ctor_get(v_s_2245_, 7);
v_denoteEntries_2254_ = lean_ctor_get(v_s_2245_, 8);
v_nextId_2255_ = lean_ctor_get(v_s_2245_, 9);
v_steps_2256_ = lean_ctor_get(v_s_2245_, 10);
v_queue_2257_ = lean_ctor_get(v_s_2245_, 11);
v_basis_2258_ = lean_ctor_get(v_s_2245_, 12);
v_diseqs_2259_ = lean_ctor_get(v_s_2245_, 13);
v_recheck_2260_ = lean_ctor_get_uint8(v_s_2245_, sizeof(void*)*17);
v_invSet_2261_ = lean_ctor_get(v_s_2245_, 14);
v_powIdentityVarCount_2262_ = lean_ctor_get(v_s_2245_, 15);
v_numEq0_x3f_2263_ = lean_ctor_get(v_s_2245_, 16);
v_numEq0Updated_2264_ = lean_ctor_get_uint8(v_s_2245_, sizeof(void*)*17 + 1);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_s_2245_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2266_ = v_s_2245_;
v_isShared_2267_ = v_isSharedCheck_2296_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_numEq0_x3f_2263_);
lean_inc(v_powIdentityVarCount_2262_);
lean_inc(v_invSet_2261_);
lean_inc(v_diseqs_2259_);
lean_inc(v_basis_2258_);
lean_inc(v_queue_2257_);
lean_inc(v_steps_2256_);
lean_inc(v_nextId_2255_);
lean_inc(v_denoteEntries_2254_);
lean_inc(v_powIdentityInst_x3f_2253_);
lean_inc(v_fieldInst_x3f_2252_);
lean_inc(v_noZeroDivInst_x3f_2251_);
lean_inc(v_commRingInst_2250_);
lean_inc(v_commSemiringInst_2249_);
lean_inc(v_semiringId_x3f_2248_);
lean_inc(v_invFn_x3f_2247_);
lean_inc(v_toRing_2246_);
lean_dec(v_s_2245_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2296_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v_id_2268_; lean_object* v_type_2269_; lean_object* v_u_2270_; lean_object* v_ringInst_2271_; lean_object* v_semiringInst_2272_; lean_object* v_charInst_x3f_2273_; lean_object* v_mulFn_x3f_2274_; lean_object* v_subFn_x3f_2275_; lean_object* v_negFn_x3f_2276_; lean_object* v_powFn_x3f_2277_; lean_object* v_intCastFn_x3f_2278_; lean_object* v_natCastFn_x3f_2279_; lean_object* v_one_x3f_2280_; lean_object* v_vars_2281_; lean_object* v_varMap_2282_; lean_object* v_denote_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2294_; 
v_id_2268_ = lean_ctor_get(v_toRing_2246_, 0);
v_type_2269_ = lean_ctor_get(v_toRing_2246_, 1);
v_u_2270_ = lean_ctor_get(v_toRing_2246_, 2);
v_ringInst_2271_ = lean_ctor_get(v_toRing_2246_, 3);
v_semiringInst_2272_ = lean_ctor_get(v_toRing_2246_, 4);
v_charInst_x3f_2273_ = lean_ctor_get(v_toRing_2246_, 5);
v_mulFn_x3f_2274_ = lean_ctor_get(v_toRing_2246_, 7);
v_subFn_x3f_2275_ = lean_ctor_get(v_toRing_2246_, 8);
v_negFn_x3f_2276_ = lean_ctor_get(v_toRing_2246_, 9);
v_powFn_x3f_2277_ = lean_ctor_get(v_toRing_2246_, 10);
v_intCastFn_x3f_2278_ = lean_ctor_get(v_toRing_2246_, 11);
v_natCastFn_x3f_2279_ = lean_ctor_get(v_toRing_2246_, 12);
v_one_x3f_2280_ = lean_ctor_get(v_toRing_2246_, 13);
v_vars_2281_ = lean_ctor_get(v_toRing_2246_, 14);
v_varMap_2282_ = lean_ctor_get(v_toRing_2246_, 15);
v_denote_2283_ = lean_ctor_get(v_toRing_2246_, 16);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_toRing_2246_);
if (v_isSharedCheck_2294_ == 0)
{
lean_object* v_unused_2295_; 
v_unused_2295_ = lean_ctor_get(v_toRing_2246_, 6);
lean_dec(v_unused_2295_);
v___x_2285_ = v_toRing_2246_;
v_isShared_2286_ = v_isSharedCheck_2294_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_denote_2283_);
lean_inc(v_varMap_2282_);
lean_inc(v_vars_2281_);
lean_inc(v_one_x3f_2280_);
lean_inc(v_natCastFn_x3f_2279_);
lean_inc(v_intCastFn_x3f_2278_);
lean_inc(v_powFn_x3f_2277_);
lean_inc(v_negFn_x3f_2276_);
lean_inc(v_subFn_x3f_2275_);
lean_inc(v_mulFn_x3f_2274_);
lean_inc(v_charInst_x3f_2273_);
lean_inc(v_semiringInst_2272_);
lean_inc(v_ringInst_2271_);
lean_inc(v_u_2270_);
lean_inc(v_type_2269_);
lean_inc(v_id_2268_);
lean_dec(v_toRing_2246_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2294_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2287_, 0, v_a_2244_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 6, v___x_2287_);
v___x_2289_ = v___x_2285_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_id_2268_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_type_2269_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_u_2270_);
lean_ctor_set(v_reuseFailAlloc_2293_, 3, v_ringInst_2271_);
lean_ctor_set(v_reuseFailAlloc_2293_, 4, v_semiringInst_2272_);
lean_ctor_set(v_reuseFailAlloc_2293_, 5, v_charInst_x3f_2273_);
lean_ctor_set(v_reuseFailAlloc_2293_, 6, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2293_, 7, v_mulFn_x3f_2274_);
lean_ctor_set(v_reuseFailAlloc_2293_, 8, v_subFn_x3f_2275_);
lean_ctor_set(v_reuseFailAlloc_2293_, 9, v_negFn_x3f_2276_);
lean_ctor_set(v_reuseFailAlloc_2293_, 10, v_powFn_x3f_2277_);
lean_ctor_set(v_reuseFailAlloc_2293_, 11, v_intCastFn_x3f_2278_);
lean_ctor_set(v_reuseFailAlloc_2293_, 12, v_natCastFn_x3f_2279_);
lean_ctor_set(v_reuseFailAlloc_2293_, 13, v_one_x3f_2280_);
lean_ctor_set(v_reuseFailAlloc_2293_, 14, v_vars_2281_);
lean_ctor_set(v_reuseFailAlloc_2293_, 15, v_varMap_2282_);
lean_ctor_set(v_reuseFailAlloc_2293_, 16, v_denote_2283_);
v___x_2289_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2291_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2289_);
v___x_2291_ = v___x_2266_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_invFn_x3f_2247_);
lean_ctor_set(v_reuseFailAlloc_2292_, 2, v_semiringId_x3f_2248_);
lean_ctor_set(v_reuseFailAlloc_2292_, 3, v_commSemiringInst_2249_);
lean_ctor_set(v_reuseFailAlloc_2292_, 4, v_commRingInst_2250_);
lean_ctor_set(v_reuseFailAlloc_2292_, 5, v_noZeroDivInst_x3f_2251_);
lean_ctor_set(v_reuseFailAlloc_2292_, 6, v_fieldInst_x3f_2252_);
lean_ctor_set(v_reuseFailAlloc_2292_, 7, v_powIdentityInst_x3f_2253_);
lean_ctor_set(v_reuseFailAlloc_2292_, 8, v_denoteEntries_2254_);
lean_ctor_set(v_reuseFailAlloc_2292_, 9, v_nextId_2255_);
lean_ctor_set(v_reuseFailAlloc_2292_, 10, v_steps_2256_);
lean_ctor_set(v_reuseFailAlloc_2292_, 11, v_queue_2257_);
lean_ctor_set(v_reuseFailAlloc_2292_, 12, v_basis_2258_);
lean_ctor_set(v_reuseFailAlloc_2292_, 13, v_diseqs_2259_);
lean_ctor_set(v_reuseFailAlloc_2292_, 14, v_invSet_2261_);
lean_ctor_set(v_reuseFailAlloc_2292_, 15, v_powIdentityVarCount_2262_);
lean_ctor_set(v_reuseFailAlloc_2292_, 16, v_numEq0_x3f_2263_);
lean_ctor_set_uint8(v_reuseFailAlloc_2292_, sizeof(void*)*17, v_recheck_2260_);
lean_ctor_set_uint8(v_reuseFailAlloc_2292_, sizeof(void*)*17 + 1, v_numEq0Updated_2264_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2353_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2353_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2353_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v_toRing_2314_; lean_object* v_addFn_x3f_2315_; 
v_toRing_2314_ = lean_ctor_get(v_a_2310_, 0);
lean_inc_ref(v_toRing_2314_);
lean_dec(v_a_2310_);
v_addFn_x3f_2315_ = lean_ctor_get(v_toRing_2314_, 6);
if (lean_obj_tag(v_addFn_x3f_2315_) == 1)
{
lean_object* v_val_2316_; lean_object* v___x_2318_; 
lean_inc_ref(v_addFn_x3f_2315_);
lean_dec_ref(v_toRing_2314_);
v_val_2316_ = lean_ctor_get(v_addFn_x3f_2315_, 0);
lean_inc(v_val_2316_);
lean_dec_ref(v_addFn_x3f_2315_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v_val_2316_);
v___x_2318_ = v___x_2312_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_val_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
else
{
lean_object* v_type_2320_; lean_object* v_u_2321_; lean_object* v_semiringInst_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v_expectedInst_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_del_object(v___x_2312_);
v_type_2320_ = lean_ctor_get(v_toRing_2314_, 1);
lean_inc_ref_n(v_type_2320_, 3);
v_u_2321_ = lean_ctor_get(v_toRing_2314_, 2);
lean_inc_n(v_u_2321_, 2);
v_semiringInst_2322_ = lean_ctor_get(v_toRing_2314_, 4);
lean_inc_ref(v_semiringInst_2322_);
lean_dec_ref(v_toRing_2314_);
v___x_2323_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_2324_ = lean_box(0);
v___x_2325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2325_, 0, v_u_2321_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
lean_inc_ref(v___x_2325_);
v___x_2326_ = l_Lean_mkConst(v___x_2323_, v___x_2325_);
v___x_2327_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_2328_ = l_Lean_mkConst(v___x_2327_, v___x_2325_);
v___x_2329_ = l_Lean_mkAppB(v___x_2328_, v_type_2320_, v_semiringInst_2322_);
v_expectedInst_2330_ = l_Lean_mkAppB(v___x_2326_, v_type_2320_, v___x_2329_);
v___x_2331_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_2332_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_2333_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2320_, v_u_2321_, v___x_2331_, v___x_2332_, v_expectedInst_2330_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___f_2335_; lean_object* v___x_2336_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc_n(v_a_2334_, 2);
lean_dec_ref(v___x_2333_);
v___f_2335_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_2335_, 0, v_a_2334_);
v___x_2336_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2335_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2343_ == 0)
{
lean_object* v_unused_2344_; 
v_unused_2344_ = lean_ctor_get(v___x_2336_, 0);
lean_dec(v_unused_2344_);
v___x_2338_ = v___x_2336_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_dec(v___x_2336_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v_a_2334_);
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2334_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_a_2334_);
v_a_2345_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2336_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2336_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
return v___x_2333_;
}
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
v_a_2354_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2309_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2309_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec(v___y_2362_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(lean_object* v_type_2375_, lean_object* v_u_2376_, lean_object* v_instDeclName_2377_, lean_object* v_declName_2378_, lean_object* v_expectedInst_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2392_ = lean_box(0);
v___x_2393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2393_, 0, v_u_2376_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
lean_inc_ref(v___x_2393_);
v___x_2394_ = l_Lean_mkConst(v_instDeclName_2377_, v___x_2393_);
lean_inc_ref(v_type_2375_);
v___x_2395_ = l_Lean_Expr_app___override(v___x_2394_, v_type_2375_);
v___x_2396_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2395_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2398_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc_n(v_a_2397_, 2);
lean_dec_ref(v___x_2396_);
lean_inc(v_declName_2378_);
v___x_2398_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2378_, v_a_2397_, v_expectedInst_2379_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
lean_dec_ref(v___x_2398_);
v___x_2399_ = l_Lean_mkConst(v_declName_2378_, v___x_2393_);
v___x_2400_ = l_Lean_mkAppB(v___x_2399_, v_type_2375_, v_a_2397_);
v___x_2401_ = l_Lean_Meta_Sym_canon(v___x_2400_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2403_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref(v___x_2401_);
v___x_2403_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2402_, v___y_2386_);
return v___x_2403_;
}
else
{
return v___x_2401_;
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_a_2397_);
lean_dec_ref(v___x_2393_);
lean_dec(v_declName_2378_);
lean_dec_ref(v_type_2375_);
v_a_2404_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2398_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2398_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_dec_ref(v___x_2393_);
lean_dec_ref(v_expectedInst_2379_);
lean_dec(v_declName_2378_);
lean_dec_ref(v_type_2375_);
return v___x_2396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_type_2412_ = _args[0];
lean_object* v_u_2413_ = _args[1];
lean_object* v_instDeclName_2414_ = _args[2];
lean_object* v_declName_2415_ = _args[3];
lean_object* v_expectedInst_2416_ = _args[4];
lean_object* v___y_2417_ = _args[5];
lean_object* v___y_2418_ = _args[6];
lean_object* v___y_2419_ = _args[7];
lean_object* v___y_2420_ = _args[8];
lean_object* v___y_2421_ = _args[9];
lean_object* v___y_2422_ = _args[10];
lean_object* v___y_2423_ = _args[11];
lean_object* v___y_2424_ = _args[12];
lean_object* v___y_2425_ = _args[13];
lean_object* v___y_2426_ = _args[14];
lean_object* v___y_2427_ = _args[15];
lean_object* v___y_2428_ = _args[16];
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2412_, v_u_2413_, v_instDeclName_2414_, v_declName_2415_, v_expectedInst_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec(v___y_2417_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object* v_a_2430_, lean_object* v_s_2431_){
_start:
{
lean_object* v_toRing_2432_; lean_object* v_invFn_x3f_2433_; lean_object* v_semiringId_x3f_2434_; lean_object* v_commSemiringInst_2435_; lean_object* v_commRingInst_2436_; lean_object* v_noZeroDivInst_x3f_2437_; lean_object* v_fieldInst_x3f_2438_; lean_object* v_powIdentityInst_x3f_2439_; lean_object* v_denoteEntries_2440_; lean_object* v_nextId_2441_; lean_object* v_steps_2442_; lean_object* v_queue_2443_; lean_object* v_basis_2444_; lean_object* v_diseqs_2445_; uint8_t v_recheck_2446_; lean_object* v_invSet_2447_; lean_object* v_powIdentityVarCount_2448_; lean_object* v_numEq0_x3f_2449_; uint8_t v_numEq0Updated_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2482_; 
v_toRing_2432_ = lean_ctor_get(v_s_2431_, 0);
v_invFn_x3f_2433_ = lean_ctor_get(v_s_2431_, 1);
v_semiringId_x3f_2434_ = lean_ctor_get(v_s_2431_, 2);
v_commSemiringInst_2435_ = lean_ctor_get(v_s_2431_, 3);
v_commRingInst_2436_ = lean_ctor_get(v_s_2431_, 4);
v_noZeroDivInst_x3f_2437_ = lean_ctor_get(v_s_2431_, 5);
v_fieldInst_x3f_2438_ = lean_ctor_get(v_s_2431_, 6);
v_powIdentityInst_x3f_2439_ = lean_ctor_get(v_s_2431_, 7);
v_denoteEntries_2440_ = lean_ctor_get(v_s_2431_, 8);
v_nextId_2441_ = lean_ctor_get(v_s_2431_, 9);
v_steps_2442_ = lean_ctor_get(v_s_2431_, 10);
v_queue_2443_ = lean_ctor_get(v_s_2431_, 11);
v_basis_2444_ = lean_ctor_get(v_s_2431_, 12);
v_diseqs_2445_ = lean_ctor_get(v_s_2431_, 13);
v_recheck_2446_ = lean_ctor_get_uint8(v_s_2431_, sizeof(void*)*17);
v_invSet_2447_ = lean_ctor_get(v_s_2431_, 14);
v_powIdentityVarCount_2448_ = lean_ctor_get(v_s_2431_, 15);
v_numEq0_x3f_2449_ = lean_ctor_get(v_s_2431_, 16);
v_numEq0Updated_2450_ = lean_ctor_get_uint8(v_s_2431_, sizeof(void*)*17 + 1);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_s_2431_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2452_ = v_s_2431_;
v_isShared_2453_ = v_isSharedCheck_2482_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_numEq0_x3f_2449_);
lean_inc(v_powIdentityVarCount_2448_);
lean_inc(v_invSet_2447_);
lean_inc(v_diseqs_2445_);
lean_inc(v_basis_2444_);
lean_inc(v_queue_2443_);
lean_inc(v_steps_2442_);
lean_inc(v_nextId_2441_);
lean_inc(v_denoteEntries_2440_);
lean_inc(v_powIdentityInst_x3f_2439_);
lean_inc(v_fieldInst_x3f_2438_);
lean_inc(v_noZeroDivInst_x3f_2437_);
lean_inc(v_commRingInst_2436_);
lean_inc(v_commSemiringInst_2435_);
lean_inc(v_semiringId_x3f_2434_);
lean_inc(v_invFn_x3f_2433_);
lean_inc(v_toRing_2432_);
lean_dec(v_s_2431_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2482_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v_id_2454_; lean_object* v_type_2455_; lean_object* v_u_2456_; lean_object* v_ringInst_2457_; lean_object* v_semiringInst_2458_; lean_object* v_charInst_x3f_2459_; lean_object* v_addFn_x3f_2460_; lean_object* v_mulFn_x3f_2461_; lean_object* v_subFn_x3f_2462_; lean_object* v_powFn_x3f_2463_; lean_object* v_intCastFn_x3f_2464_; lean_object* v_natCastFn_x3f_2465_; lean_object* v_one_x3f_2466_; lean_object* v_vars_2467_; lean_object* v_varMap_2468_; lean_object* v_denote_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2480_; 
v_id_2454_ = lean_ctor_get(v_toRing_2432_, 0);
v_type_2455_ = lean_ctor_get(v_toRing_2432_, 1);
v_u_2456_ = lean_ctor_get(v_toRing_2432_, 2);
v_ringInst_2457_ = lean_ctor_get(v_toRing_2432_, 3);
v_semiringInst_2458_ = lean_ctor_get(v_toRing_2432_, 4);
v_charInst_x3f_2459_ = lean_ctor_get(v_toRing_2432_, 5);
v_addFn_x3f_2460_ = lean_ctor_get(v_toRing_2432_, 6);
v_mulFn_x3f_2461_ = lean_ctor_get(v_toRing_2432_, 7);
v_subFn_x3f_2462_ = lean_ctor_get(v_toRing_2432_, 8);
v_powFn_x3f_2463_ = lean_ctor_get(v_toRing_2432_, 10);
v_intCastFn_x3f_2464_ = lean_ctor_get(v_toRing_2432_, 11);
v_natCastFn_x3f_2465_ = lean_ctor_get(v_toRing_2432_, 12);
v_one_x3f_2466_ = lean_ctor_get(v_toRing_2432_, 13);
v_vars_2467_ = lean_ctor_get(v_toRing_2432_, 14);
v_varMap_2468_ = lean_ctor_get(v_toRing_2432_, 15);
v_denote_2469_ = lean_ctor_get(v_toRing_2432_, 16);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_toRing_2432_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v_toRing_2432_, 9);
lean_dec(v_unused_2481_);
v___x_2471_ = v_toRing_2432_;
v_isShared_2472_ = v_isSharedCheck_2480_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_denote_2469_);
lean_inc(v_varMap_2468_);
lean_inc(v_vars_2467_);
lean_inc(v_one_x3f_2466_);
lean_inc(v_natCastFn_x3f_2465_);
lean_inc(v_intCastFn_x3f_2464_);
lean_inc(v_powFn_x3f_2463_);
lean_inc(v_subFn_x3f_2462_);
lean_inc(v_mulFn_x3f_2461_);
lean_inc(v_addFn_x3f_2460_);
lean_inc(v_charInst_x3f_2459_);
lean_inc(v_semiringInst_2458_);
lean_inc(v_ringInst_2457_);
lean_inc(v_u_2456_);
lean_inc(v_type_2455_);
lean_inc(v_id_2454_);
lean_dec(v_toRing_2432_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2480_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2473_, 0, v_a_2430_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 9, v___x_2473_);
v___x_2475_ = v___x_2471_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_id_2454_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_type_2455_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v_u_2456_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v_ringInst_2457_);
lean_ctor_set(v_reuseFailAlloc_2479_, 4, v_semiringInst_2458_);
lean_ctor_set(v_reuseFailAlloc_2479_, 5, v_charInst_x3f_2459_);
lean_ctor_set(v_reuseFailAlloc_2479_, 6, v_addFn_x3f_2460_);
lean_ctor_set(v_reuseFailAlloc_2479_, 7, v_mulFn_x3f_2461_);
lean_ctor_set(v_reuseFailAlloc_2479_, 8, v_subFn_x3f_2462_);
lean_ctor_set(v_reuseFailAlloc_2479_, 9, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2479_, 10, v_powFn_x3f_2463_);
lean_ctor_set(v_reuseFailAlloc_2479_, 11, v_intCastFn_x3f_2464_);
lean_ctor_set(v_reuseFailAlloc_2479_, 12, v_natCastFn_x3f_2465_);
lean_ctor_set(v_reuseFailAlloc_2479_, 13, v_one_x3f_2466_);
lean_ctor_set(v_reuseFailAlloc_2479_, 14, v_vars_2467_);
lean_ctor_set(v_reuseFailAlloc_2479_, 15, v_varMap_2468_);
lean_ctor_set(v_reuseFailAlloc_2479_, 16, v_denote_2469_);
v___x_2475_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2477_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2475_);
v___x_2477_ = v___x_2452_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_invFn_x3f_2433_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_semiringId_x3f_2434_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v_commSemiringInst_2435_);
lean_ctor_set(v_reuseFailAlloc_2478_, 4, v_commRingInst_2436_);
lean_ctor_set(v_reuseFailAlloc_2478_, 5, v_noZeroDivInst_x3f_2437_);
lean_ctor_set(v_reuseFailAlloc_2478_, 6, v_fieldInst_x3f_2438_);
lean_ctor_set(v_reuseFailAlloc_2478_, 7, v_powIdentityInst_x3f_2439_);
lean_ctor_set(v_reuseFailAlloc_2478_, 8, v_denoteEntries_2440_);
lean_ctor_set(v_reuseFailAlloc_2478_, 9, v_nextId_2441_);
lean_ctor_set(v_reuseFailAlloc_2478_, 10, v_steps_2442_);
lean_ctor_set(v_reuseFailAlloc_2478_, 11, v_queue_2443_);
lean_ctor_set(v_reuseFailAlloc_2478_, 12, v_basis_2444_);
lean_ctor_set(v_reuseFailAlloc_2478_, 13, v_diseqs_2445_);
lean_ctor_set(v_reuseFailAlloc_2478_, 14, v_invSet_2447_);
lean_ctor_set(v_reuseFailAlloc_2478_, 15, v_powIdentityVarCount_2448_);
lean_ctor_set(v_reuseFailAlloc_2478_, 16, v_numEq0_x3f_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2478_, sizeof(void*)*17, v_recheck_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2478_, sizeof(void*)*17 + 1, v_numEq0Updated_2450_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2549_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2549_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2549_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v_toRing_2513_; lean_object* v_negFn_x3f_2514_; 
v_toRing_2513_ = lean_ctor_get(v_a_2509_, 0);
lean_inc_ref(v_toRing_2513_);
lean_dec(v_a_2509_);
v_negFn_x3f_2514_ = lean_ctor_get(v_toRing_2513_, 9);
if (lean_obj_tag(v_negFn_x3f_2514_) == 1)
{
lean_object* v_val_2515_; lean_object* v___x_2517_; 
lean_inc_ref(v_negFn_x3f_2514_);
lean_dec_ref(v_toRing_2513_);
v_val_2515_ = lean_ctor_get(v_negFn_x3f_2514_, 0);
lean_inc(v_val_2515_);
lean_dec_ref(v_negFn_x3f_2514_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v_val_2515_);
v___x_2517_ = v___x_2511_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_val_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
else
{
lean_object* v_type_2519_; lean_object* v_u_2520_; lean_object* v_ringInst_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v_expectedInst_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_del_object(v___x_2511_);
v_type_2519_ = lean_ctor_get(v_toRing_2513_, 1);
lean_inc_ref_n(v_type_2519_, 2);
v_u_2520_ = lean_ctor_get(v_toRing_2513_, 2);
lean_inc_n(v_u_2520_, 2);
v_ringInst_2521_ = lean_ctor_get(v_toRing_2513_, 3);
lean_inc_ref(v_ringInst_2521_);
lean_dec_ref(v_toRing_2513_);
v___x_2522_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1));
v___x_2523_ = lean_box(0);
v___x_2524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2524_, 0, v_u_2520_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = l_Lean_mkConst(v___x_2522_, v___x_2524_);
v_expectedInst_2526_ = l_Lean_mkAppB(v___x_2525_, v_type_2519_, v_ringInst_2521_);
v___x_2527_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3));
v___x_2528_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5));
v___x_2529_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2519_, v_u_2520_, v___x_2527_, v___x_2528_, v_expectedInst_2526_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___f_2531_; lean_object* v___x_2532_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc_n(v_a_2530_, 2);
lean_dec_ref(v___x_2529_);
v___f_2531_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_2531_, 0, v_a_2530_);
v___x_2532_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2531_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; 
v_unused_2540_ = lean_ctor_get(v___x_2532_, 0);
lean_dec(v_unused_2540_);
v___x_2534_ = v___x_2532_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_dec(v___x_2532_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v_a_2530_);
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2530_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_a_2530_);
v_a_2541_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2532_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2532_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
return v___x_2529_;
}
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
v_a_2550_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2508_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2508_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec(v___y_2558_);
return v_res_2570_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = lean_unsigned_to_nat(0u);
v___x_2579_ = lean_nat_to_int(v___x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object* v_k_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v_toRing_2600_; lean_object* v_type_2601_; lean_object* v_u_2602_; lean_object* v_semiringInst_2603_; lean_object* v___x_2604_; lean_object* v_n_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref(v___x_2598_);
v_toRing_2600_ = lean_ctor_get(v_a_2599_, 0);
lean_inc_ref(v_toRing_2600_);
lean_dec(v_a_2599_);
v_type_2601_ = lean_ctor_get(v_toRing_2600_, 1);
lean_inc_ref_n(v_type_2601_, 2);
v_u_2602_ = lean_ctor_get(v_toRing_2600_, 2);
lean_inc(v_u_2602_);
v_semiringInst_2603_ = lean_ctor_get(v_toRing_2600_, 4);
lean_inc_ref(v_semiringInst_2603_);
lean_dec_ref(v_toRing_2600_);
v___x_2604_ = lean_nat_abs(v_k_2585_);
v_n_2605_ = l_Lean_mkRawNatLit(v___x_2604_);
v___x_2606_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1));
v___x_2607_ = lean_box(0);
v___x_2608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2608_, 0, v_u_2602_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
lean_inc_ref(v___x_2608_);
v___x_2609_ = l_Lean_mkConst(v___x_2606_, v___x_2608_);
lean_inc_ref(v_n_2605_);
v___x_2610_ = l_Lean_mkAppB(v___x_2609_, v_type_2601_, v_n_2605_);
v___x_2611_ = lean_box(0);
v___x_2612_ = l_Lean_Meta_synthInstance_x3f(v___x_2610_, v___x_2611_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2652_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2652_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2652_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v_ofNatInst_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; 
if (lean_obj_tag(v_a_2613_) == 1)
{
lean_object* v_val_2648_; 
lean_dec_ref(v_semiringInst_2603_);
v_val_2648_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_val_2648_);
lean_dec_ref(v_a_2613_);
v_ofNatInst_2618_ = v_val_2648_;
v___y_2619_ = v___y_2586_;
v___y_2620_ = v___y_2587_;
v___y_2621_ = v___y_2588_;
v___y_2622_ = v___y_2589_;
v___y_2623_ = v___y_2590_;
v___y_2624_ = v___y_2591_;
v___y_2625_ = v___y_2592_;
v___y_2626_ = v___y_2593_;
v___y_2627_ = v___y_2594_;
v___y_2628_ = v___y_2595_;
v___y_2629_ = v___y_2596_;
goto v___jp_2617_;
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_dec(v_a_2613_);
v___x_2649_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5));
lean_inc_ref(v___x_2608_);
v___x_2650_ = l_Lean_mkConst(v___x_2649_, v___x_2608_);
lean_inc_ref(v_n_2605_);
lean_inc_ref(v_type_2601_);
v___x_2651_ = l_Lean_mkApp3(v___x_2650_, v_type_2601_, v_semiringInst_2603_, v_n_2605_);
v_ofNatInst_2618_ = v___x_2651_;
v___y_2619_ = v___y_2586_;
v___y_2620_ = v___y_2587_;
v___y_2621_ = v___y_2588_;
v___y_2622_ = v___y_2589_;
v___y_2623_ = v___y_2590_;
v___y_2624_ = v___y_2591_;
v___y_2625_ = v___y_2592_;
v___y_2626_ = v___y_2593_;
v___y_2627_ = v___y_2594_;
v___y_2628_ = v___y_2595_;
v___y_2629_ = v___y_2596_;
goto v___jp_2617_;
}
v___jp_2617_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v_n_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2630_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3));
v___x_2631_ = l_Lean_mkConst(v___x_2630_, v___x_2608_);
v_n_2632_ = l_Lean_mkApp3(v___x_2631_, v_type_2601_, v_n_2605_, v_ofNatInst_2618_);
v___x_2633_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4);
v___x_2634_ = lean_int_dec_lt(v_k_2585_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2636_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v_n_2632_);
v___x_2636_ = v___x_2615_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_n_2632_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
else
{
lean_object* v___x_2638_; 
lean_del_object(v___x_2615_);
v___x_2638_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2647_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2647_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2647_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = l_Lean_Expr_app___override(v_a_2639_, v_n_2632_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2643_);
v___x_2645_ = v___x_2641_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
else
{
lean_dec_ref(v_n_2632_);
return v___x_2638_;
}
}
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec_ref(v___x_2608_);
lean_dec_ref(v_n_2605_);
lean_dec_ref(v_semiringInst_2603_);
lean_dec_ref(v_type_2601_);
v_a_2653_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2612_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2612_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
v_a_2661_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2598_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2598_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object* v_k_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec(v_k_2669_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object* v_a_2683_, lean_object* v_s_2684_){
_start:
{
lean_object* v_toRing_2685_; lean_object* v_invFn_x3f_2686_; lean_object* v_semiringId_x3f_2687_; lean_object* v_commSemiringInst_2688_; lean_object* v_commRingInst_2689_; lean_object* v_noZeroDivInst_x3f_2690_; lean_object* v_fieldInst_x3f_2691_; lean_object* v_powIdentityInst_x3f_2692_; lean_object* v_denoteEntries_2693_; lean_object* v_nextId_2694_; lean_object* v_steps_2695_; lean_object* v_queue_2696_; lean_object* v_basis_2697_; lean_object* v_diseqs_2698_; uint8_t v_recheck_2699_; lean_object* v_invSet_2700_; lean_object* v_powIdentityVarCount_2701_; lean_object* v_numEq0_x3f_2702_; uint8_t v_numEq0Updated_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2735_; 
v_toRing_2685_ = lean_ctor_get(v_s_2684_, 0);
v_invFn_x3f_2686_ = lean_ctor_get(v_s_2684_, 1);
v_semiringId_x3f_2687_ = lean_ctor_get(v_s_2684_, 2);
v_commSemiringInst_2688_ = lean_ctor_get(v_s_2684_, 3);
v_commRingInst_2689_ = lean_ctor_get(v_s_2684_, 4);
v_noZeroDivInst_x3f_2690_ = lean_ctor_get(v_s_2684_, 5);
v_fieldInst_x3f_2691_ = lean_ctor_get(v_s_2684_, 6);
v_powIdentityInst_x3f_2692_ = lean_ctor_get(v_s_2684_, 7);
v_denoteEntries_2693_ = lean_ctor_get(v_s_2684_, 8);
v_nextId_2694_ = lean_ctor_get(v_s_2684_, 9);
v_steps_2695_ = lean_ctor_get(v_s_2684_, 10);
v_queue_2696_ = lean_ctor_get(v_s_2684_, 11);
v_basis_2697_ = lean_ctor_get(v_s_2684_, 12);
v_diseqs_2698_ = lean_ctor_get(v_s_2684_, 13);
v_recheck_2699_ = lean_ctor_get_uint8(v_s_2684_, sizeof(void*)*17);
v_invSet_2700_ = lean_ctor_get(v_s_2684_, 14);
v_powIdentityVarCount_2701_ = lean_ctor_get(v_s_2684_, 15);
v_numEq0_x3f_2702_ = lean_ctor_get(v_s_2684_, 16);
v_numEq0Updated_2703_ = lean_ctor_get_uint8(v_s_2684_, sizeof(void*)*17 + 1);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_s_2684_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2705_ = v_s_2684_;
v_isShared_2706_ = v_isSharedCheck_2735_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_numEq0_x3f_2702_);
lean_inc(v_powIdentityVarCount_2701_);
lean_inc(v_invSet_2700_);
lean_inc(v_diseqs_2698_);
lean_inc(v_basis_2697_);
lean_inc(v_queue_2696_);
lean_inc(v_steps_2695_);
lean_inc(v_nextId_2694_);
lean_inc(v_denoteEntries_2693_);
lean_inc(v_powIdentityInst_x3f_2692_);
lean_inc(v_fieldInst_x3f_2691_);
lean_inc(v_noZeroDivInst_x3f_2690_);
lean_inc(v_commRingInst_2689_);
lean_inc(v_commSemiringInst_2688_);
lean_inc(v_semiringId_x3f_2687_);
lean_inc(v_invFn_x3f_2686_);
lean_inc(v_toRing_2685_);
lean_dec(v_s_2684_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2735_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v_id_2707_; lean_object* v_type_2708_; lean_object* v_u_2709_; lean_object* v_ringInst_2710_; lean_object* v_semiringInst_2711_; lean_object* v_charInst_x3f_2712_; lean_object* v_addFn_x3f_2713_; lean_object* v_mulFn_x3f_2714_; lean_object* v_subFn_x3f_2715_; lean_object* v_negFn_x3f_2716_; lean_object* v_intCastFn_x3f_2717_; lean_object* v_natCastFn_x3f_2718_; lean_object* v_one_x3f_2719_; lean_object* v_vars_2720_; lean_object* v_varMap_2721_; lean_object* v_denote_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2733_; 
v_id_2707_ = lean_ctor_get(v_toRing_2685_, 0);
v_type_2708_ = lean_ctor_get(v_toRing_2685_, 1);
v_u_2709_ = lean_ctor_get(v_toRing_2685_, 2);
v_ringInst_2710_ = lean_ctor_get(v_toRing_2685_, 3);
v_semiringInst_2711_ = lean_ctor_get(v_toRing_2685_, 4);
v_charInst_x3f_2712_ = lean_ctor_get(v_toRing_2685_, 5);
v_addFn_x3f_2713_ = lean_ctor_get(v_toRing_2685_, 6);
v_mulFn_x3f_2714_ = lean_ctor_get(v_toRing_2685_, 7);
v_subFn_x3f_2715_ = lean_ctor_get(v_toRing_2685_, 8);
v_negFn_x3f_2716_ = lean_ctor_get(v_toRing_2685_, 9);
v_intCastFn_x3f_2717_ = lean_ctor_get(v_toRing_2685_, 11);
v_natCastFn_x3f_2718_ = lean_ctor_get(v_toRing_2685_, 12);
v_one_x3f_2719_ = lean_ctor_get(v_toRing_2685_, 13);
v_vars_2720_ = lean_ctor_get(v_toRing_2685_, 14);
v_varMap_2721_ = lean_ctor_get(v_toRing_2685_, 15);
v_denote_2722_ = lean_ctor_get(v_toRing_2685_, 16);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_toRing_2685_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; 
v_unused_2734_ = lean_ctor_get(v_toRing_2685_, 10);
lean_dec(v_unused_2734_);
v___x_2724_ = v_toRing_2685_;
v_isShared_2725_ = v_isSharedCheck_2733_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_denote_2722_);
lean_inc(v_varMap_2721_);
lean_inc(v_vars_2720_);
lean_inc(v_one_x3f_2719_);
lean_inc(v_natCastFn_x3f_2718_);
lean_inc(v_intCastFn_x3f_2717_);
lean_inc(v_negFn_x3f_2716_);
lean_inc(v_subFn_x3f_2715_);
lean_inc(v_mulFn_x3f_2714_);
lean_inc(v_addFn_x3f_2713_);
lean_inc(v_charInst_x3f_2712_);
lean_inc(v_semiringInst_2711_);
lean_inc(v_ringInst_2710_);
lean_inc(v_u_2709_);
lean_inc(v_type_2708_);
lean_inc(v_id_2707_);
lean_dec(v_toRing_2685_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2733_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_a_2683_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 10, v___x_2726_);
v___x_2728_ = v___x_2724_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_id_2707_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_type_2708_);
lean_ctor_set(v_reuseFailAlloc_2732_, 2, v_u_2709_);
lean_ctor_set(v_reuseFailAlloc_2732_, 3, v_ringInst_2710_);
lean_ctor_set(v_reuseFailAlloc_2732_, 4, v_semiringInst_2711_);
lean_ctor_set(v_reuseFailAlloc_2732_, 5, v_charInst_x3f_2712_);
lean_ctor_set(v_reuseFailAlloc_2732_, 6, v_addFn_x3f_2713_);
lean_ctor_set(v_reuseFailAlloc_2732_, 7, v_mulFn_x3f_2714_);
lean_ctor_set(v_reuseFailAlloc_2732_, 8, v_subFn_x3f_2715_);
lean_ctor_set(v_reuseFailAlloc_2732_, 9, v_negFn_x3f_2716_);
lean_ctor_set(v_reuseFailAlloc_2732_, 10, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2732_, 11, v_intCastFn_x3f_2717_);
lean_ctor_set(v_reuseFailAlloc_2732_, 12, v_natCastFn_x3f_2718_);
lean_ctor_set(v_reuseFailAlloc_2732_, 13, v_one_x3f_2719_);
lean_ctor_set(v_reuseFailAlloc_2732_, 14, v_vars_2720_);
lean_ctor_set(v_reuseFailAlloc_2732_, 15, v_varMap_2721_);
lean_ctor_set(v_reuseFailAlloc_2732_, 16, v_denote_2722_);
v___x_2728_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2730_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2728_);
v___x_2730_ = v___x_2705_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_invFn_x3f_2686_);
lean_ctor_set(v_reuseFailAlloc_2731_, 2, v_semiringId_x3f_2687_);
lean_ctor_set(v_reuseFailAlloc_2731_, 3, v_commSemiringInst_2688_);
lean_ctor_set(v_reuseFailAlloc_2731_, 4, v_commRingInst_2689_);
lean_ctor_set(v_reuseFailAlloc_2731_, 5, v_noZeroDivInst_x3f_2690_);
lean_ctor_set(v_reuseFailAlloc_2731_, 6, v_fieldInst_x3f_2691_);
lean_ctor_set(v_reuseFailAlloc_2731_, 7, v_powIdentityInst_x3f_2692_);
lean_ctor_set(v_reuseFailAlloc_2731_, 8, v_denoteEntries_2693_);
lean_ctor_set(v_reuseFailAlloc_2731_, 9, v_nextId_2694_);
lean_ctor_set(v_reuseFailAlloc_2731_, 10, v_steps_2695_);
lean_ctor_set(v_reuseFailAlloc_2731_, 11, v_queue_2696_);
lean_ctor_set(v_reuseFailAlloc_2731_, 12, v_basis_2697_);
lean_ctor_set(v_reuseFailAlloc_2731_, 13, v_diseqs_2698_);
lean_ctor_set(v_reuseFailAlloc_2731_, 14, v_invSet_2700_);
lean_ctor_set(v_reuseFailAlloc_2731_, 15, v_powIdentityVarCount_2701_);
lean_ctor_set(v_reuseFailAlloc_2731_, 16, v_numEq0_x3f_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, sizeof(void*)*17, v_recheck_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2731_, sizeof(void*)*17 + 1, v_numEq0Updated_2703_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = lean_unsigned_to_nat(0u);
v___x_2740_ = l_Lean_Level_ofNat(v___x_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(lean_object* v_u_2751_, lean_object* v_type_2752_, lean_object* v_semiringInst_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2766_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1));
v___x_2767_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2);
v___x_2768_ = lean_box(0);
lean_inc(v_u_2751_);
v___x_2769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2769_, 0, v_u_2751_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
lean_inc_ref(v___x_2769_);
v___x_2770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2767_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
v___x_2771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2771_, 0, v_u_2751_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
lean_inc_ref(v___x_2771_);
v___x_2772_ = l_Lean_mkConst(v___x_2766_, v___x_2771_);
v___x_2773_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2752_, 2);
v___x_2774_ = l_Lean_mkApp3(v___x_2772_, v_type_2752_, v___x_2773_, v_type_2752_);
v___x_2775_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2774_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v_inst_x27_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc_n(v_a_2776_, 2);
lean_dec_ref(v___x_2775_);
v___x_2777_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4));
v___x_2778_ = l_Lean_mkConst(v___x_2777_, v___x_2769_);
lean_inc_ref(v_type_2752_);
v_inst_x27_2779_ = l_Lean_mkAppB(v___x_2778_, v_type_2752_, v_semiringInst_2753_);
v___x_2780_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6));
v___x_2781_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_2780_, v_a_2776_, v_inst_x27_2779_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_dec_ref(v___x_2781_);
v___x_2782_ = l_Lean_mkConst(v___x_2780_, v___x_2771_);
lean_inc_ref(v_type_2752_);
v___x_2783_ = l_Lean_mkApp4(v___x_2782_, v_type_2752_, v___x_2773_, v_type_2752_, v_a_2776_);
v___x_2784_ = l_Lean_Meta_Sym_canon(v___x_2783_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2786_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref(v___x_2784_);
v___x_2786_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2785_, v___y_2760_);
return v___x_2786_;
}
else
{
return v___x_2784_;
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec(v_a_2776_);
lean_dec_ref(v___x_2771_);
lean_dec_ref(v_type_2752_);
v_a_2787_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2781_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2781_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
else
{
lean_dec_ref(v___x_2771_);
lean_dec_ref(v___x_2769_);
lean_dec_ref(v_semiringInst_2753_);
lean_dec_ref(v_type_2752_);
return v___x_2775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___boxed(lean_object* v_u_2795_, lean_object* v_type_2796_, lean_object* v_semiringInst_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2795_, v_type_2796_, v_semiringInst_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2798_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2857_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_2857_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2857_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v_toRing_2828_; lean_object* v_powFn_x3f_2829_; 
v_toRing_2828_ = lean_ctor_get(v_a_2824_, 0);
lean_inc_ref(v_toRing_2828_);
lean_dec(v_a_2824_);
v_powFn_x3f_2829_ = lean_ctor_get(v_toRing_2828_, 10);
if (lean_obj_tag(v_powFn_x3f_2829_) == 1)
{
lean_object* v_val_2830_; lean_object* v___x_2832_; 
lean_inc_ref(v_powFn_x3f_2829_);
lean_dec_ref(v_toRing_2828_);
v_val_2830_ = lean_ctor_get(v_powFn_x3f_2829_, 0);
lean_inc(v_val_2830_);
lean_dec_ref(v_powFn_x3f_2829_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v_val_2830_);
v___x_2832_ = v___x_2826_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_val_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
else
{
lean_object* v_type_2834_; lean_object* v_u_2835_; lean_object* v_semiringInst_2836_; lean_object* v___x_2837_; 
lean_del_object(v___x_2826_);
v_type_2834_ = lean_ctor_get(v_toRing_2828_, 1);
lean_inc_ref(v_type_2834_);
v_u_2835_ = lean_ctor_get(v_toRing_2828_, 2);
lean_inc(v_u_2835_);
v_semiringInst_2836_ = lean_ctor_get(v_toRing_2828_, 4);
lean_inc_ref(v_semiringInst_2836_);
lean_dec_ref(v_toRing_2828_);
v___x_2837_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2835_, v_type_2834_, v_semiringInst_2836_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___f_2839_; lean_object* v___x_2840_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc_n(v_a_2838_, 2);
lean_dec_ref(v___x_2837_);
v___f_2839_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_2839_, 0, v_a_2838_);
v___x_2840_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2839_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v___x_2840_, 0);
lean_dec(v_unused_2848_);
v___x_2842_ = v___x_2840_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_dec(v___x_2840_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v_a_2838_);
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2838_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v_a_2838_);
v_a_2849_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2840_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2840_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
v_a_2858_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2823_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2823_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec(v___y_2866_);
return v_res_2878_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2));
v___x_2883_ = lean_unsigned_to_nat(39u);
v___x_2884_ = lean_unsigned_to_nat(159u);
v___x_2885_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1));
v___x_2886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0));
v___x_2887_ = l_mkPanicMessageWithDecl(v___x_2886_, v___x_2885_, v___x_2884_, v___x_2883_, v___x_2882_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
switch(lean_obj_tag(v_a_2888_))
{
case 0:
{
lean_object* v_k_2901_; lean_object* v___x_2902_; 
v_k_2901_ = lean_ctor_get(v_a_2888_, 0);
lean_inc(v_k_2901_);
lean_dec_ref(v_a_2888_);
v___x_2902_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2901_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec(v_k_2901_);
return v___x_2902_;
}
case 1:
{
lean_object* v_k_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v_k_2903_ = lean_ctor_get(v_a_2888_, 0);
lean_inc(v_k_2903_);
lean_dec_ref(v_a_2888_);
v___x_2904_ = lean_nat_to_int(v_k_2903_);
v___x_2905_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_2904_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec(v___x_2904_);
return v___x_2905_;
}
case 3:
{
lean_object* v_i_2906_; lean_object* v___x_2907_; 
v_i_2906_ = lean_ctor_get(v_a_2888_, 0);
lean_inc(v_i_2906_);
lean_dec_ref(v_a_2888_);
v___x_2907_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2909_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref(v___x_2907_);
v___x_2909_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2927_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2927_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2927_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___y_2915_; lean_object* v_toSemiring_2920_; lean_object* v_vars_2921_; lean_object* v_size_2922_; lean_object* v___x_2923_; uint8_t v___x_2924_; 
v_toSemiring_2920_ = lean_ctor_get(v_a_2910_, 0);
lean_inc_ref(v_toSemiring_2920_);
lean_dec(v_a_2910_);
v_vars_2921_ = lean_ctor_get(v_toSemiring_2920_, 9);
lean_inc_ref(v_vars_2921_);
lean_dec_ref(v_toSemiring_2920_);
v_size_2922_ = lean_ctor_get(v_vars_2921_, 2);
v___x_2923_ = l_Lean_instInhabitedExpr;
v___x_2924_ = lean_nat_dec_lt(v_i_2906_, v_size_2922_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; 
lean_dec_ref(v_vars_2921_);
lean_dec(v_i_2906_);
v___x_2925_ = l_outOfBounds___redArg(v___x_2923_);
v___y_2915_ = v___x_2925_;
goto v___jp_2914_;
}
else
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2923_, v_vars_2921_, v_i_2906_);
lean_dec(v_i_2906_);
lean_dec_ref(v_vars_2921_);
v___y_2915_ = v___x_2926_;
goto v___jp_2914_;
}
v___jp_2914_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = l_Lean_Expr_app___override(v_a_2908_, v___y_2915_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2916_);
v___x_2918_ = v___x_2912_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_a_2908_);
lean_dec(v_i_2906_);
v_a_2928_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2909_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2909_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
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
lean_dec(v_i_2906_);
return v___x_2907_;
}
}
case 5:
{
lean_object* v_a_2936_; lean_object* v_b_2937_; lean_object* v___x_2938_; 
v_a_2936_ = lean_ctor_get(v_a_2888_, 0);
lean_inc_ref(v_a_2936_);
v_b_2937_ = lean_ctor_get(v_a_2888_, 1);
lean_inc_ref(v_b_2937_);
lean_dec_ref(v_a_2888_);
v___x_2938_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref(v___x_2938_);
v___x_2940_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2936_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref(v___x_2940_);
v___x_2942_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2937_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2951_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_2951_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2951_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2947_ = l_Lean_mkAppB(v_a_2939_, v_a_2941_, v_a_2943_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2947_);
v___x_2949_ = v___x_2945_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
else
{
lean_dec(v_a_2941_);
lean_dec(v_a_2939_);
return v___x_2942_;
}
}
else
{
lean_dec(v_a_2939_);
lean_dec_ref(v_b_2937_);
return v___x_2940_;
}
}
else
{
lean_dec_ref(v_b_2937_);
lean_dec_ref(v_a_2936_);
return v___x_2938_;
}
}
case 7:
{
lean_object* v_a_2952_; lean_object* v_b_2953_; lean_object* v___x_2954_; 
v_a_2952_ = lean_ctor_get(v_a_2888_, 0);
lean_inc_ref(v_a_2952_);
v_b_2953_ = lean_ctor_get(v_a_2888_, 1);
lean_inc_ref(v_b_2953_);
lean_dec_ref(v_a_2888_);
v___x_2954_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2956_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref(v___x_2954_);
v___x_2956_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2952_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2958_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref(v___x_2956_);
v___x_2958_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2953_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2967_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2967_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2967_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2963_ = l_Lean_mkAppB(v_a_2955_, v_a_2957_, v_a_2959_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2963_);
v___x_2965_ = v___x_2961_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
else
{
lean_dec(v_a_2957_);
lean_dec(v_a_2955_);
return v___x_2958_;
}
}
else
{
lean_dec(v_a_2955_);
lean_dec_ref(v_b_2953_);
return v___x_2956_;
}
}
else
{
lean_dec_ref(v_b_2953_);
lean_dec_ref(v_a_2952_);
return v___x_2954_;
}
}
case 8:
{
lean_object* v_a_2968_; lean_object* v_k_2969_; lean_object* v___x_2970_; 
v_a_2968_ = lean_ctor_get(v_a_2888_, 0);
lean_inc_ref(v_a_2968_);
v_k_2969_ = lean_ctor_get(v_a_2888_, 1);
lean_inc(v_k_2969_);
lean_dec_ref(v_a_2888_);
v___x_2970_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___x_2972_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref(v___x_2970_);
v___x_2972_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2968_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2982_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_2982_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2982_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2977_ = l_Lean_mkNatLit(v_k_2969_);
v___x_2978_ = l_Lean_mkAppB(v_a_2971_, v_a_2973_, v___x_2977_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_2978_);
v___x_2980_ = v___x_2975_;
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
lean_dec(v_a_2971_);
lean_dec(v_k_2969_);
return v___x_2972_;
}
}
else
{
lean_dec(v_k_2969_);
lean_dec_ref(v_a_2968_);
return v___x_2970_;
}
}
default: 
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
lean_dec_ref(v_a_2888_);
v___x_2983_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
v___x_2984_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___x_2983_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
return v___x_2984_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec(v_a_2987_);
lean_dec(v_a_2986_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(lean_object* v_type_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_2999_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(lean_object* v_type_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(v_type_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec(v___y_3014_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object* v_e_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_e_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3042_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref(v___x_3040_);
v___x_3042_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3041_, v_a_3034_);
return v___x_3042_;
}
else
{
return v___x_3040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object* v_e_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(v_e_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec(v_a_3044_);
return v_res_3056_;
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
