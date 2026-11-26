// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Init.Data.Int.OfNat import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.NatInstTesters
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntDiv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntMod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntPowNat(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_mkIntNatCast(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natImage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natImage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "natCast_ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(238, 161, 137, 195, 161, 239, 200, 79)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 126, 174, 185, 27, 56, 123, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__7(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mod_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 250, 102, 19, 8, 50, 252, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "div_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 168, 146, 132, 240, 126, 147, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "pow_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 58, 93, 228, 192, 253, 115, 4)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mul_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 119, 195, 92, 68, 86, 209, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__6_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__7_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__9_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__12_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__13_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__15_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__16_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(165, 91, 87, 132, 175, 103, 206, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "isLt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(222, 150, 50, 101, 25, 222, 136, 68)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1_spec__2(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToIntExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToIntExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 96, .m_capacity = 96, .m_length = 95, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat.0.Lean.Meta.Grind.Arith.Cutsat.mkNonnegThm\?.go"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Nonneg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1_value),LEAN_SCALAR_PTR_LITERAL(221, 113, 7, 185, 57, 18, 171, 207)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__8_value),LEAN_SCALAR_PTR_LITERAL(18, 216, 199, 74, 39, 140, 254, 20)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(188, 150, 118, 217, 197, 2, 106, 60)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "div"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(3, 105, 42, 253, 30, 168, 164, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__17_value),LEAN_SCALAR_PTR_LITERAL(52, 118, 58, 105, 21, 29, 158, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__20_value),LEAN_SCALAR_PTR_LITERAL(91, 38, 36, 71, 236, 90, 216, 150)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__23_value),LEAN_SCALAR_PTR_LITERAL(195, 74, 119, 167, 0, 49, 135, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toPoly"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 134, 248, 74, 100, 20, 67, 14)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = l_Lean_Level_ofNat(v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__4(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_box(0);
v___x_9_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__3);
v___x_10_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__5(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__4);
v___x_12_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__2));
v___x_13_ = l_Lean_mkConst(v___x_12_, v___x_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl(lean_object* v_e_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_15_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__5);
v___x_16_ = l_Lean_Int_mkType;
lean_inc_ref(v_e_14_);
v___x_17_ = l_Lean_mkAppB(v___x_15_, v___x_16_, v_e_14_);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v_e_14_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_19_, lean_object* v_x_20_, lean_object* v_x_21_, lean_object* v_x_22_){
_start:
{
lean_object* v_ks_23_; lean_object* v_vs_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_50_; 
v_ks_23_ = lean_ctor_get(v_x_19_, 0);
v_vs_24_ = lean_ctor_get(v_x_19_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v_x_19_);
if (v_isSharedCheck_50_ == 0)
{
v___x_26_ = v_x_19_;
v_isShared_27_ = v_isSharedCheck_50_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_vs_24_);
lean_inc(v_ks_23_);
lean_dec(v_x_19_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_50_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_28_ = lean_array_get_size(v_ks_23_);
v___x_29_ = lean_nat_dec_lt(v_x_20_, v___x_28_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
lean_dec(v_x_20_);
v___x_30_ = lean_array_push(v_ks_23_, v_x_21_);
v___x_31_ = lean_array_push(v_vs_24_, v_x_22_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 1, v___x_31_);
lean_ctor_set(v___x_26_, 0, v___x_30_);
v___x_33_ = v___x_26_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
else
{
lean_object* v_k_x27_35_; size_t v___x_36_; size_t v___x_37_; uint8_t v___x_38_; 
v_k_x27_35_ = lean_array_fget_borrowed(v_ks_23_, v_x_20_);
v___x_36_ = lean_ptr_addr(v_x_21_);
v___x_37_ = lean_ptr_addr(v_k_x27_35_);
v___x_38_ = lean_usize_dec_eq(v___x_36_, v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_40_; 
if (v_isShared_27_ == 0)
{
v___x_40_ = v___x_26_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_ks_23_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_vs_24_);
v___x_40_ = v_reuseFailAlloc_44_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_add(v_x_20_, v___x_41_);
lean_dec(v_x_20_);
v_x_19_ = v___x_40_;
v_x_20_ = v___x_42_;
goto _start;
}
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_45_ = lean_array_fset(v_ks_23_, v_x_20_, v_x_21_);
v___x_46_ = lean_array_fset(v_vs_24_, v_x_20_, v_x_22_);
lean_dec(v_x_20_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 1, v___x_46_);
lean_ctor_set(v___x_26_, 0, v___x_45_);
v___x_48_ = v___x_26_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(lean_object* v_n_51_, lean_object* v_k_52_, lean_object* v_v_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(v_n_51_, v___x_54_, v_k_52_, v_v_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(lean_object* v_x_57_, size_t v_x_58_, size_t v_x_59_, lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
if (lean_obj_tag(v_x_57_) == 0)
{
lean_object* v_es_62_; size_t v___x_63_; size_t v___x_64_; lean_object* v_j_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v_es_62_ = lean_ctor_get(v_x_57_, 0);
v___x_63_ = ((size_t)31ULL);
v___x_64_ = lean_usize_land(v_x_58_, v___x_63_);
v_j_65_ = lean_usize_to_nat(v___x_64_);
v___x_66_ = lean_array_get_size(v_es_62_);
v___x_67_ = lean_nat_dec_lt(v_j_65_, v___x_66_);
if (v___x_67_ == 0)
{
lean_dec(v_j_65_);
lean_dec(v_x_61_);
lean_dec_ref(v_x_60_);
return v_x_57_;
}
else
{
lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_108_; 
lean_inc_ref(v_es_62_);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v_x_57_, 0);
lean_dec(v_unused_109_);
v___x_69_ = v_x_57_;
v_isShared_70_ = v_isSharedCheck_108_;
goto v_resetjp_68_;
}
else
{
lean_dec(v_x_57_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_108_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v_v_71_; lean_object* v___x_72_; lean_object* v_xs_x27_73_; lean_object* v___y_75_; 
v_v_71_ = lean_array_fget(v_es_62_, v_j_65_);
v___x_72_ = lean_box(0);
v_xs_x27_73_ = lean_array_fset(v_es_62_, v_j_65_, v___x_72_);
switch(lean_obj_tag(v_v_71_))
{
case 0:
{
lean_object* v_key_80_; lean_object* v_val_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_93_; 
v_key_80_ = lean_ctor_get(v_v_71_, 0);
v_val_81_ = lean_ctor_get(v_v_71_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v_v_71_);
if (v_isSharedCheck_93_ == 0)
{
v___x_83_ = v_v_71_;
v_isShared_84_ = v_isSharedCheck_93_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_val_81_);
lean_inc(v_key_80_);
lean_dec(v_v_71_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_93_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
size_t v___x_85_; size_t v___x_86_; uint8_t v___x_87_; 
v___x_85_ = lean_ptr_addr(v_x_60_);
v___x_86_ = lean_ptr_addr(v_key_80_);
v___x_87_ = lean_usize_dec_eq(v___x_85_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_del_object(v___x_83_);
v___x_88_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_80_, v_val_81_, v_x_60_, v_x_61_);
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
v___y_75_ = v___x_89_;
goto v___jp_74_;
}
else
{
lean_object* v___x_91_; 
lean_dec(v_val_81_);
lean_dec(v_key_80_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_x_61_);
lean_ctor_set(v___x_83_, 0, v_x_60_);
v___x_91_ = v___x_83_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_x_60_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_x_61_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
v___y_75_ = v___x_91_;
goto v___jp_74_;
}
}
}
}
case 1:
{
lean_object* v_node_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_106_; 
v_node_94_ = lean_ctor_get(v_v_71_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v_v_71_);
if (v_isSharedCheck_106_ == 0)
{
v___x_96_ = v_v_71_;
v_isShared_97_ = v_isSharedCheck_106_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_node_94_);
lean_dec(v_v_71_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_106_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_98_ = ((size_t)5ULL);
v___x_99_ = lean_usize_shift_right(v_x_58_, v___x_98_);
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_add(v_x_59_, v___x_100_);
v___x_102_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_node_94_, v___x_99_, v___x_101_, v_x_60_, v_x_61_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_102_);
v___x_104_ = v___x_96_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
v___y_75_ = v___x_104_;
goto v___jp_74_;
}
}
}
default: 
{
lean_object* v___x_107_; 
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v_x_60_);
lean_ctor_set(v___x_107_, 1, v_x_61_);
v___y_75_ = v___x_107_;
goto v___jp_74_;
}
}
v___jp_74_:
{
lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_76_ = lean_array_fset(v_xs_x27_73_, v_j_65_, v___y_75_);
lean_dec(v_j_65_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_76_);
v___x_78_ = v___x_69_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
else
{
lean_object* v_ks_110_; lean_object* v_vs_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_129_; 
v_ks_110_ = lean_ctor_get(v_x_57_, 0);
v_vs_111_ = lean_ctor_get(v_x_57_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_129_ == 0)
{
v___x_113_ = v_x_57_;
v_isShared_114_ = v_isSharedCheck_129_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_vs_111_);
lean_inc(v_ks_110_);
lean_dec(v_x_57_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_129_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_ks_110_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_vs_111_);
v___x_116_ = v_reuseFailAlloc_128_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v_newNode_117_; size_t v___x_118_; uint8_t v___x_119_; 
v_newNode_117_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(v___x_116_, v_x_60_, v_x_61_);
v___x_118_ = ((size_t)7ULL);
v___x_119_ = lean_usize_dec_le(v___x_118_, v_x_59_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_117_);
v___x_121_ = lean_unsigned_to_nat(4u);
v___x_122_ = lean_nat_dec_lt(v___x_120_, v___x_121_);
lean_dec(v___x_120_);
if (v___x_122_ == 0)
{
lean_object* v_ks_123_; lean_object* v_vs_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_ks_123_ = lean_ctor_get(v_newNode_117_, 0);
lean_inc_ref(v_ks_123_);
v_vs_124_ = lean_ctor_get(v_newNode_117_, 1);
lean_inc_ref(v_vs_124_);
lean_dec_ref(v_newNode_117_);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0);
v___x_127_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_x_59_, v_ks_123_, v_vs_124_, v___x_125_, v___x_126_);
lean_dec_ref(v_vs_124_);
lean_dec_ref(v_ks_123_);
return v___x_127_;
}
else
{
return v_newNode_117_;
}
}
else
{
return v_newNode_117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(size_t v_depth_130_, lean_object* v_keys_131_, lean_object* v_vals_132_, lean_object* v_i_133_, lean_object* v_entries_134_){
_start:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_array_get_size(v_keys_131_);
v___x_136_ = lean_nat_dec_lt(v_i_133_, v___x_135_);
if (v___x_136_ == 0)
{
lean_dec(v_i_133_);
return v_entries_134_;
}
else
{
lean_object* v_k_137_; lean_object* v_v_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; uint64_t v___x_142_; size_t v_h_143_; size_t v___x_144_; lean_object* v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v_h_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_k_137_ = lean_array_fget_borrowed(v_keys_131_, v_i_133_);
v_v_138_ = lean_array_fget_borrowed(v_vals_132_, v_i_133_);
v___x_139_ = lean_ptr_addr(v_k_137_);
v___x_140_ = ((size_t)3ULL);
v___x_141_ = lean_usize_shift_right(v___x_139_, v___x_140_);
v___x_142_ = lean_usize_to_uint64(v___x_141_);
v_h_143_ = lean_uint64_to_usize(v___x_142_);
v___x_144_ = ((size_t)5ULL);
v___x_145_ = lean_unsigned_to_nat(1u);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_sub(v_depth_130_, v___x_146_);
v___x_148_ = lean_usize_mul(v___x_144_, v___x_147_);
v_h_149_ = lean_usize_shift_right(v_h_143_, v___x_148_);
v___x_150_ = lean_nat_add(v_i_133_, v___x_145_);
lean_dec(v_i_133_);
lean_inc(v_v_138_);
lean_inc(v_k_137_);
v___x_151_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_entries_134_, v_h_149_, v_depth_130_, v_k_137_, v_v_138_);
v_i_133_ = v___x_150_;
v_entries_134_ = v___x_151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_153_, lean_object* v_keys_154_, lean_object* v_vals_155_, lean_object* v_i_156_, lean_object* v_entries_157_){
_start:
{
size_t v_depth_boxed_158_; lean_object* v_res_159_; 
v_depth_boxed_158_ = lean_unbox_usize(v_depth_153_);
lean_dec(v_depth_153_);
v_res_159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_depth_boxed_158_, v_keys_154_, v_vals_155_, v_i_156_, v_entries_157_);
lean_dec_ref(v_vals_155_);
lean_dec_ref(v_keys_154_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___boxed(lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
size_t v_x_8129__boxed_165_; size_t v_x_8130__boxed_166_; lean_object* v_res_167_; 
v_x_8129__boxed_165_ = lean_unbox_usize(v_x_161_);
lean_dec(v_x_161_);
v_x_8130__boxed_166_ = lean_unbox_usize(v_x_162_);
lean_dec(v_x_162_);
v_res_167_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_160_, v_x_8129__boxed_165_, v_x_8130__boxed_166_, v_x_163_, v_x_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(lean_object* v_x_168_, lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; uint64_t v___x_174_; size_t v___x_175_; size_t v___x_176_; lean_object* v___x_177_; 
v___x_171_ = lean_ptr_addr(v_x_169_);
v___x_172_ = ((size_t)3ULL);
v___x_173_ = lean_usize_shift_right(v___x_171_, v___x_172_);
v___x_174_ = lean_usize_to_uint64(v___x_173_);
v___x_175_ = lean_uint64_to_usize(v___x_174_);
v___x_176_ = ((size_t)1ULL);
v___x_177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_168_, v___x_175_, v___x_176_, v_x_169_, v_x_170_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___lam__0(lean_object* v_e_178_, lean_object* v___x_179_, lean_object* v_s_180_){
_start:
{
lean_object* v_vars_181_; lean_object* v_varMap_182_; lean_object* v_varsHistory_183_; lean_object* v_natToIntMap_184_; lean_object* v_natDef_185_; lean_object* v_dvds_186_; lean_object* v_lowers_187_; lean_object* v_uppers_188_; lean_object* v_diseqs_189_; lean_object* v_elimEqs_190_; lean_object* v_active_191_; lean_object* v_elimStack_192_; lean_object* v_occurs_193_; lean_object* v_assignment_194_; lean_object* v_nextCnstrId_195_; uint8_t v_caseSplits_196_; lean_object* v_steps_197_; lean_object* v_penalties_198_; lean_object* v_numReorderRequests_199_; lean_object* v_conflict_x3f_200_; lean_object* v_diseqSplits_201_; lean_object* v_divMod_202_; uint8_t v_usedCommRing_203_; lean_object* v_nonlinearOccs_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_212_; 
v_vars_181_ = lean_ctor_get(v_s_180_, 0);
v_varMap_182_ = lean_ctor_get(v_s_180_, 1);
v_varsHistory_183_ = lean_ctor_get(v_s_180_, 2);
v_natToIntMap_184_ = lean_ctor_get(v_s_180_, 3);
v_natDef_185_ = lean_ctor_get(v_s_180_, 4);
v_dvds_186_ = lean_ctor_get(v_s_180_, 5);
v_lowers_187_ = lean_ctor_get(v_s_180_, 6);
v_uppers_188_ = lean_ctor_get(v_s_180_, 7);
v_diseqs_189_ = lean_ctor_get(v_s_180_, 8);
v_elimEqs_190_ = lean_ctor_get(v_s_180_, 9);
v_active_191_ = lean_ctor_get(v_s_180_, 10);
v_elimStack_192_ = lean_ctor_get(v_s_180_, 11);
v_occurs_193_ = lean_ctor_get(v_s_180_, 12);
v_assignment_194_ = lean_ctor_get(v_s_180_, 13);
v_nextCnstrId_195_ = lean_ctor_get(v_s_180_, 14);
v_caseSplits_196_ = lean_ctor_get_uint8(v_s_180_, sizeof(void*)*22);
v_steps_197_ = lean_ctor_get(v_s_180_, 15);
v_penalties_198_ = lean_ctor_get(v_s_180_, 16);
v_numReorderRequests_199_ = lean_ctor_get(v_s_180_, 17);
v_conflict_x3f_200_ = lean_ctor_get(v_s_180_, 18);
v_diseqSplits_201_ = lean_ctor_get(v_s_180_, 19);
v_divMod_202_ = lean_ctor_get(v_s_180_, 20);
v_usedCommRing_203_ = lean_ctor_get_uint8(v_s_180_, sizeof(void*)*22 + 1);
v_nonlinearOccs_204_ = lean_ctor_get(v_s_180_, 21);
v_isSharedCheck_212_ = !lean_is_exclusive(v_s_180_);
if (v_isSharedCheck_212_ == 0)
{
v___x_206_ = v_s_180_;
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_nonlinearOccs_204_);
lean_inc(v_divMod_202_);
lean_inc(v_diseqSplits_201_);
lean_inc(v_conflict_x3f_200_);
lean_inc(v_numReorderRequests_199_);
lean_inc(v_penalties_198_);
lean_inc(v_steps_197_);
lean_inc(v_nextCnstrId_195_);
lean_inc(v_assignment_194_);
lean_inc(v_occurs_193_);
lean_inc(v_elimStack_192_);
lean_inc(v_active_191_);
lean_inc(v_elimEqs_190_);
lean_inc(v_diseqs_189_);
lean_inc(v_uppers_188_);
lean_inc(v_lowers_187_);
lean_inc(v_dvds_186_);
lean_inc(v_natDef_185_);
lean_inc(v_natToIntMap_184_);
lean_inc(v_varsHistory_183_);
lean_inc(v_varMap_182_);
lean_inc(v_vars_181_);
lean_dec(v_s_180_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(v_natToIntMap_184_, v_e_178_, v___x_179_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 3, v___x_208_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_vars_181_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_varMap_182_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_varsHistory_183_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_211_, 4, v_natDef_185_);
lean_ctor_set(v_reuseFailAlloc_211_, 5, v_dvds_186_);
lean_ctor_set(v_reuseFailAlloc_211_, 6, v_lowers_187_);
lean_ctor_set(v_reuseFailAlloc_211_, 7, v_uppers_188_);
lean_ctor_set(v_reuseFailAlloc_211_, 8, v_diseqs_189_);
lean_ctor_set(v_reuseFailAlloc_211_, 9, v_elimEqs_190_);
lean_ctor_set(v_reuseFailAlloc_211_, 10, v_active_191_);
lean_ctor_set(v_reuseFailAlloc_211_, 11, v_elimStack_192_);
lean_ctor_set(v_reuseFailAlloc_211_, 12, v_occurs_193_);
lean_ctor_set(v_reuseFailAlloc_211_, 13, v_assignment_194_);
lean_ctor_set(v_reuseFailAlloc_211_, 14, v_nextCnstrId_195_);
lean_ctor_set(v_reuseFailAlloc_211_, 15, v_steps_197_);
lean_ctor_set(v_reuseFailAlloc_211_, 16, v_penalties_198_);
lean_ctor_set(v_reuseFailAlloc_211_, 17, v_numReorderRequests_199_);
lean_ctor_set(v_reuseFailAlloc_211_, 18, v_conflict_x3f_200_);
lean_ctor_set(v_reuseFailAlloc_211_, 19, v_diseqSplits_201_);
lean_ctor_set(v_reuseFailAlloc_211_, 20, v_divMod_202_);
lean_ctor_set(v_reuseFailAlloc_211_, 21, v_nonlinearOccs_204_);
lean_ctor_set_uint8(v_reuseFailAlloc_211_, sizeof(void*)*22, v_caseSplits_196_);
lean_ctor_set_uint8(v_reuseFailAlloc_211_, sizeof(void*)*22 + 1, v_usedCommRing_203_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_213_, lean_object* v_vals_214_, lean_object* v_i_215_, lean_object* v_k_216_){
_start:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_array_get_size(v_keys_213_);
v___x_218_ = lean_nat_dec_lt(v_i_215_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
lean_dec(v_i_215_);
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
lean_object* v_k_x27_220_; size_t v___x_221_; size_t v___x_222_; uint8_t v___x_223_; 
v_k_x27_220_ = lean_array_fget_borrowed(v_keys_213_, v_i_215_);
v___x_221_ = lean_ptr_addr(v_k_216_);
v___x_222_ = lean_ptr_addr(v_k_x27_220_);
v___x_223_ = lean_usize_dec_eq(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_add(v_i_215_, v___x_224_);
lean_dec(v_i_215_);
v_i_215_ = v___x_225_;
goto _start;
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_array_fget_borrowed(v_vals_214_, v_i_215_);
lean_dec(v_i_215_);
lean_inc(v___x_227_);
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_229_, lean_object* v_vals_230_, lean_object* v_i_231_, lean_object* v_k_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_keys_229_, v_vals_230_, v_i_231_, v_k_232_);
lean_dec_ref(v_k_232_);
lean_dec_ref(v_vals_230_);
lean_dec_ref(v_keys_229_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(lean_object* v_x_234_, size_t v_x_235_, lean_object* v_x_236_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
lean_object* v_es_237_; lean_object* v___x_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v_j_241_; lean_object* v___x_242_; 
v_es_237_ = lean_ctor_get(v_x_234_, 0);
v___x_238_ = lean_box(2);
v___x_239_ = ((size_t)31ULL);
v___x_240_ = lean_usize_land(v_x_235_, v___x_239_);
v_j_241_ = lean_usize_to_nat(v___x_240_);
v___x_242_ = lean_array_get_borrowed(v___x_238_, v_es_237_, v_j_241_);
lean_dec(v_j_241_);
switch(lean_obj_tag(v___x_242_))
{
case 0:
{
lean_object* v_key_243_; lean_object* v_val_244_; size_t v___x_245_; size_t v___x_246_; uint8_t v___x_247_; 
v_key_243_ = lean_ctor_get(v___x_242_, 0);
v_val_244_ = lean_ctor_get(v___x_242_, 1);
v___x_245_ = lean_ptr_addr(v_x_236_);
v___x_246_ = lean_ptr_addr(v_key_243_);
v___x_247_ = lean_usize_dec_eq(v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
v___x_248_ = lean_box(0);
return v___x_248_;
}
else
{
lean_object* v___x_249_; 
lean_inc(v_val_244_);
v___x_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_249_, 0, v_val_244_);
return v___x_249_;
}
}
case 1:
{
lean_object* v_node_250_; size_t v___x_251_; size_t v___x_252_; 
v_node_250_ = lean_ctor_get(v___x_242_, 0);
v___x_251_ = ((size_t)5ULL);
v___x_252_ = lean_usize_shift_right(v_x_235_, v___x_251_);
v_x_234_ = v_node_250_;
v_x_235_ = v___x_252_;
goto _start;
}
default: 
{
lean_object* v___x_254_; 
v___x_254_ = lean_box(0);
return v___x_254_;
}
}
}
else
{
lean_object* v_ks_255_; lean_object* v_vs_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_ks_255_ = lean_ctor_get(v_x_234_, 0);
v_vs_256_ = lean_ctor_get(v_x_234_, 1);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_ks_255_, v_vs_256_, v___x_257_, v_x_236_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
size_t v_x_8348__boxed_262_; lean_object* v_res_263_; 
v_x_8348__boxed_262_ = lean_unbox_usize(v_x_260_);
lean_dec(v_x_260_);
v_res_263_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_259_, v_x_8348__boxed_262_, v_x_261_);
lean_dec_ref(v_x_261_);
lean_dec_ref(v_x_259_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
size_t v___x_266_; size_t v___x_267_; size_t v___x_268_; uint64_t v___x_269_; size_t v___x_270_; lean_object* v___x_271_; 
v___x_266_ = lean_ptr_addr(v_x_265_);
v___x_267_ = ((size_t)3ULL);
v___x_268_ = lean_usize_shift_right(v___x_266_, v___x_267_);
v___x_269_ = lean_usize_to_uint64(v___x_268_);
v___x_270_ = lean_uint64_to_usize(v___x_269_);
v___x_271_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_264_, v___x_270_, v_x_265_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg___boxed(lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_x_272_, v_x_273_);
lean_dec_ref(v_x_273_);
lean_dec_ref(v_x_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(lean_object* v_e_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_276_, v_a_284_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_358_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_358_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_358_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_358_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_natToIntMap_292_; lean_object* v___x_293_; 
v_natToIntMap_292_ = lean_ctor_get(v_a_288_, 3);
lean_inc_ref(v_natToIntMap_292_);
lean_dec(v_a_288_);
v___x_293_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_natToIntMap_292_, v_e_275_);
lean_dec_ref(v_natToIntMap_292_);
if (lean_obj_tag(v___x_293_) == 1)
{
lean_object* v_val_294_; lean_object* v___x_296_; 
lean_dec_ref(v_e_275_);
v_val_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_val_294_);
lean_dec_ref_known(v___x_293_, 1);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_val_294_);
v___x_296_ = v___x_290_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_val_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v___x_293_);
lean_del_object(v___x_290_);
lean_inc_ref(v_e_275_);
v___x_298_ = l_Lean_mkIntNatCast(v_e_275_);
v___x_299_ = l_Lean_Meta_Sym_shareCommon(v___x_298_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_301_; lean_object* v___f_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc_n(v_a_300_, 2);
lean_dec_ref_known(v___x_299_, 1);
v___x_301_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl(v_a_300_);
lean_inc_ref(v___x_301_);
lean_inc_ref(v_e_275_);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___lam__0), 3, 2);
lean_closure_set(v___f_302_, 0, v_e_275_);
lean_closure_set(v___f_302_, 1, v___x_301_);
v___x_303_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_304_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_303_, v___f_302_, v_a_276_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v___x_305_; 
lean_dec_ref_known(v___x_304_, 1);
v___x_305_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_275_, v_a_276_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v___x_305_, 1);
v___x_307_ = lean_box(0);
lean_inc(v_a_285_);
lean_inc_ref(v_a_284_);
lean_inc(v_a_283_);
lean_inc_ref(v_a_282_);
lean_inc(v_a_281_);
lean_inc_ref(v_a_280_);
lean_inc(v_a_279_);
lean_inc_ref(v_a_278_);
lean_inc(v_a_277_);
lean_inc(v_a_276_);
v___x_308_ = lean_grind_internalize(v_a_300_, v_a_306_, v___x_307_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_309_; 
lean_dec_ref_known(v___x_308_, 1);
v___x_309_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_303_, v_e_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; 
v_unused_317_ = lean_ctor_get(v___x_309_, 0);
lean_dec(v_unused_317_);
v___x_311_ = v___x_309_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_dec(v___x_309_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_301_);
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_301_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref(v___x_301_);
v_a_318_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_309_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_309_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref(v___x_301_);
lean_dec_ref(v_e_275_);
v_a_326_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_308_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_308_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec_ref(v___x_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_e_275_);
v_a_334_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_305_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_305_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec_ref(v___x_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_e_275_);
v_a_342_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_304_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_304_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref(v_e_275_);
v_a_350_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_299_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_299_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v_e_275_);
v_a_359_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_287_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_287_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___boxed(lean_object* v_e_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec(v_a_368_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0(lean_object* v_00_u03b2_380_, lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_x_381_, v_x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___boxed(lean_object* v_00_u03b2_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0(v_00_u03b2_384_, v_x_385_, v_x_386_);
lean_dec_ref(v_x_386_);
lean_dec_ref(v_x_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1(lean_object* v_00_u03b2_388_, lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(v_x_389_, v_x_390_, v_x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0(lean_object* v_00_u03b2_393_, lean_object* v_x_394_, size_t v_x_395_, lean_object* v_x_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_394_, v_x_395_, v_x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_398_, lean_object* v_x_399_, lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
size_t v_x_8597__boxed_402_; lean_object* v_res_403_; 
v_x_8597__boxed_402_ = lean_unbox_usize(v_x_400_);
lean_dec(v_x_400_);
v_res_403_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0(v_00_u03b2_398_, v_x_399_, v_x_8597__boxed_402_, v_x_401_);
lean_dec_ref(v_x_401_);
lean_dec_ref(v_x_399_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2(lean_object* v_00_u03b2_404_, lean_object* v_x_405_, size_t v_x_406_, size_t v_x_407_, lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_405_, v_x_406_, v_x_407_, v_x_408_, v_x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_411_, lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
size_t v_x_8608__boxed_417_; size_t v_x_8609__boxed_418_; lean_object* v_res_419_; 
v_x_8608__boxed_417_ = lean_unbox_usize(v_x_413_);
lean_dec(v_x_413_);
v_x_8609__boxed_418_ = lean_unbox_usize(v_x_414_);
lean_dec(v_x_414_);
v_res_419_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2(v_00_u03b2_411_, v_x_412_, v_x_8608__boxed_417_, v_x_8609__boxed_418_, v_x_415_, v_x_416_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_420_, lean_object* v_keys_421_, lean_object* v_vals_422_, lean_object* v_heq_423_, lean_object* v_i_424_, lean_object* v_k_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_keys_421_, v_vals_422_, v_i_424_, v_k_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_427_, lean_object* v_keys_428_, lean_object* v_vals_429_, lean_object* v_heq_430_, lean_object* v_i_431_, lean_object* v_k_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1(v_00_u03b2_427_, v_keys_428_, v_vals_429_, v_heq_430_, v_i_431_, v_k_432_);
lean_dec_ref(v_k_432_);
lean_dec_ref(v_vals_429_);
lean_dec_ref(v_keys_428_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_434_, lean_object* v_n_435_, lean_object* v_k_436_, lean_object* v_v_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(v_n_435_, v_k_436_, v_v_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_439_, size_t v_depth_440_, lean_object* v_keys_441_, lean_object* v_vals_442_, lean_object* v_heq_443_, lean_object* v_i_444_, lean_object* v_entries_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_depth_440_, v_keys_441_, v_vals_442_, v_i_444_, v_entries_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_447_, lean_object* v_depth_448_, lean_object* v_keys_449_, lean_object* v_vals_450_, lean_object* v_heq_451_, lean_object* v_i_452_, lean_object* v_entries_453_){
_start:
{
size_t v_depth_boxed_454_; lean_object* v_res_455_; 
v_depth_boxed_454_ = lean_unbox_usize(v_depth_448_);
lean_dec(v_depth_448_);
v_res_455_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5(v_00_u03b2_447_, v_depth_boxed_454_, v_keys_449_, v_vals_450_, v_heq_451_, v_i_452_, v_entries_453_);
lean_dec_ref(v_vals_450_);
lean_dec_ref(v_keys_449_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_456_, lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(v_x_457_, v_x_458_, v_x_459_, v_x_460_);
return v___x_461_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl___closed__4);
v___x_466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1));
v___x_467_ = l_Lean_mkConst(v___x_466_, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = l_Lean_Int_mkType;
v___x_469_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2);
v___x_470_ = l_Lean_Expr_app___override(v___x_469_, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte(void){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natImage(lean_object* v_e_472_, lean_object* v_e_x27_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Meta_Sym_shareCommon(v_e_x27_473_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_487_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v___x_487_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_472_, v_a_474_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_487_, 1);
v___x_489_ = lean_box(0);
lean_inc(v_a_483_);
lean_inc_ref(v_a_482_);
lean_inc(v_a_481_);
lean_inc_ref(v_a_480_);
lean_inc(v_a_479_);
lean_inc_ref(v_a_478_);
lean_inc(v_a_477_);
lean_inc_ref(v_a_476_);
lean_inc(v_a_475_);
lean_inc(v_a_474_);
lean_inc(v_a_486_);
v___x_490_ = lean_grind_internalize(v_a_486_, v_a_488_, v___x_489_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; 
v_unused_498_ = lean_ctor_get(v___x_490_, 0);
lean_dec(v_unused_498_);
v___x_492_ = v___x_490_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_dec(v___x_490_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v_a_486_);
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_486_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_a_486_);
v_a_499_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_490_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_490_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec(v_a_486_);
v_a_507_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_487_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_487_);
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
else
{
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natImage___boxed(lean_object* v_e_515_, lean_object* v_e_x27_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natImage(v_e_515_, v_e_x27_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
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
lean_dec_ref(v_e_515_);
return v_res_528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = lean_box(0);
v___x_537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__3));
v___x_538_ = l_Lean_mkConst(v___x_537_, v___x_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0(lean_object* v_e_539_, lean_object* v_toPure_540_, lean_object* v_toVar_541_, lean_object* v_____do__lift_542_){
_start:
{
if (lean_obj_tag(v_____do__lift_542_) == 1)
{
lean_object* v_val_543_; lean_object* v___x_544_; lean_object* v_h_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v_toVar_541_);
v_val_543_ = lean_ctor_get(v_____do__lift_542_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v_____do__lift_542_, 1);
v___x_544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__4);
v_h_545_ = l_Lean_Expr_app___override(v___x_544_, v_e_539_);
v___x_546_ = lean_nat_to_int(v_val_543_);
v___x_547_ = l_Lean_mkIntLit(v___x_546_);
lean_dec(v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_h_545_);
v___x_549_ = lean_apply_2(v_toPure_540_, lean_box(0), v___x_548_);
return v___x_549_;
}
else
{
lean_object* v___x_550_; 
lean_dec(v_____do__lift_542_);
lean_dec(v_toPure_540_);
v___x_550_ = lean_apply_1(v_toVar_541_, v_e_539_);
return v___x_550_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_box(0);
v___x_557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__1));
v___x_558_ = l_Lean_mkConst(v___x_557_, v___x_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1(lean_object* v_arg_559_, lean_object* v_arg_560_, lean_object* v_fst_561_, lean_object* v_snd_562_, lean_object* v_toPure_563_, lean_object* v_____x_564_){
_start:
{
lean_object* v_fst_565_; lean_object* v_snd_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_577_; 
v_fst_565_ = lean_ctor_get(v_____x_564_, 0);
v_snd_566_ = lean_ctor_get(v_____x_564_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v_____x_564_);
if (v_isSharedCheck_577_ == 0)
{
v___x_568_ = v_____x_564_;
v_isShared_569_ = v_isSharedCheck_577_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_snd_566_);
lean_inc(v_fst_565_);
lean_dec(v_____x_564_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_577_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v_h_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_570_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__2);
lean_inc(v_fst_565_);
lean_inc_ref(v_fst_561_);
v_h_571_ = l_Lean_mkApp6(v___x_570_, v_arg_559_, v_arg_560_, v_fst_561_, v_fst_565_, v_snd_562_, v_snd_566_);
v___x_572_ = l_Lean_mkIntAdd(v_fst_561_, v_fst_565_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 1, v_h_571_);
lean_ctor_set(v___x_568_, 0, v___x_572_);
v___x_574_ = v___x_568_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_h_571_);
v___x_574_ = v_reuseFailAlloc_576_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; 
v___x_575_ = lean_apply_2(v_toPure_563_, lean_box(0), v___x_574_);
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__7(lean_object* v_h_578_, lean_object* v_toPure_579_, lean_object* v_____do__lift_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v_____do__lift_580_);
lean_ctor_set(v___x_581_, 1, v_h_578_);
v___x_582_ = lean_apply_2(v_toPure_579_, lean_box(0), v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__2(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_box(0);
v___x_589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__1));
v___x_590_ = l_Lean_mkConst(v___x_589_, v___x_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11(lean_object* v_arg_591_, lean_object* v_arg_592_, lean_object* v_fst_593_, lean_object* v_snd_594_, lean_object* v_toPure_595_, lean_object* v_image_596_, lean_object* v_e_597_, lean_object* v_toBind_598_, lean_object* v_____x_599_){
_start:
{
lean_object* v_fst_600_; lean_object* v_snd_601_; lean_object* v___x_602_; lean_object* v_h_603_; lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_fst_600_ = lean_ctor_get(v_____x_599_, 0);
lean_inc_n(v_fst_600_, 2);
v_snd_601_ = lean_ctor_get(v_____x_599_, 1);
lean_inc(v_snd_601_);
lean_dec_ref(v_____x_599_);
v___x_602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__2);
lean_inc_ref(v_fst_593_);
v_h_603_ = l_Lean_mkApp6(v___x_602_, v_arg_591_, v_arg_592_, v_fst_593_, v_fst_600_, v_snd_594_, v_snd_601_);
v___f_604_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__7), 3, 2);
lean_closure_set(v___f_604_, 0, v_h_603_);
lean_closure_set(v___f_604_, 1, v_toPure_595_);
v___x_605_ = l_Lean_mkIntMod(v_fst_593_, v_fst_600_);
v___x_606_ = lean_apply_2(v_image_596_, v_e_597_, v___x_605_);
v___x_607_ = lean_apply_4(v_toBind_598_, lean_box(0), lean_box(0), v___x_606_, v___f_604_);
return v___x_607_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__2(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_box(0);
v___x_614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__1));
v___x_615_ = l_Lean_mkConst(v___x_614_, v___x_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6(lean_object* v_arg_616_, lean_object* v_arg_617_, lean_object* v_fst_618_, lean_object* v_snd_619_, lean_object* v_toPure_620_, lean_object* v_image_621_, lean_object* v_e_622_, lean_object* v_toBind_623_, lean_object* v_____x_624_){
_start:
{
lean_object* v_fst_625_; lean_object* v_snd_626_; lean_object* v___x_627_; lean_object* v_h_628_; lean_object* v___f_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_fst_625_ = lean_ctor_get(v_____x_624_, 0);
lean_inc_n(v_fst_625_, 2);
v_snd_626_ = lean_ctor_get(v_____x_624_, 1);
lean_inc(v_snd_626_);
lean_dec_ref(v_____x_624_);
v___x_627_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__2);
lean_inc_ref(v_fst_618_);
v_h_628_ = l_Lean_mkApp6(v___x_627_, v_arg_616_, v_arg_617_, v_fst_618_, v_fst_625_, v_snd_619_, v_snd_626_);
v___f_629_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__7), 3, 2);
lean_closure_set(v___f_629_, 0, v_h_628_);
lean_closure_set(v___f_629_, 1, v_toPure_620_);
v___x_630_ = l_Lean_mkIntDiv(v_fst_618_, v_fst_625_);
v___x_631_ = lean_apply_2(v_image_621_, v_e_622_, v___x_630_);
v___x_632_ = lean_apply_4(v_toBind_623_, lean_box(0), lean_box(0), v___x_631_, v___f_629_);
return v___x_632_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__2(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_box(0);
v___x_639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__1));
v___x_640_ = l_Lean_mkConst(v___x_639_, v___x_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13(lean_object* v_arg_641_, lean_object* v_arg_642_, lean_object* v_toPure_643_, lean_object* v_image_644_, lean_object* v_e_645_, lean_object* v_toBind_646_, lean_object* v_____x_647_){
_start:
{
lean_object* v_fst_648_; lean_object* v_snd_649_; lean_object* v___x_650_; lean_object* v_h_651_; lean_object* v___f_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_fst_648_ = lean_ctor_get(v_____x_647_, 0);
lean_inc_n(v_fst_648_, 2);
v_snd_649_ = lean_ctor_get(v_____x_647_, 1);
lean_inc(v_snd_649_);
lean_dec_ref(v_____x_647_);
v___x_650_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__2);
lean_inc_ref(v_arg_642_);
v_h_651_ = l_Lean_mkApp4(v___x_650_, v_arg_641_, v_arg_642_, v_fst_648_, v_snd_649_);
v___f_652_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__7), 3, 2);
lean_closure_set(v___f_652_, 0, v_h_651_);
lean_closure_set(v___f_652_, 1, v_toPure_643_);
v___x_653_ = l_Lean_mkIntPowNat(v_fst_648_, v_arg_642_);
v___x_654_ = lean_apply_2(v_image_644_, v_e_645_, v___x_653_);
v___x_655_ = lean_apply_4(v_toBind_646_, lean_box(0), lean_box(0), v___x_654_, v___f_652_);
return v___x_655_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__2(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = lean_box(0);
v___x_662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__1));
v___x_663_ = l_Lean_mkConst(v___x_662_, v___x_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4(lean_object* v_arg_664_, lean_object* v_arg_665_, lean_object* v_fst_666_, lean_object* v_snd_667_, lean_object* v_toPure_668_, lean_object* v_____x_669_){
_start:
{
lean_object* v_fst_670_; lean_object* v_snd_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_682_; 
v_fst_670_ = lean_ctor_get(v_____x_669_, 0);
v_snd_671_ = lean_ctor_get(v_____x_669_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_____x_669_);
if (v_isSharedCheck_682_ == 0)
{
v___x_673_ = v_____x_669_;
v_isShared_674_ = v_isSharedCheck_682_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_snd_671_);
lean_inc(v_fst_670_);
lean_dec(v_____x_669_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_682_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v_h_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__2);
lean_inc(v_fst_670_);
lean_inc_ref(v_fst_666_);
v_h_676_ = l_Lean_mkApp6(v___x_675_, v_arg_664_, v_arg_665_, v_fst_666_, v_fst_670_, v_snd_667_, v_snd_671_);
v___x_677_ = l_Lean_mkIntMul(v_fst_666_, v_fst_670_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v_h_676_);
lean_ctor_set(v___x_673_, 0, v___x_677_);
v___x_679_ = v___x_673_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_h_676_);
v___x_679_ = v_reuseFailAlloc_681_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; 
v___x_680_ = lean_apply_2(v_toPure_668_, lean_box(0), v___x_679_);
return v___x_680_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__3(lean_object* v_toVar_713_, lean_object* v_e_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_image_717_, lean_object* v_arg_718_, lean_object* v_toBind_719_, lean_object* v___f_720_, uint8_t v_____do__lift_721_){
_start:
{
if (v_____do__lift_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec(v___f_720_);
lean_dec(v_toBind_719_);
lean_dec_ref(v_arg_718_);
lean_dec(v_image_717_);
lean_dec(v_inst_716_);
lean_dec_ref(v_inst_715_);
v___x_722_ = lean_apply_1(v_toVar_713_, v_e_714_);
return v___x_722_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec_ref(v_e_714_);
v___x_723_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg(v_inst_715_, v_inst_716_, v_toVar_713_, v_image_717_, v_arg_718_);
v___x_724_ = lean_apply_4(v_toBind_719_, lean_box(0), lean_box(0), v___x_723_, v___f_720_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__3___boxed(lean_object* v_toVar_725_, lean_object* v_e_726_, lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_image_729_, lean_object* v_arg_730_, lean_object* v_toBind_731_, lean_object* v___f_732_, lean_object* v_____do__lift_733_){
_start:
{
uint8_t v_____do__lift_1888__boxed_734_; lean_object* v_res_735_; 
v_____do__lift_1888__boxed_734_ = lean_unbox(v_____do__lift_733_);
v_res_735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__3(v_toVar_725_, v_e_726_, v_inst_727_, v_inst_728_, v_image_729_, v_arg_730_, v_toBind_731_, v___f_732_, v_____do__lift_1888__boxed_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__5(lean_object* v_arg_736_, lean_object* v_arg_737_, lean_object* v_toPure_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_toVar_741_, lean_object* v_image_742_, lean_object* v_toBind_743_, lean_object* v_____x_744_){
_start:
{
lean_object* v_fst_745_; lean_object* v_snd_746_; lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_fst_745_ = lean_ctor_get(v_____x_744_, 0);
lean_inc(v_fst_745_);
v_snd_746_ = lean_ctor_get(v_____x_744_, 1);
lean_inc(v_snd_746_);
lean_dec_ref(v_____x_744_);
lean_inc_ref(v_arg_737_);
v___f_747_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4), 6, 5);
lean_closure_set(v___f_747_, 0, v_arg_736_);
lean_closure_set(v___f_747_, 1, v_arg_737_);
lean_closure_set(v___f_747_, 2, v_fst_745_);
lean_closure_set(v___f_747_, 3, v_snd_746_);
lean_closure_set(v___f_747_, 4, v_toPure_738_);
v___x_748_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg(v_inst_739_, v_inst_740_, v_toVar_741_, v_image_742_, v_arg_737_);
v___x_749_ = lean_apply_4(v_toBind_743_, lean_box(0), lean_box(0), v___x_748_, v___f_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__8(lean_object* v_arg_750_, lean_object* v_arg_751_, lean_object* v_toPure_752_, lean_object* v_image_753_, lean_object* v_e_754_, lean_object* v_toBind_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_toVar_758_, lean_object* v_____x_759_){
_start:
{
lean_object* v_fst_760_; lean_object* v_snd_761_; lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_fst_760_ = lean_ctor_get(v_____x_759_, 0);
lean_inc(v_fst_760_);
v_snd_761_ = lean_ctor_get(v_____x_759_, 1);
lean_inc(v_snd_761_);
lean_dec_ref(v_____x_759_);
lean_inc(v_toBind_755_);
lean_inc(v_image_753_);
lean_inc_ref(v_arg_751_);
v___f_762_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6), 9, 8);
lean_closure_set(v___f_762_, 0, v_arg_750_);
lean_closure_set(v___f_762_, 1, v_arg_751_);
lean_closure_set(v___f_762_, 2, v_fst_760_);
lean_closure_set(v___f_762_, 3, v_snd_761_);
lean_closure_set(v___f_762_, 4, v_toPure_752_);
lean_closure_set(v___f_762_, 5, v_image_753_);
lean_closure_set(v___f_762_, 6, v_e_754_);
lean_closure_set(v___f_762_, 7, v_toBind_755_);
v___x_763_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg(v_inst_756_, v_inst_757_, v_toVar_758_, v_image_753_, v_arg_751_);
v___x_764_ = lean_apply_4(v_toBind_755_, lean_box(0), lean_box(0), v___x_763_, v___f_762_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__9(lean_object* v_arg_765_, lean_object* v_arg_766_, lean_object* v_toPure_767_, lean_object* v_image_768_, lean_object* v_e_769_, lean_object* v_toBind_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v_toVar_773_, lean_object* v_____x_774_){
_start:
{
lean_object* v_fst_775_; lean_object* v_snd_776_; lean_object* v___f_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_fst_775_ = lean_ctor_get(v_____x_774_, 0);
lean_inc(v_fst_775_);
v_snd_776_ = lean_ctor_get(v_____x_774_, 1);
lean_inc(v_snd_776_);
lean_dec_ref(v_____x_774_);
lean_inc(v_toBind_770_);
lean_inc(v_image_768_);
lean_inc_ref(v_arg_766_);
v___f_777_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11), 9, 8);
lean_closure_set(v___f_777_, 0, v_arg_765_);
lean_closure_set(v___f_777_, 1, v_arg_766_);
lean_closure_set(v___f_777_, 2, v_fst_775_);
lean_closure_set(v___f_777_, 3, v_snd_776_);
lean_closure_set(v___f_777_, 4, v_toPure_767_);
lean_closure_set(v___f_777_, 5, v_image_768_);
lean_closure_set(v___f_777_, 6, v_e_769_);
lean_closure_set(v___f_777_, 7, v_toBind_770_);
v___x_778_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg(v_inst_771_, v_inst_772_, v_toVar_773_, v_image_768_, v_arg_766_);
v___x_779_ = lean_apply_4(v_toBind_770_, lean_box(0), lean_box(0), v___x_778_, v___f_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12(lean_object* v_toVar_780_, lean_object* v_e_781_, lean_object* v_toPure_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_image_785_, lean_object* v_toBind_786_, lean_object* v___f_787_, lean_object* v_____x_788_){
_start:
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = l_Lean_Expr_cleanupAnnotations(v_____x_788_);
v___x_790_ = l_Lean_Expr_isApp(v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_dec_ref(v___x_789_);
lean_dec(v___f_787_);
lean_dec(v_toBind_786_);
lean_dec(v_image_785_);
lean_dec(v_inst_784_);
lean_dec_ref(v_inst_783_);
lean_dec(v_toPure_782_);
v___x_791_ = lean_apply_1(v_toVar_780_, v_e_781_);
return v___x_791_;
}
else
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = l_Lean_Expr_appFnCleanup___redArg(v___x_789_);
v___x_793_ = l_Lean_Expr_isApp(v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_dec_ref(v___x_792_);
lean_dec_ref(v___x_789_);
lean_dec(v___f_787_);
lean_dec(v_toBind_786_);
lean_dec(v_image_785_);
lean_dec(v_inst_784_);
lean_dec_ref(v_inst_783_);
lean_dec(v_toPure_782_);
v___x_794_ = lean_apply_1(v_toVar_780_, v_e_781_);
return v___x_794_;
}
else
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = l_Lean_Expr_appFnCleanup___redArg(v___x_792_);
v___x_796_ = l_Lean_Expr_isApp(v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; 
lean_dec_ref(v___x_795_);
lean_dec_ref(v___x_792_);
lean_dec_ref(v___x_789_);
lean_dec(v___f_787_);
lean_dec(v_toBind_786_);
lean_dec(v_image_785_);
lean_dec(v_inst_784_);
lean_dec_ref(v_inst_783_);
lean_dec(v_toPure_782_);
v___x_797_ = lean_apply_1(v_toVar_780_, v_e_781_);
return v___x_797_;
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_798_ = l_Lean_Expr_appFnCleanup___redArg(v___x_795_);
v___x_799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__2));
v___x_800_ = l_Lean_Expr_isConstOf(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
uint8_t v___x_801_; 
lean_dec(v___f_787_);
v___x_801_ = l_Lean_Expr_isApp(v___x_798_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
lean_dec_ref(v___x_798_);
lean_dec_ref(v___x_795_);
lean_dec_ref(v___x_792_);
lean_dec_ref(v___x_789_);
lean_dec(v_toBind_786_);
lean_dec(v_image_785_);
lean_dec(v_inst_784_);
lean_dec_ref(v_inst_783_);
lean_dec(v_toPure_782_);
v___x_802_ = lean_apply_1(v_toVar_780_, v_e_781_);
return v___x_802_;
}
else
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = l_Lean_Expr_appFnCleanup___redArg(v___x_798_);
lean_dec_ref(v___x_798_);
v___x_804_ = l_Lean_Expr_isApp(v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
lean_dec_ref(v___x_803_);
lean_dec_ref(v___x_795_);
lean_dec_ref(v___x_792_);
lean_dec_ref(v___x_789_);
lean_dec(v_toBind_786_);
lean_dec(v_image_785_);
lean_dec(v_inst_784_);
lean_dec_ref(v_inst_783_);
lean_dec(v_toPure_782_);
v___x_805_ = lean_apply_1(v_toVar_780_, v_e_781_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = l_Lean_Expr_appFnCleanup___redArg(v___x_803_);
lean_dec_ref(v___x_803_);
v___x_807_ = l_Lean_Expr_isApp(v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; 
lean_dec_ref(v___x_806_);
lean_dec_ref(v___x_795_);
lean_dec_ref(v___x_792_);
lean_dec_ref(v___x_789_);
lean_dec(v_toBind_786_);
lean_dec(v_image_785_);
lean_dec(v_inst_784_);
lean_dec_ref(v_inst_783_);
lean_dec(v_toPure_782_);
v___x_808_ = lean_apply_1(v_toVar_780_, v_e_781_);
return v___x_808_;
}
else
{
lean_object* v_arg_809_; lean_object* v_arg_810_; lean_object* v_arg_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v_arg_809_ = lean_ctor_get(v___x_789_, 1);
lean_inc_ref(v_arg_809_);
lean_dec_ref(v___x_789_);
v_arg_810_ = lean_ctor_get(v___x_792_, 1);
lean_inc_ref(v_arg_810_);
lean_dec_ref(v___x_792_);
v_arg_811_ = lean_ctor_get(v___x_795_, 1);
lean_inc_ref(v_arg_811_);
lean_dec_ref(v___x_795_);
v___x_812_ = l_Lean_Expr_appFnCleanup___redArg(v___x_806_);
lean_dec_ref(v___x_806_);
v___x_813_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__5));
v___x_814_ = l_Lean_Expr_isConstOf(v___x_812_, v___x_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__8));
v___x_816_ = l_Lean_Expr_isConstOf(v___x_812_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__11));
v___x_818_ = l_Lean_Expr_isConstOf(v___x_812_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__14));
v___x_820_ = l_Lean_Expr_isConstOf(v___x_812_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__17));
v___x_822_ = l_Lean_Expr_isConstOf(v___x_812_, v___x_821_);
lean_dec_ref(v___x_812_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; 
lean_dec_ref(v_arg_811_);
lean_dec_ref(v_arg_810_);
lean_dec_ref(v_arg_809_);
lean_dec(v_toBind_786_);
lean_dec(v_image_785_);
lean_dec(v_inst_784_);
lean_dec_ref(v_inst_783_);
lean_dec(v_toPure_782_);
v___x_823_ = lean_apply_1(v_toVar_780_, v_e_781_);
return v___x_823_;
}
else
{
lean_object* v___f_824_; lean_object* v___f_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
lean_inc_n(v_toBind_786_, 2);
lean_inc(v_image_785_);
lean_inc(v_toVar_780_);
lean_inc_n(v_inst_784_, 2);
lean_inc_ref(v_inst_783_);
lean_inc_ref(v_arg_810_);
v___f_824_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__2), 9, 8);
lean_closure_set(v___f_824_, 0, v_arg_810_);
lean_closure_set(v___f_824_, 1, v_arg_809_);
lean_closure_set(v___f_824_, 2, v_toPure_782_);
lean_closure_set(v___f_824_, 3, v_inst_783_);
lean_closure_set(v___f_824_, 4, v_inst_784_);
lean_closure_set(v___f_824_, 5, v_toVar_780_);
lean_closure_set(v___f_824_, 6, v_image_785_);
lean_closure_set(v___f_824_, 7, v_toBind_786_);
v___f_825_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_825_, 0, v_toVar_780_);
lean_closure_set(v___f_825_, 1, v_e_781_);
lean_closure_set(v___f_825_, 2, v_inst_783_);
lean_closure_set(v___f_825_, 3, v_inst_784_);
lean_closure_set(v___f_825_, 4, v_image_785_);
lean_closure_set(v___f_825_, 5, v_arg_810_);
lean_closure_set(v___f_825_, 6, v_toBind_786_);
lean_closure_set(v___f_825_, 7, v___f_824_);
v___x_826_ = lean_alloc_closure((void*)(l_Lean_Meta_Structural_isInstHAddNat___boxed), 6, 1);
lean_closure_set(v___x_826_, 0, v_arg_811_);
v___x_827_ = lean_apply_2(v_inst_784_, lean_box(0), v___x_826_);
v___x_828_ = lean_apply_4(v_toBind_786_, lean_box(0), lean_box(0), v___x_827_, v___f_825_);
return v___x_828_;
}
}
else
{
lean_object* v___f_829_; lean_object* v___f_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec_ref(v___x_812_);
lean_inc_n(v_toBind_786_, 2);
lean_inc(v_image_785_);
lean_inc(v_toVar_780_);
lean_inc_n(v_inst_784_, 2);
lean_inc_ref(v_inst_783_);
lean_inc_ref(v_arg_810_);
v___f_829_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__5), 9, 8);
lean_closure_set(v___f_829_, 0, v_arg_810_);
lean_closure_set(v___f_829_, 1, v_arg_809_);
lean_closure_set(v___f_829_, 2, v_toPure_782_);
lean_closure_set(v___f_829_, 3, v_inst_783_);
lean_closure_set(v___f_829_, 4, v_inst_784_);
lean_closure_set(v___f_829_, 5, v_toVar_780_);
lean_closure_set(v___f_829_, 6, v_image_785_);
lean_closure_set(v___f_829_, 7, v_toBind_786_);
v___f_830_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_830_, 0, v_toVar_780_);
lean_closure_set(v___f_830_, 1, v_e_781_);
lean_closure_set(v___f_830_, 2, v_inst_783_);
lean_closure_set(v___f_830_, 3, v_inst_784_);
lean_closure_set(v___f_830_, 4, v_image_785_);
lean_closure_set(v___f_830_, 5, v_arg_810_);
lean_closure_set(v___f_830_, 6, v_toBind_786_);
lean_closure_set(v___f_830_, 7, v___f_829_);
v___x_831_ = lean_alloc_closure((void*)(l_Lean_Meta_Structural_isInstHMulNat___boxed), 6, 1);
lean_closure_set(v___x_831_, 0, v_arg_811_);
v___x_832_ = lean_apply_2(v_inst_784_, lean_box(0), v___x_831_);
v___x_833_ = lean_apply_4(v_toBind_786_, lean_box(0), lean_box(0), v___x_832_, v___f_830_);
return v___x_833_;
}
}
else
{
lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v___x_812_);
lean_inc(v_toVar_780_);
lean_inc_n(v_inst_784_, 2);
lean_inc_ref(v_inst_783_);
lean_inc_n(v_toBind_786_, 2);
lean_inc_ref(v_e_781_);
lean_inc(v_image_785_);
lean_inc_ref(v_arg_810_);
v___f_834_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__8), 10, 9);
lean_closure_set(v___f_834_, 0, v_arg_810_);
lean_closure_set(v___f_834_, 1, v_arg_809_);
lean_closure_set(v___f_834_, 2, v_toPure_782_);
lean_closure_set(v___f_834_, 3, v_image_785_);
lean_closure_set(v___f_834_, 4, v_e_781_);
lean_closure_set(v___f_834_, 5, v_toBind_786_);
lean_closure_set(v___f_834_, 6, v_inst_783_);
lean_closure_set(v___f_834_, 7, v_inst_784_);
lean_closure_set(v___f_834_, 8, v_toVar_780_);
v___f_835_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_835_, 0, v_toVar_780_);
lean_closure_set(v___f_835_, 1, v_e_781_);
lean_closure_set(v___f_835_, 2, v_inst_783_);
lean_closure_set(v___f_835_, 3, v_inst_784_);
lean_closure_set(v___f_835_, 4, v_image_785_);
lean_closure_set(v___f_835_, 5, v_arg_810_);
lean_closure_set(v___f_835_, 6, v_toBind_786_);
lean_closure_set(v___f_835_, 7, v___f_834_);
v___x_836_ = lean_alloc_closure((void*)(l_Lean_Meta_Structural_isInstHDivNat___boxed), 6, 1);
lean_closure_set(v___x_836_, 0, v_arg_811_);
v___x_837_ = lean_apply_2(v_inst_784_, lean_box(0), v___x_836_);
v___x_838_ = lean_apply_4(v_toBind_786_, lean_box(0), lean_box(0), v___x_837_, v___f_835_);
return v___x_838_;
}
}
else
{
lean_object* v___f_839_; lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec_ref(v___x_812_);
lean_inc(v_toVar_780_);
lean_inc_n(v_inst_784_, 2);
lean_inc_ref(v_inst_783_);
lean_inc_n(v_toBind_786_, 2);
lean_inc_ref(v_e_781_);
lean_inc(v_image_785_);
lean_inc_ref(v_arg_810_);
v___f_839_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__9), 10, 9);
lean_closure_set(v___f_839_, 0, v_arg_810_);
lean_closure_set(v___f_839_, 1, v_arg_809_);
lean_closure_set(v___f_839_, 2, v_toPure_782_);
lean_closure_set(v___f_839_, 3, v_image_785_);
lean_closure_set(v___f_839_, 4, v_e_781_);
lean_closure_set(v___f_839_, 5, v_toBind_786_);
lean_closure_set(v___f_839_, 6, v_inst_783_);
lean_closure_set(v___f_839_, 7, v_inst_784_);
lean_closure_set(v___f_839_, 8, v_toVar_780_);
v___f_840_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_840_, 0, v_toVar_780_);
lean_closure_set(v___f_840_, 1, v_e_781_);
lean_closure_set(v___f_840_, 2, v_inst_783_);
lean_closure_set(v___f_840_, 3, v_inst_784_);
lean_closure_set(v___f_840_, 4, v_image_785_);
lean_closure_set(v___f_840_, 5, v_arg_810_);
lean_closure_set(v___f_840_, 6, v_toBind_786_);
lean_closure_set(v___f_840_, 7, v___f_839_);
v___x_841_ = lean_alloc_closure((void*)(l_Lean_Meta_Structural_isInstHModNat___boxed), 6, 1);
lean_closure_set(v___x_841_, 0, v_arg_811_);
v___x_842_ = lean_apply_2(v_inst_784_, lean_box(0), v___x_841_);
v___x_843_ = lean_apply_4(v_toBind_786_, lean_box(0), lean_box(0), v___x_842_, v___f_840_);
return v___x_843_;
}
}
else
{
lean_object* v___f_844_; lean_object* v___f_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec_ref(v___x_812_);
lean_inc_n(v_toBind_786_, 2);
lean_inc_ref(v_e_781_);
lean_inc(v_image_785_);
lean_inc_ref(v_arg_810_);
v___f_844_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13), 7, 6);
lean_closure_set(v___f_844_, 0, v_arg_810_);
lean_closure_set(v___f_844_, 1, v_arg_809_);
lean_closure_set(v___f_844_, 2, v_toPure_782_);
lean_closure_set(v___f_844_, 3, v_image_785_);
lean_closure_set(v___f_844_, 4, v_e_781_);
lean_closure_set(v___f_844_, 5, v_toBind_786_);
lean_inc(v_inst_784_);
v___f_845_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_845_, 0, v_toVar_780_);
lean_closure_set(v___f_845_, 1, v_e_781_);
lean_closure_set(v___f_845_, 2, v_inst_783_);
lean_closure_set(v___f_845_, 3, v_inst_784_);
lean_closure_set(v___f_845_, 4, v_image_785_);
lean_closure_set(v___f_845_, 5, v_arg_810_);
lean_closure_set(v___f_845_, 6, v_toBind_786_);
lean_closure_set(v___f_845_, 7, v___f_844_);
v___x_846_ = lean_alloc_closure((void*)(l_Lean_Meta_Structural_isInstHPowNat___boxed), 6, 1);
lean_closure_set(v___x_846_, 0, v_arg_811_);
v___x_847_ = lean_apply_2(v_inst_784_, lean_box(0), v___x_846_);
v___x_848_ = lean_apply_4(v_toBind_786_, lean_box(0), lean_box(0), v___x_847_, v___f_845_);
return v___x_848_;
}
}
}
}
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref(v___x_798_);
lean_dec_ref(v___x_795_);
lean_dec_ref(v___x_792_);
lean_dec_ref(v___x_789_);
lean_dec(v_image_785_);
lean_dec_ref(v_inst_783_);
lean_dec(v_toPure_782_);
lean_dec(v_toVar_780_);
v___x_849_ = lean_alloc_closure((void*)(l_Lean_Meta_getNatValue_x3f___boxed), 6, 1);
lean_closure_set(v___x_849_, 0, v_e_781_);
v___x_850_ = lean_apply_2(v_inst_784_, lean_box(0), v___x_849_);
v___x_851_ = lean_apply_4(v_toBind_786_, lean_box(0), lean_box(0), v___x_850_, v___f_787_);
return v___x_851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___boxed(lean_object* v_toVar_852_, lean_object* v_e_853_, lean_object* v_toPure_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_image_857_, lean_object* v_toBind_858_, lean_object* v___f_859_, lean_object* v_____x_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12(v_toVar_852_, v_e_853_, v_toPure_854_, v_inst_855_, v_inst_856_, v_image_857_, v_toBind_858_, v___f_859_, v_____x_860_);
lean_dec_ref(v_____x_860_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg(lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_toVar_864_, lean_object* v_image_865_, lean_object* v_e_866_){
_start:
{
lean_object* v_toApplicative_867_; lean_object* v_toBind_868_; lean_object* v_toPure_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___f_872_; lean_object* v___f_873_; lean_object* v___x_874_; 
v_toApplicative_867_ = lean_ctor_get(v_inst_862_, 0);
v_toBind_868_ = lean_ctor_get(v_inst_862_, 1);
lean_inc_n(v_toBind_868_, 2);
v_toPure_869_ = lean_ctor_get(v_toApplicative_867_, 1);
lean_inc_n(v_toPure_869_, 2);
lean_inc_ref_n(v_e_866_, 2);
v___x_870_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_870_, 0, v_e_866_);
lean_inc(v_inst_863_);
v___x_871_ = lean_apply_2(v_inst_863_, lean_box(0), v___x_870_);
lean_inc(v_toVar_864_);
v___f_872_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0), 4, 3);
lean_closure_set(v___f_872_, 0, v_e_866_);
lean_closure_set(v___f_872_, 1, v_toPure_869_);
lean_closure_set(v___f_872_, 2, v_toVar_864_);
v___f_873_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___boxed), 9, 8);
lean_closure_set(v___f_873_, 0, v_toVar_864_);
lean_closure_set(v___f_873_, 1, v_e_866_);
lean_closure_set(v___f_873_, 2, v_toPure_869_);
lean_closure_set(v___f_873_, 3, v_inst_862_);
lean_closure_set(v___f_873_, 4, v_inst_863_);
lean_closure_set(v___f_873_, 5, v_image_865_);
lean_closure_set(v___f_873_, 6, v_toBind_868_);
lean_closure_set(v___f_873_, 7, v___f_872_);
v___x_874_ = lean_apply_4(v_toBind_868_, lean_box(0), lean_box(0), v___x_871_, v___f_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__2(lean_object* v_arg_875_, lean_object* v_arg_876_, lean_object* v_toPure_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_toVar_880_, lean_object* v_image_881_, lean_object* v_toBind_882_, lean_object* v_____x_883_){
_start:
{
lean_object* v_fst_884_; lean_object* v_snd_885_; lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_fst_884_ = lean_ctor_get(v_____x_883_, 0);
lean_inc(v_fst_884_);
v_snd_885_ = lean_ctor_get(v_____x_883_, 1);
lean_inc(v_snd_885_);
lean_dec_ref(v_____x_883_);
lean_inc_ref(v_arg_876_);
v___f_886_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1), 6, 5);
lean_closure_set(v___f_886_, 0, v_arg_875_);
lean_closure_set(v___f_886_, 1, v_arg_876_);
lean_closure_set(v___f_886_, 2, v_fst_884_);
lean_closure_set(v___f_886_, 3, v_snd_885_);
lean_closure_set(v___f_886_, 4, v_toPure_877_);
v___x_887_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg(v_inst_878_, v_inst_879_, v_toVar_880_, v_image_881_, v_arg_876_);
v___x_888_ = lean_apply_4(v_toBind_882_, lean_box(0), lean_box(0), v___x_887_, v___f_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux(lean_object* v_m_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_toVar_892_, lean_object* v_image_893_, lean_object* v_e_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg(v_inst_890_, v_inst_891_, v_toVar_892_, v_image_893_, v_e_894_);
return v___x_895_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_896_, lean_object* v_i_897_, lean_object* v_k_898_){
_start:
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = lean_array_get_size(v_keys_896_);
v___x_900_ = lean_nat_dec_lt(v_i_897_, v___x_899_);
if (v___x_900_ == 0)
{
lean_dec(v_i_897_);
return v___x_900_;
}
else
{
lean_object* v_k_x27_901_; size_t v___x_902_; size_t v___x_903_; uint8_t v___x_904_; 
v_k_x27_901_ = lean_array_fget_borrowed(v_keys_896_, v_i_897_);
v___x_902_ = lean_ptr_addr(v_k_898_);
v___x_903_ = lean_ptr_addr(v_k_x27_901_);
v___x_904_ = lean_usize_dec_eq(v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_add(v_i_897_, v___x_905_);
lean_dec(v_i_897_);
v_i_897_ = v___x_906_;
goto _start;
}
else
{
lean_dec(v_i_897_);
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_908_, lean_object* v_i_909_, lean_object* v_k_910_){
_start:
{
uint8_t v_res_911_; lean_object* v_r_912_; 
v_res_911_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0_spec__1___redArg(v_keys_908_, v_i_909_, v_k_910_);
lean_dec_ref(v_k_910_);
lean_dec_ref(v_keys_908_);
v_r_912_ = lean_box(v_res_911_);
return v_r_912_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0___redArg(lean_object* v_x_913_, size_t v_x_914_, lean_object* v_x_915_){
_start:
{
if (lean_obj_tag(v_x_913_) == 0)
{
lean_object* v_es_916_; lean_object* v___x_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v_j_920_; lean_object* v___x_921_; 
v_es_916_ = lean_ctor_get(v_x_913_, 0);
v___x_917_ = lean_box(2);
v___x_918_ = ((size_t)31ULL);
v___x_919_ = lean_usize_land(v_x_914_, v___x_918_);
v_j_920_ = lean_usize_to_nat(v___x_919_);
v___x_921_ = lean_array_get_borrowed(v___x_917_, v_es_916_, v_j_920_);
lean_dec(v_j_920_);
switch(lean_obj_tag(v___x_921_))
{
case 0:
{
lean_object* v_key_922_; size_t v___x_923_; size_t v___x_924_; uint8_t v___x_925_; 
v_key_922_ = lean_ctor_get(v___x_921_, 0);
v___x_923_ = lean_ptr_addr(v_x_915_);
v___x_924_ = lean_ptr_addr(v_key_922_);
v___x_925_ = lean_usize_dec_eq(v___x_923_, v___x_924_);
return v___x_925_;
}
case 1:
{
lean_object* v_node_926_; size_t v___x_927_; size_t v___x_928_; 
v_node_926_ = lean_ctor_get(v___x_921_, 0);
v___x_927_ = ((size_t)5ULL);
v___x_928_ = lean_usize_shift_right(v_x_914_, v___x_927_);
v_x_913_ = v_node_926_;
v_x_914_ = v___x_928_;
goto _start;
}
default: 
{
uint8_t v___x_930_; 
v___x_930_ = 0;
return v___x_930_;
}
}
}
else
{
lean_object* v_ks_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_ks_931_ = lean_ctor_get(v_x_913_, 0);
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0_spec__1___redArg(v_ks_931_, v___x_932_, v_x_915_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0___redArg___boxed(lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
size_t v_x_29558__boxed_937_; uint8_t v_res_938_; lean_object* v_r_939_; 
v_x_29558__boxed_937_ = lean_unbox_usize(v_x_935_);
lean_dec(v_x_935_);
v_res_938_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0___redArg(v_x_934_, v_x_29558__boxed_937_, v_x_936_);
lean_dec_ref(v_x_936_);
lean_dec_ref(v_x_934_);
v_r_939_ = lean_box(v_res_938_);
return v_r_939_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0___redArg(lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
size_t v___x_942_; size_t v___x_943_; size_t v___x_944_; uint64_t v___x_945_; size_t v___x_946_; uint8_t v___x_947_; 
v___x_942_ = lean_ptr_addr(v_x_941_);
v___x_943_ = ((size_t)3ULL);
v___x_944_ = lean_usize_shift_right(v___x_942_, v___x_943_);
v___x_945_ = lean_usize_to_uint64(v___x_944_);
v___x_946_ = lean_uint64_to_usize(v___x_945_);
v___x_947_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0___redArg(v_x_940_, v___x_946_, v_x_941_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0___redArg___boxed(lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
uint8_t v_res_950_; lean_object* v_r_951_; 
v_res_950_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0___redArg(v_x_948_, v_x_949_);
lean_dec_ref(v_x_949_);
lean_dec_ref(v_x_948_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__5(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = lean_box(0);
v___x_962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__4));
v___x_963_ = l_Lean_mkConst(v___x_962_, v___x_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(lean_object* v_e_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___y_977_; lean_object* v_t_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v_e_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___x_1058_; 
lean_inc_ref(v_e_964_);
v___x_1058_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_964_, v___y_972_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = l_Lean_Expr_cleanupAnnotations(v_a_1059_);
lean_dec(v_a_1059_);
v___x_1061_ = l_Lean_Expr_isApp(v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec_ref(v___x_1060_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1060_);
v___x_1063_ = l_Lean_Expr_isApp(v___x_1062_);
if (v___x_1063_ == 0)
{
lean_dec_ref(v___x_1062_);
lean_dec_ref(v___x_1060_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1062_);
v___x_1065_ = l_Lean_Expr_isApp(v___x_1064_);
if (v___x_1065_ == 0)
{
lean_dec_ref(v___x_1064_);
lean_dec_ref(v___x_1062_);
lean_dec_ref(v___x_1060_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1064_);
v___x_1067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__2));
v___x_1068_ = l_Lean_Expr_isConstOf(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
uint8_t v___x_1069_; 
v___x_1069_ = l_Lean_Expr_isApp(v___x_1066_);
if (v___x_1069_ == 0)
{
lean_dec_ref(v___x_1066_);
lean_dec_ref(v___x_1064_);
lean_dec_ref(v___x_1062_);
lean_dec_ref(v___x_1060_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1066_);
lean_dec_ref(v___x_1066_);
v___x_1071_ = l_Lean_Expr_isApp(v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec_ref(v___x_1070_);
lean_dec_ref(v___x_1064_);
lean_dec_ref(v___x_1062_);
lean_dec_ref(v___x_1060_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1070_);
lean_dec_ref(v___x_1070_);
v___x_1073_ = l_Lean_Expr_isApp(v___x_1072_);
if (v___x_1073_ == 0)
{
lean_dec_ref(v___x_1072_);
lean_dec_ref(v___x_1064_);
lean_dec_ref(v___x_1062_);
lean_dec_ref(v___x_1060_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
else
{
lean_object* v_arg_1074_; lean_object* v_arg_1075_; lean_object* v_arg_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_arg_1074_ = lean_ctor_get(v___x_1060_, 1);
lean_inc_ref(v_arg_1074_);
lean_dec_ref(v___x_1060_);
v_arg_1075_ = lean_ctor_get(v___x_1062_, 1);
lean_inc_ref(v_arg_1075_);
lean_dec_ref(v___x_1062_);
v_arg_1076_ = lean_ctor_get(v___x_1064_, 1);
lean_inc_ref(v_arg_1076_);
lean_dec_ref(v___x_1064_);
v___x_1077_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1072_);
lean_dec_ref(v___x_1072_);
v___x_1078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__5));
v___x_1079_ = l_Lean_Expr_isConstOf(v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__8));
v___x_1081_ = l_Lean_Expr_isConstOf(v___x_1077_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__11));
v___x_1083_ = l_Lean_Expr_isConstOf(v___x_1077_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__14));
v___x_1085_ = l_Lean_Expr_isConstOf(v___x_1077_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__17));
v___x_1087_ = l_Lean_Expr_isConstOf(v___x_1077_, v___x_1086_);
lean_dec_ref(v___x_1077_);
if (v___x_1087_ == 0)
{
lean_dec_ref(v_arg_1076_);
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_1076_, v___y_972_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; uint8_t v___x_1090_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = lean_unbox(v_a_1089_);
lean_dec(v_a_1089_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1091_; 
lean_dec_ref(v_e_964_);
lean_inc_ref(v_arg_1075_);
v___x_1091_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(v_arg_1075_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v_fst_1093_; lean_object* v_snd_1094_; lean_object* v___x_1095_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v_fst_1093_ = lean_ctor_get(v_a_1092_, 0);
lean_inc(v_fst_1093_);
v_snd_1094_ = lean_ctor_get(v_a_1092_, 1);
lean_inc(v_snd_1094_);
lean_dec(v_a_1092_);
lean_inc_ref(v_arg_1074_);
v___x_1095_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(v_arg_1074_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1115_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1098_ = v___x_1095_;
v_isShared_1099_ = v_isSharedCheck_1115_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1115_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_fst_1100_; lean_object* v_snd_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1114_; 
v_fst_1100_ = lean_ctor_get(v_a_1096_, 0);
v_snd_1101_ = lean_ctor_get(v_a_1096_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_a_1096_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1103_ = v_a_1096_;
v_isShared_1104_ = v_isSharedCheck_1114_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_snd_1101_);
lean_inc(v_fst_1100_);
lean_dec(v_a_1096_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1114_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v_h_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__2);
lean_inc(v_fst_1100_);
lean_inc(v_fst_1093_);
v_h_1106_ = l_Lean_mkApp6(v___x_1105_, v_arg_1075_, v_arg_1074_, v_fst_1093_, v_fst_1100_, v_snd_1094_, v_snd_1101_);
v___x_1107_ = l_Lean_mkIntAdd(v_fst_1093_, v_fst_1100_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 1, v_h_1106_);
lean_ctor_set(v___x_1103_, 0, v___x_1107_);
v___x_1109_ = v___x_1103_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_h_1106_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1109_);
v___x_1111_ = v___x_1098_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
else
{
lean_dec(v_snd_1094_);
lean_dec(v_fst_1093_);
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
return v___x_1095_;
}
}
else
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
return v___x_1091_;
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_e_964_);
v_a_1116_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1088_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1088_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
else
{
lean_object* v___x_1124_; 
lean_dec_ref(v___x_1077_);
v___x_1124_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_1076_, v___y_972_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; uint8_t v___x_1126_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref_known(v___x_1124_, 1);
v___x_1126_ = lean_unbox(v_a_1125_);
lean_dec(v_a_1125_);
if (v___x_1126_ == 0)
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1127_; 
lean_dec_ref(v_e_964_);
lean_inc_ref(v_arg_1075_);
v___x_1127_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(v_arg_1075_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v_fst_1129_; lean_object* v_snd_1130_; lean_object* v___x_1131_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v_fst_1129_ = lean_ctor_get(v_a_1128_, 0);
lean_inc(v_fst_1129_);
v_snd_1130_ = lean_ctor_get(v_a_1128_, 1);
lean_inc(v_snd_1130_);
lean_dec(v_a_1128_);
lean_inc_ref(v_arg_1074_);
v___x_1131_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(v_arg_1074_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1151_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1151_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1151_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v_fst_1136_; lean_object* v_snd_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1150_; 
v_fst_1136_ = lean_ctor_get(v_a_1132_, 0);
v_snd_1137_ = lean_ctor_get(v_a_1132_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_a_1132_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1139_ = v_a_1132_;
v_isShared_1140_ = v_isSharedCheck_1150_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_snd_1137_);
lean_inc(v_fst_1136_);
lean_dec(v_a_1132_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1150_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v_h_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1141_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__2);
lean_inc(v_fst_1136_);
lean_inc(v_fst_1129_);
v_h_1142_ = l_Lean_mkApp6(v___x_1141_, v_arg_1075_, v_arg_1074_, v_fst_1129_, v_fst_1136_, v_snd_1130_, v_snd_1137_);
v___x_1143_ = l_Lean_mkIntMul(v_fst_1129_, v_fst_1136_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v_h_1142_);
lean_ctor_set(v___x_1139_, 0, v___x_1143_);
v___x_1145_ = v___x_1139_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_h_1142_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1145_);
v___x_1147_ = v___x_1134_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
else
{
lean_dec(v_snd_1130_);
lean_dec(v_fst_1129_);
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
return v___x_1131_;
}
}
else
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
return v___x_1127_;
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_e_964_);
v_a_1152_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1124_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1124_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
else
{
lean_object* v___x_1160_; 
lean_dec_ref(v___x_1077_);
v___x_1160_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_1076_, v___y_972_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; uint8_t v___x_1162_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
v___x_1162_ = lean_unbox(v_a_1161_);
lean_dec(v_a_1161_);
if (v___x_1162_ == 0)
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1163_; 
lean_inc_ref(v_arg_1075_);
v___x_1163_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(v_arg_1075_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v_fst_1165_; lean_object* v_snd_1166_; lean_object* v___x_1167_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v_fst_1165_ = lean_ctor_get(v_a_1164_, 0);
lean_inc(v_fst_1165_);
v_snd_1166_ = lean_ctor_get(v_a_1164_, 1);
lean_inc(v_snd_1166_);
lean_dec(v_a_1164_);
lean_inc_ref(v_arg_1074_);
v___x_1167_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(v_arg_1074_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v_fst_1169_; lean_object* v_snd_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1197_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v_fst_1169_ = lean_ctor_get(v_a_1168_, 0);
v_snd_1170_ = lean_ctor_get(v_a_1168_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_a_1168_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1172_ = v_a_1168_;
v_isShared_1173_ = v_isSharedCheck_1197_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_snd_1170_);
lean_inc(v_fst_1169_);
lean_dec(v_a_1168_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1197_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v_h_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__2);
lean_inc(v_fst_1169_);
lean_inc(v_fst_1165_);
v_h_1175_ = l_Lean_mkApp6(v___x_1174_, v_arg_1075_, v_arg_1074_, v_fst_1165_, v_fst_1169_, v_snd_1166_, v_snd_1170_);
v___x_1176_ = l_Lean_mkIntDiv(v_fst_1165_, v_fst_1169_);
v___x_1177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natImage(v_e_964_, v___x_1176_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec_ref(v_e_964_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1188_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1188_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1188_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_h_1175_);
lean_ctor_set(v___x_1172_, 0, v_a_1178_);
v___x_1183_ = v___x_1172_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1178_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_h_1175_);
v___x_1183_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1185_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1183_);
v___x_1185_ = v___x_1180_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_h_1175_);
lean_del_object(v___x_1172_);
v_a_1189_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1177_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1177_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
else
{
lean_dec(v_snd_1166_);
lean_dec(v_fst_1165_);
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_e_964_);
return v___x_1167_;
}
}
else
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_e_964_);
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_e_964_);
v_a_1198_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1160_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1160_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
else
{
lean_object* v___x_1206_; 
lean_dec_ref(v___x_1077_);
v___x_1206_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_1076_, v___y_972_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; uint8_t v___x_1208_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1208_ = lean_unbox(v_a_1207_);
lean_dec(v_a_1207_);
if (v___x_1208_ == 0)
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1209_; 
lean_inc_ref(v_arg_1075_);
v___x_1209_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(v_arg_1075_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v_fst_1211_; lean_object* v_snd_1212_; lean_object* v___x_1213_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v_fst_1211_ = lean_ctor_get(v_a_1210_, 0);
lean_inc(v_fst_1211_);
v_snd_1212_ = lean_ctor_get(v_a_1210_, 1);
lean_inc(v_snd_1212_);
lean_dec(v_a_1210_);
lean_inc_ref(v_arg_1074_);
v___x_1213_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(v_arg_1074_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v_fst_1215_; lean_object* v_snd_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1243_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v_fst_1215_ = lean_ctor_get(v_a_1214_, 0);
v_snd_1216_ = lean_ctor_get(v_a_1214_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_a_1214_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1218_ = v_a_1214_;
v_isShared_1219_ = v_isSharedCheck_1243_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_snd_1216_);
lean_inc(v_fst_1215_);
lean_dec(v_a_1214_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1243_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v_h_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1220_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__2);
lean_inc(v_fst_1215_);
lean_inc(v_fst_1211_);
v_h_1221_ = l_Lean_mkApp6(v___x_1220_, v_arg_1075_, v_arg_1074_, v_fst_1211_, v_fst_1215_, v_snd_1212_, v_snd_1216_);
v___x_1222_ = l_Lean_mkIntMod(v_fst_1211_, v_fst_1215_);
v___x_1223_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natImage(v_e_964_, v___x_1222_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec_ref(v_e_964_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1234_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1234_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1234_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v_h_1221_);
lean_ctor_set(v___x_1218_, 0, v_a_1224_);
v___x_1229_ = v___x_1218_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1224_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_h_1221_);
v___x_1229_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1229_);
v___x_1231_ = v___x_1226_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v_h_1221_);
lean_del_object(v___x_1218_);
v_a_1235_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1223_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1223_);
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
}
else
{
lean_dec(v_snd_1212_);
lean_dec(v_fst_1211_);
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_e_964_);
return v___x_1213_;
}
}
else
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_e_964_);
return v___x_1209_;
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_e_964_);
v_a_1244_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1206_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1206_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
else
{
lean_object* v___x_1252_; 
lean_dec_ref(v___x_1077_);
v___x_1252_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_1076_, v___y_972_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; uint8_t v___x_1254_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v___x_1254_ = lean_unbox(v_a_1253_);
lean_dec(v_a_1253_);
if (v___x_1254_ == 0)
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1255_; 
lean_inc_ref(v_arg_1075_);
v___x_1255_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(v_arg_1075_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v_fst_1257_; lean_object* v_snd_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1285_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v_fst_1257_ = lean_ctor_get(v_a_1256_, 0);
v_snd_1258_ = lean_ctor_get(v_a_1256_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_a_1256_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1260_ = v_a_1256_;
v_isShared_1261_ = v_isSharedCheck_1285_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_snd_1258_);
lean_inc(v_fst_1257_);
lean_dec(v_a_1256_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1285_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v_h_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__2);
lean_inc(v_fst_1257_);
lean_inc_ref(v_arg_1074_);
v_h_1263_ = l_Lean_mkApp4(v___x_1262_, v_arg_1075_, v_arg_1074_, v_fst_1257_, v_snd_1258_);
v___x_1264_ = l_Lean_mkIntPowNat(v_fst_1257_, v_arg_1074_);
v___x_1265_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natImage(v_e_964_, v___x_1264_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec_ref(v_e_964_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1276_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1276_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1276_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 1, v_h_1263_);
lean_ctor_set(v___x_1260_, 0, v_a_1266_);
v___x_1271_ = v___x_1260_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1266_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_h_1263_);
v___x_1271_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1273_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1271_);
v___x_1273_ = v___x_1268_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_h_1263_);
lean_del_object(v___x_1260_);
v_a_1277_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1265_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1265_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_e_964_);
return v___x_1255_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1074_);
lean_dec_ref(v_e_964_);
v_a_1286_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1252_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1252_);
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
}
}
}
else
{
lean_object* v___x_1294_; 
lean_dec_ref(v___x_1066_);
lean_dec_ref(v___x_1064_);
lean_dec_ref(v___x_1062_);
lean_dec_ref(v___x_1060_);
v___x_1294_ = l_Lean_Meta_getNatValue_x3f(v_e_964_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1308_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1308_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1308_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
if (lean_obj_tag(v_a_1295_) == 1)
{
lean_object* v_val_1299_; lean_object* v___x_1300_; lean_object* v_h_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v_val_1299_ = lean_ctor_get(v_a_1295_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v_a_1295_, 1);
v___x_1300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__4);
v_h_1301_ = l_Lean_Expr_app___override(v___x_1300_, v_e_964_);
v___x_1302_ = lean_nat_to_int(v_val_1299_);
v___x_1303_ = l_Lean_mkIntLit(v___x_1302_);
lean_dec(v___x_1302_);
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v_h_1301_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1304_);
v___x_1306_ = v___x_1297_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
else
{
lean_del_object(v___x_1297_);
lean_dec(v_a_1295_);
v_e_1036_ = v_e_964_;
v___y_1037_ = v___y_965_;
v___y_1038_ = v___y_966_;
v___y_1039_ = v___y_967_;
v___y_1040_ = v___y_968_;
v___y_1041_ = v___y_969_;
v___y_1042_ = v___y_970_;
v___y_1043_ = v___y_971_;
v___y_1044_ = v___y_972_;
v___y_1045_ = v___y_973_;
v___y_1046_ = v___y_974_;
goto v___jp_1035_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref(v_e_964_);
v_a_1309_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1294_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1294_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
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
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v_e_964_);
v_a_1317_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1058_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1058_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
v___jp_976_:
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = l_Lean_Expr_cleanupAnnotations(v_t_978_);
lean_dec_ref(v_t_978_);
v___x_990_ = l_Lean_Expr_isApp(v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
lean_dec_ref(v___x_989_);
v___x_991_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v___y_977_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = l_Lean_Expr_appFnCleanup___redArg(v___x_989_);
v___x_993_ = l_Lean_Expr_isApp(v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
lean_dec_ref(v___x_992_);
lean_dec_ref(v___x_989_);
v___x_994_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v___y_977_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
return v___x_994_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_995_ = l_Lean_Expr_appFnCleanup___redArg(v___x_992_);
v___x_996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__2));
v___x_997_ = l_Lean_Expr_isConstOf(v___x_995_, v___x_996_);
lean_dec_ref(v___x_995_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; 
lean_dec_ref(v___x_992_);
lean_dec_ref(v___x_989_);
v___x_998_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v___y_977_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
return v___x_998_;
}
else
{
lean_object* v_arg_999_; lean_object* v_arg_1000_; lean_object* v___x_1001_; 
v_arg_999_ = lean_ctor_get(v___x_989_, 1);
lean_inc_ref(v_arg_999_);
lean_dec_ref(v___x_989_);
v_arg_1000_ = lean_ctor_get(v___x_992_, 1);
lean_inc_ref(v_arg_1000_);
lean_dec_ref(v___x_992_);
v___x_1001_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_979_, v___y_987_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v_natToIntMap_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v_natToIntMap_1003_ = lean_ctor_get(v_a_1002_, 3);
lean_inc_ref(v_natToIntMap_1003_);
lean_dec(v_a_1002_);
v___x_1004_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0___redArg(v_natToIntMap_1003_, v___y_977_);
lean_dec_ref(v_natToIntMap_1003_);
v___x_1005_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v___y_977_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_1005_) == 0)
{
if (v___x_1004_ == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___closed__5);
v___x_1008_ = l_Lean_mkAppB(v___x_1007_, v_arg_1000_, v_arg_999_);
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = l_Lean_Meta_Grind_pushNewFact(v___x_1008_, v___x_1009_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v___x_1010_, 0);
lean_dec(v_unused_1018_);
v___x_1012_ = v___x_1010_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_dec(v___x_1010_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v_a_1006_);
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1006_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_a_1006_);
v_a_1019_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1010_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1010_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
else
{
lean_dec_ref(v_arg_1000_);
lean_dec_ref(v_arg_999_);
return v___x_1005_;
}
}
else
{
lean_dec_ref(v_arg_1000_);
lean_dec_ref(v_arg_999_);
return v___x_1005_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec_ref(v_arg_1000_);
lean_dec_ref(v_arg_999_);
lean_dec_ref(v___y_977_);
v_a_1027_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1001_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1001_);
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
}
}
}
v___jp_1035_:
{
uint8_t v___x_1047_; 
v___x_1047_ = l_Lean_Expr_hasExprMVar(v_e_1036_);
if (v___x_1047_ == 0)
{
lean_inc_ref(v_e_1036_);
v___y_977_ = v_e_1036_;
v_t_978_ = v_e_1036_;
v___y_979_ = v___y_1037_;
v___y_980_ = v___y_1038_;
v___y_981_ = v___y_1039_;
v___y_982_ = v___y_1040_;
v___y_983_ = v___y_1041_;
v___y_984_ = v___y_1042_;
v___y_985_ = v___y_1043_;
v___y_986_ = v___y_1044_;
v___y_987_ = v___y_1045_;
v___y_988_ = v___y_1046_;
goto v___jp_976_;
}
else
{
lean_object* v___x_1048_; 
lean_inc_ref(v_e_1036_);
v___x_1048_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1036_, v___y_1044_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___y_977_ = v_e_1036_;
v_t_978_ = v_a_1049_;
v___y_979_ = v___y_1037_;
v___y_980_ = v___y_1038_;
v___y_981_ = v___y_1039_;
v___y_982_ = v___y_1040_;
v___y_983_ = v___y_1041_;
v___y_984_ = v___y_1042_;
v___y_985_ = v___y_1043_;
v___y_986_ = v___y_1044_;
v___y_987_ = v___y_1045_;
v___y_988_ = v___y_1046_;
goto v___jp_976_;
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v_e_1036_);
v_a_1050_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1048_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1048_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1___boxed(lean_object* v_e_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(v_e_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec(v___y_1326_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1(v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v_fst_1352_; lean_object* v_snd_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1377_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v_fst_1352_ = lean_ctor_get(v_a_1351_, 0);
v_snd_1353_ = lean_ctor_get(v_a_1351_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_a_1351_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1355_ = v_a_1351_;
v_isShared_1356_ = v_isSharedCheck_1377_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_snd_1353_);
lean_inc(v_fst_1352_);
lean_dec(v_a_1351_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1377_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Meta_Sym_shareCommon(v_fst_1352_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1368_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1368_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1368_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v_a_1358_);
v___x_1363_ = v___x_1355_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1358_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_snd_1353_);
v___x_1363_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1363_);
v___x_1365_ = v___x_1360_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_del_object(v___x_1355_);
lean_dec(v_snd_1353_);
v_a_1369_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1357_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1357_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
else
{
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt___boxed(lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec(v_a_1379_);
return v_res_1390_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0(lean_object* v_00_u03b2_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
uint8_t v___x_1394_; 
v___x_1394_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0___redArg(v_x_1392_, v_x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0___boxed(lean_object* v_00_u03b2_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_){
_start:
{
uint8_t v_res_1398_; lean_object* v_r_1399_; 
v_res_1398_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0(v_00_u03b2_1395_, v_x_1396_, v_x_1397_);
lean_dec_ref(v_x_1397_);
lean_dec_ref(v_x_1396_);
v_r_1399_ = lean_box(v_res_1398_);
return v_r_1399_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__1_spec__2(lean_object* v_a_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_nat_to_int(v_a_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0(lean_object* v_00_u03b2_1402_, lean_object* v_x_1403_, size_t v_x_1404_, lean_object* v_x_1405_){
_start:
{
uint8_t v___x_1406_; 
v___x_1406_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0___redArg(v_x_1403_, v_x_1404_, v_x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
size_t v_x_30545__boxed_1411_; uint8_t v_res_1412_; lean_object* v_r_1413_; 
v_x_30545__boxed_1411_ = lean_unbox_usize(v_x_1409_);
lean_dec(v_x_1409_);
v_res_1412_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0(v_00_u03b2_1407_, v_x_1408_, v_x_30545__boxed_1411_, v_x_1410_);
lean_dec_ref(v_x_1410_);
lean_dec_ref(v_x_1408_);
v_r_1413_ = lean_box(v_res_1412_);
return v_r_1413_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1414_, lean_object* v_keys_1415_, lean_object* v_vals_1416_, lean_object* v_heq_1417_, lean_object* v_i_1418_, lean_object* v_k_1419_){
_start:
{
uint8_t v___x_1420_; 
v___x_1420_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0_spec__1___redArg(v_keys_1415_, v_i_1418_, v_k_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1421_, lean_object* v_keys_1422_, lean_object* v_vals_1423_, lean_object* v_heq_1424_, lean_object* v_i_1425_, lean_object* v_k_1426_){
_start:
{
uint8_t v_res_1427_; lean_object* v_r_1428_; 
v_res_1427_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0_spec__0_spec__1(v_00_u03b2_1421_, v_keys_1422_, v_vals_1423_, v_heq_1424_, v_i_1425_, v_k_1426_);
lean_dec_ref(v_k_1426_);
lean_dec_ref(v_vals_1423_);
lean_dec_ref(v_keys_1422_);
v_r_1428_ = lean_box(v_res_1427_);
return v_r_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(lean_object* v_e_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_e_1436_; lean_object* v___x_1440_; 
lean_inc_ref(v_e_1429_);
v___x_1440_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1429_, v___y_1431_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = l_Lean_Expr_cleanupAnnotations(v_a_1441_);
lean_dec(v_a_1441_);
v___x_1443_ = l_Lean_Expr_isApp(v___x_1442_);
if (v___x_1443_ == 0)
{
lean_dec_ref(v___x_1442_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1442_);
v___x_1445_ = l_Lean_Expr_isApp(v___x_1444_);
if (v___x_1445_ == 0)
{
lean_dec_ref(v___x_1444_);
lean_dec_ref(v___x_1442_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1444_);
v___x_1447_ = l_Lean_Expr_isApp(v___x_1446_);
if (v___x_1447_ == 0)
{
lean_dec_ref(v___x_1446_);
lean_dec_ref(v___x_1444_);
lean_dec_ref(v___x_1442_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1448_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1446_);
v___x_1449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__2));
v___x_1450_ = l_Lean_Expr_isConstOf(v___x_1448_, v___x_1449_);
if (v___x_1450_ == 0)
{
uint8_t v___x_1451_; 
v___x_1451_ = l_Lean_Expr_isApp(v___x_1448_);
if (v___x_1451_ == 0)
{
lean_dec_ref(v___x_1448_);
lean_dec_ref(v___x_1446_);
lean_dec_ref(v___x_1444_);
lean_dec_ref(v___x_1442_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1448_);
lean_dec_ref(v___x_1448_);
v___x_1453_ = l_Lean_Expr_isApp(v___x_1452_);
if (v___x_1453_ == 0)
{
lean_dec_ref(v___x_1452_);
lean_dec_ref(v___x_1446_);
lean_dec_ref(v___x_1444_);
lean_dec_ref(v___x_1442_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1452_);
lean_dec_ref(v___x_1452_);
v___x_1455_ = l_Lean_Expr_isApp(v___x_1454_);
if (v___x_1455_ == 0)
{
lean_dec_ref(v___x_1454_);
lean_dec_ref(v___x_1446_);
lean_dec_ref(v___x_1444_);
lean_dec_ref(v___x_1442_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
else
{
lean_object* v_arg_1456_; lean_object* v_arg_1457_; lean_object* v_arg_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_arg_1456_ = lean_ctor_get(v___x_1442_, 1);
lean_inc_ref(v_arg_1456_);
lean_dec_ref(v___x_1442_);
v_arg_1457_ = lean_ctor_get(v___x_1444_, 1);
lean_inc_ref(v_arg_1457_);
lean_dec_ref(v___x_1444_);
v_arg_1458_ = lean_ctor_get(v___x_1446_, 1);
lean_inc_ref(v_arg_1458_);
lean_dec_ref(v___x_1446_);
v___x_1459_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1454_);
lean_dec_ref(v___x_1454_);
v___x_1460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__5));
v___x_1461_ = l_Lean_Expr_isConstOf(v___x_1459_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__8));
v___x_1463_ = l_Lean_Expr_isConstOf(v___x_1459_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__11));
v___x_1465_ = l_Lean_Expr_isConstOf(v___x_1459_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__14));
v___x_1467_ = l_Lean_Expr_isConstOf(v___x_1459_, v___x_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__17));
v___x_1469_ = l_Lean_Expr_isConstOf(v___x_1459_, v___x_1468_);
lean_dec_ref(v___x_1459_);
if (v___x_1469_ == 0)
{
lean_dec_ref(v_arg_1458_);
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_1458_, v___y_1431_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; uint8_t v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = lean_unbox(v_a_1471_);
lean_dec(v_a_1471_);
if (v___x_1472_ == 0)
{
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1473_; 
lean_dec_ref(v_e_1429_);
lean_inc_ref(v_arg_1457_);
v___x_1473_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(v_arg_1457_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v_fst_1475_; lean_object* v_snd_1476_; lean_object* v___x_1477_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v_fst_1475_ = lean_ctor_get(v_a_1474_, 0);
lean_inc(v_fst_1475_);
v_snd_1476_ = lean_ctor_get(v_a_1474_, 1);
lean_inc(v_snd_1476_);
lean_dec(v_a_1474_);
lean_inc_ref(v_arg_1456_);
v___x_1477_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(v_arg_1456_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1497_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1497_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1497_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v_fst_1482_; lean_object* v_snd_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1496_; 
v_fst_1482_ = lean_ctor_get(v_a_1478_, 0);
v_snd_1483_ = lean_ctor_get(v_a_1478_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_a_1478_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1485_ = v_a_1478_;
v_isShared_1486_ = v_isSharedCheck_1496_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_snd_1483_);
lean_inc(v_fst_1482_);
lean_dec(v_a_1478_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1496_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; lean_object* v_h_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__1___closed__2);
lean_inc(v_fst_1482_);
lean_inc(v_fst_1475_);
v_h_1488_ = l_Lean_mkApp6(v___x_1487_, v_arg_1457_, v_arg_1456_, v_fst_1475_, v_fst_1482_, v_snd_1476_, v_snd_1483_);
v___x_1489_ = l_Lean_mkIntAdd(v_fst_1475_, v_fst_1482_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v_h_1488_);
lean_ctor_set(v___x_1485_, 0, v___x_1489_);
v___x_1491_ = v___x_1485_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_h_1488_);
v___x_1491_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1491_);
v___x_1493_ = v___x_1480_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
else
{
lean_dec(v_snd_1476_);
lean_dec(v_fst_1475_);
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
return v___x_1477_;
}
}
else
{
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
return v___x_1473_;
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
lean_dec_ref(v_e_1429_);
v_a_1498_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1470_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1470_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
else
{
lean_object* v___x_1506_; 
lean_dec_ref(v___x_1459_);
v___x_1506_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_1458_, v___y_1431_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; uint8_t v___x_1508_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v___x_1508_ = lean_unbox(v_a_1507_);
lean_dec(v_a_1507_);
if (v___x_1508_ == 0)
{
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1509_; 
lean_dec_ref(v_e_1429_);
lean_inc_ref(v_arg_1457_);
v___x_1509_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(v_arg_1457_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v_fst_1511_; lean_object* v_snd_1512_; lean_object* v___x_1513_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v_fst_1511_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_fst_1511_);
v_snd_1512_ = lean_ctor_get(v_a_1510_, 1);
lean_inc(v_snd_1512_);
lean_dec(v_a_1510_);
lean_inc_ref(v_arg_1456_);
v___x_1513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(v_arg_1456_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1533_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1533_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1533_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v_fst_1518_; lean_object* v_snd_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1532_; 
v_fst_1518_ = lean_ctor_get(v_a_1514_, 0);
v_snd_1519_ = lean_ctor_get(v_a_1514_, 1);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_a_1514_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1521_ = v_a_1514_;
v_isShared_1522_ = v_isSharedCheck_1532_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_snd_1519_);
lean_inc(v_fst_1518_);
lean_dec(v_a_1514_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1532_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v_h_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__4___closed__2);
lean_inc(v_fst_1518_);
lean_inc(v_fst_1511_);
v_h_1524_ = l_Lean_mkApp6(v___x_1523_, v_arg_1457_, v_arg_1456_, v_fst_1511_, v_fst_1518_, v_snd_1512_, v_snd_1519_);
v___x_1525_ = l_Lean_mkIntMul(v_fst_1511_, v_fst_1518_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v_h_1524_);
lean_ctor_set(v___x_1521_, 0, v___x_1525_);
v___x_1527_ = v___x_1521_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_h_1524_);
v___x_1527_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1529_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1527_);
v___x_1529_ = v___x_1516_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
else
{
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
return v___x_1513_;
}
}
else
{
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
return v___x_1509_;
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
lean_dec_ref(v_e_1429_);
v_a_1534_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1506_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1506_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
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
else
{
lean_object* v___x_1542_; 
lean_dec_ref(v___x_1459_);
v___x_1542_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_1458_, v___y_1431_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; uint8_t v___x_1544_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1544_ = lean_unbox(v_a_1543_);
lean_dec(v_a_1543_);
if (v___x_1544_ == 0)
{
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1545_; 
lean_dec_ref(v_e_1429_);
lean_inc_ref(v_arg_1457_);
v___x_1545_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(v_arg_1457_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v_fst_1547_; lean_object* v_snd_1548_; lean_object* v___x_1549_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v_fst_1547_ = lean_ctor_get(v_a_1546_, 0);
lean_inc(v_fst_1547_);
v_snd_1548_ = lean_ctor_get(v_a_1546_, 1);
lean_inc(v_snd_1548_);
lean_dec(v_a_1546_);
lean_inc_ref(v_arg_1456_);
v___x_1549_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(v_arg_1456_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1569_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1569_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1569_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v_fst_1554_; lean_object* v_snd_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1568_; 
v_fst_1554_ = lean_ctor_get(v_a_1550_, 0);
v_snd_1555_ = lean_ctor_get(v_a_1550_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_a_1550_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1557_ = v_a_1550_;
v_isShared_1558_ = v_isSharedCheck_1568_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_snd_1555_);
lean_inc(v_fst_1554_);
lean_dec(v_a_1550_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1568_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v_h_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__6___closed__2);
lean_inc(v_fst_1554_);
lean_inc(v_fst_1547_);
v_h_1560_ = l_Lean_mkApp6(v___x_1559_, v_arg_1457_, v_arg_1456_, v_fst_1547_, v_fst_1554_, v_snd_1548_, v_snd_1555_);
v___x_1561_ = l_Lean_mkIntDiv(v_fst_1547_, v_fst_1554_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 1, v_h_1560_);
lean_ctor_set(v___x_1557_, 0, v___x_1561_);
v___x_1563_ = v___x_1557_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_h_1560_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1563_);
v___x_1565_ = v___x_1552_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
else
{
lean_dec(v_snd_1548_);
lean_dec(v_fst_1547_);
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
return v___x_1549_;
}
}
else
{
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
return v___x_1545_;
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
lean_dec_ref(v_e_1429_);
v_a_1570_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1542_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1542_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
else
{
lean_object* v___x_1578_; 
lean_dec_ref(v___x_1459_);
v___x_1578_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_1458_, v___y_1431_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; uint8_t v___x_1580_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1580_ = lean_unbox(v_a_1579_);
lean_dec(v_a_1579_);
if (v___x_1580_ == 0)
{
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1581_; 
lean_dec_ref(v_e_1429_);
lean_inc_ref(v_arg_1457_);
v___x_1581_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(v_arg_1457_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v_fst_1583_; lean_object* v_snd_1584_; lean_object* v___x_1585_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v_fst_1583_ = lean_ctor_get(v_a_1582_, 0);
lean_inc(v_fst_1583_);
v_snd_1584_ = lean_ctor_get(v_a_1582_, 1);
lean_inc(v_snd_1584_);
lean_dec(v_a_1582_);
lean_inc_ref(v_arg_1456_);
v___x_1585_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(v_arg_1456_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1605_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1605_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1605_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v_fst_1590_; lean_object* v_snd_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1604_; 
v_fst_1590_ = lean_ctor_get(v_a_1586_, 0);
v_snd_1591_ = lean_ctor_get(v_a_1586_, 1);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_a_1586_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1593_ = v_a_1586_;
v_isShared_1594_ = v_isSharedCheck_1604_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_snd_1591_);
lean_inc(v_fst_1590_);
lean_dec(v_a_1586_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1604_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v_h_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__11___closed__2);
lean_inc(v_fst_1590_);
lean_inc(v_fst_1583_);
v_h_1596_ = l_Lean_mkApp6(v___x_1595_, v_arg_1457_, v_arg_1456_, v_fst_1583_, v_fst_1590_, v_snd_1584_, v_snd_1591_);
v___x_1597_ = l_Lean_mkIntMod(v_fst_1583_, v_fst_1590_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v_h_1596_);
lean_ctor_set(v___x_1593_, 0, v___x_1597_);
v___x_1599_ = v___x_1593_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_h_1596_);
v___x_1599_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1601_; 
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1599_);
v___x_1601_ = v___x_1588_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
else
{
lean_dec(v_snd_1584_);
lean_dec(v_fst_1583_);
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
return v___x_1585_;
}
}
else
{
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
return v___x_1581_;
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
lean_dec_ref(v_e_1429_);
v_a_1606_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1578_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1578_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
else
{
lean_object* v___x_1614_; 
lean_dec_ref(v___x_1459_);
v___x_1614_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_1458_, v___y_1431_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; uint8_t v___x_1616_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1616_ = lean_unbox(v_a_1615_);
lean_dec(v_a_1615_);
if (v___x_1616_ == 0)
{
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1617_; 
lean_dec_ref(v_e_1429_);
lean_inc_ref(v_arg_1457_);
v___x_1617_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(v_arg_1457_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1637_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1637_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1637_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1636_; 
v_fst_1622_ = lean_ctor_get(v_a_1618_, 0);
v_snd_1623_ = lean_ctor_get(v_a_1618_, 1);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_a_1618_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1625_ = v_a_1618_;
v_isShared_1626_ = v_isSharedCheck_1636_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_snd_1623_);
lean_inc(v_fst_1622_);
lean_dec(v_a_1618_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1636_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v_h_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1627_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__13___closed__2);
lean_inc(v_fst_1622_);
lean_inc_ref(v_arg_1456_);
v_h_1628_ = l_Lean_mkApp4(v___x_1627_, v_arg_1457_, v_arg_1456_, v_fst_1622_, v_snd_1623_);
v___x_1629_ = l_Lean_mkIntPowNat(v_fst_1622_, v_arg_1456_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 1, v_h_1628_);
lean_ctor_set(v___x_1625_, 0, v___x_1629_);
v___x_1631_ = v___x_1625_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_h_1628_);
v___x_1631_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1633_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1631_);
v___x_1633_ = v___x_1620_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
return v___x_1617_;
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v_arg_1457_);
lean_dec_ref(v_arg_1456_);
lean_dec_ref(v_e_1429_);
v_a_1638_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1614_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1614_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
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
lean_object* v___x_1646_; 
lean_dec_ref(v___x_1448_);
lean_dec_ref(v___x_1446_);
lean_dec_ref(v___x_1444_);
lean_dec_ref(v___x_1442_);
v___x_1646_ = l_Lean_Meta_getNatValue_x3f(v_e_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1660_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1660_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1660_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
if (lean_obj_tag(v_a_1647_) == 1)
{
lean_object* v_val_1651_; lean_object* v___x_1652_; lean_object* v_h_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
v_val_1651_ = lean_ctor_get(v_a_1647_, 0);
lean_inc(v_val_1651_);
lean_dec_ref_known(v_a_1647_, 1);
v___x_1652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__0___closed__4);
v_h_1653_ = l_Lean_Expr_app___override(v___x_1652_, v_e_1429_);
v___x_1654_ = lean_nat_to_int(v_val_1651_);
v___x_1655_ = l_Lean_mkIntLit(v___x_1654_);
lean_dec(v___x_1654_);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v_h_1653_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1656_);
v___x_1658_ = v___x_1649_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
else
{
lean_del_object(v___x_1649_);
lean_dec(v_a_1647_);
v_e_1436_ = v_e_1429_;
goto v___jp_1435_;
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v_e_1429_);
v_a_1661_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1646_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1646_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
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
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec_ref(v_e_1429_);
v_a_1669_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1440_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1440_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
v___jp_1435_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = l_Lean_mkIntNatCast(v_e_1436_);
v___x_1438_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natCastRefl(v___x_1437_);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0___boxed(lean_object* v_e_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(v_e_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToIntExpr(lean_object* v_e_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___at___00Lean_Meta_Grind_Arith_Cutsat_natToIntExpr_spec__0(v_e_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1699_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_fst_1695_; lean_object* v___x_1697_; 
v_fst_1695_ = lean_ctor_get(v_a_1691_, 0);
lean_inc(v_fst_1695_);
lean_dec(v_a_1691_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v_fst_1695_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_fst_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
v_a_1700_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1690_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1690_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToIntExpr___boxed(lean_object* v_e_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Meta_Grind_Arith_Cutsat_natToIntExpr(v_e_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
return v_res_1714_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_unsigned_to_nat(1u);
v___x_1724_ = lean_nat_to_int(v___x_1723_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5);
v___x_1726_ = lean_int_neg(v___x_1725_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = lean_nat_to_int(v___x_1727_);
return v___x_1728_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object* v_e_1731_, lean_object* v_x_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = l_Lean_Expr_cleanupAnnotations(v_e_1731_);
v___x_1748_ = l_Lean_Expr_isApp(v___x_1747_);
if (v___x_1748_ == 0)
{
lean_dec_ref(v___x_1747_);
lean_dec(v_x_1732_);
goto v___jp_1744_;
}
else
{
lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1747_);
v___x_1750_ = l_Lean_Expr_isApp(v___x_1749_);
if (v___x_1750_ == 0)
{
lean_dec_ref(v___x_1749_);
lean_dec_ref(v___x_1747_);
lean_dec(v_x_1732_);
goto v___jp_1744_;
}
else
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1749_);
v___x_1752_ = l_Lean_Expr_isApp(v___x_1751_);
if (v___x_1752_ == 0)
{
lean_dec_ref(v___x_1751_);
lean_dec_ref(v___x_1749_);
lean_dec_ref(v___x_1747_);
lean_dec(v_x_1732_);
goto v___jp_1744_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1753_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1751_);
lean_dec_ref(v___x_1751_);
v___x_1754_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1755_ = l_Lean_Expr_isConstOf(v___x_1753_, v___x_1754_);
lean_dec_ref(v___x_1753_);
if (v___x_1755_ == 0)
{
lean_dec_ref(v___x_1749_);
lean_dec_ref(v___x_1747_);
lean_dec(v_x_1732_);
goto v___jp_1744_;
}
else
{
lean_object* v_arg_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v_arg_1756_ = lean_ctor_get(v___x_1749_, 1);
lean_inc_ref(v_arg_1756_);
lean_dec_ref(v___x_1749_);
v___x_1757_ = l_Lean_Expr_cleanupAnnotations(v_arg_1756_);
lean_dec_ref(v_arg_1756_);
v___x_1758_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4));
v___x_1759_ = l_Lean_Expr_isConstOf(v___x_1757_, v___x_1758_);
lean_dec_ref(v___x_1757_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec_ref(v___x_1747_);
lean_dec(v_x_1732_);
v___x_1760_ = lean_box(0);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
else
{
lean_object* v_arg_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_arg_1762_ = lean_ctor_get(v___x_1747_, 1);
lean_inc_ref(v_arg_1762_);
lean_dec_ref(v___x_1747_);
v___x_1763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__2));
v___x_1764_ = l_Lean_Expr_isAppOf(v_arg_1762_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1733_, v_a_1741_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1792_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1792_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1792_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_natDef_1770_; uint8_t v___x_1771_; 
v_natDef_1770_ = lean_ctor_get(v_a_1766_, 4);
lean_inc_ref(v_natDef_1770_);
lean_dec(v_a_1766_);
v___x_1771_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0___redArg(v_natDef_1770_, v_arg_1762_);
lean_dec_ref(v_natDef_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_del_object(v___x_1768_);
lean_inc_ref(v_arg_1762_);
v___x_1772_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_1762_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec_ref_known(v___x_1772_, 1);
v___x_1773_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6);
v___x_1774_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8);
v___x_1775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v_x_1732_);
lean_ctor_set(v___x_1775_, 2, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1776_, 0, v_arg_1762_);
v___x_1777_ = lean_box(0);
v___x_1778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1775_);
lean_ctor_set(v___x_1778_, 1, v___x_1776_);
lean_ctor_set(v___x_1778_, 2, v___x_1777_);
lean_inc(v_a_1742_);
lean_inc_ref(v_a_1741_);
lean_inc(v_a_1740_);
lean_inc_ref(v_a_1739_);
lean_inc(v_a_1738_);
lean_inc_ref(v_a_1737_);
lean_inc(v_a_1736_);
lean_inc_ref(v_a_1735_);
lean_inc(v_a_1734_);
lean_inc(v_a_1733_);
v___x_1779_ = lean_grind_cutsat_assert_le(v___x_1778_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
return v___x_1779_;
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref(v_arg_1762_);
lean_dec(v_x_1732_);
v_a_1780_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1772_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1772_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
lean_dec_ref(v_arg_1762_);
lean_dec(v_x_1732_);
v___x_1788_ = lean_box(0);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1788_);
v___x_1790_ = v___x_1768_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec_ref(v_arg_1762_);
lean_dec(v_x_1732_);
v_a_1793_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1765_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1765_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec_ref(v_arg_1762_);
lean_dec(v_x_1732_);
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
}
}
}
}
}
v___jp_1744_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_box(0);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___boxed(lean_object* v_e_1803_, lean_object* v_x_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_e_1803_, v_x_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_e_1803_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(lean_object* v_e_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1818_, v_a_1819_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1832_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1832_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1832_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_natToIntMap_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
v_natToIntMap_1826_ = lean_ctor_get(v_a_1822_, 3);
lean_inc_ref(v_natToIntMap_1826_);
lean_dec(v_a_1822_);
v___x_1827_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_natToInt_spec__0___redArg(v_natToIntMap_1826_, v_e_1817_);
lean_dec_ref(v_natToIntMap_1826_);
v___x_1828_ = lean_box(v___x_1827_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1828_);
v___x_1830_ = v___x_1824_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
v_a_1833_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1821_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1821_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg___boxed(lean_object* v_e_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(v_e_1841_, v_a_1842_, v_a_1843_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_e_1841_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(lean_object* v_e_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(v_e_1846_, v_a_1847_, v_a_1855_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___boxed(lean_object* v_e_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(v_e_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_e_1859_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(lean_object* v_e_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v___y_1883_; lean_object* v___x_1915_; 
lean_inc_ref(v_e_1872_);
v___x_1915_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1872_, v_a_1874_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v___x_1917_ = l_Lean_Expr_cleanupAnnotations(v_a_1916_);
lean_dec(v_a_1916_);
v___x_1918_ = l_Lean_Expr_isApp(v___x_1917_);
if (v___x_1918_ == 0)
{
lean_dec_ref(v___x_1917_);
v___y_1883_ = v_a_1874_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1917_);
v___x_1920_ = l_Lean_Expr_isApp(v___x_1919_);
if (v___x_1920_ == 0)
{
lean_dec_ref(v___x_1919_);
lean_dec_ref(v___x_1917_);
v___y_1883_ = v_a_1874_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1919_);
v___x_1922_ = l_Lean_Expr_isApp(v___x_1921_);
if (v___x_1922_ == 0)
{
lean_dec_ref(v___x_1921_);
lean_dec_ref(v___x_1919_);
lean_dec_ref(v___x_1917_);
v___y_1883_ = v_a_1874_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1923_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1921_);
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__2));
v___x_1925_ = l_Lean_Expr_isConstOf(v___x_1923_, v___x_1924_);
if (v___x_1925_ == 0)
{
uint8_t v___x_1926_; 
v___x_1926_ = l_Lean_Expr_isApp(v___x_1923_);
if (v___x_1926_ == 0)
{
lean_dec_ref(v___x_1923_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v___x_1919_);
lean_dec_ref(v___x_1917_);
v___y_1883_ = v_a_1874_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1923_);
lean_dec_ref(v___x_1923_);
v___x_1928_ = l_Lean_Expr_isApp(v___x_1927_);
if (v___x_1928_ == 0)
{
lean_dec_ref(v___x_1927_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v___x_1919_);
lean_dec_ref(v___x_1917_);
v___y_1883_ = v_a_1874_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1927_);
lean_dec_ref(v___x_1927_);
v___x_1930_ = l_Lean_Expr_isApp(v___x_1929_);
if (v___x_1930_ == 0)
{
lean_dec_ref(v___x_1929_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v___x_1919_);
lean_dec_ref(v___x_1917_);
v___y_1883_ = v_a_1874_;
goto v___jp_1882_;
}
else
{
lean_object* v_arg_1931_; lean_object* v_arg_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v_arg_1931_ = lean_ctor_get(v___x_1919_, 1);
lean_inc_ref(v_arg_1931_);
lean_dec_ref(v___x_1919_);
v_arg_1932_ = lean_ctor_get(v___x_1921_, 1);
lean_inc_ref(v_arg_1932_);
lean_dec_ref(v___x_1921_);
v___x_1933_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1929_);
lean_dec_ref(v___x_1929_);
v___x_1934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__5));
v___x_1935_ = l_Lean_Expr_isConstOf(v___x_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__8));
v___x_1937_ = l_Lean_Expr_isConstOf(v___x_1933_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_object* v_arg_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v_arg_1938_ = lean_ctor_get(v___x_1917_, 1);
lean_inc_ref(v_arg_1938_);
lean_dec_ref(v___x_1917_);
v___x_1939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__11));
v___x_1940_ = l_Lean_Expr_isConstOf(v___x_1933_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__14));
v___x_1942_ = l_Lean_Expr_isConstOf(v___x_1933_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__17));
v___x_1944_ = l_Lean_Expr_isConstOf(v___x_1933_, v___x_1943_);
lean_dec_ref(v___x_1933_);
if (v___x_1944_ == 0)
{
lean_dec_ref(v_arg_1938_);
lean_dec_ref(v_arg_1932_);
lean_dec_ref(v_arg_1931_);
v___y_1883_ = v_a_1874_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1945_; 
lean_dec_ref(v_e_1872_);
v___x_1945_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1932_, v_a_1874_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; uint8_t v___x_1947_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v___x_1947_ = lean_unbox(v_a_1946_);
if (v___x_1947_ == 0)
{
lean_dec_ref(v_arg_1938_);
lean_dec_ref(v_arg_1931_);
return v___x_1945_;
}
else
{
lean_object* v___x_1948_; 
lean_dec_ref_known(v___x_1945_, 1);
v___x_1948_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_1931_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; uint8_t v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v___x_1950_ = lean_unbox(v_a_1949_);
if (v___x_1950_ == 0)
{
lean_dec_ref(v_arg_1938_);
return v___x_1948_;
}
else
{
lean_dec_ref_known(v___x_1948_, 1);
v_e_1872_ = v_arg_1938_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1938_);
return v___x_1948_;
}
}
}
else
{
lean_dec_ref(v_arg_1938_);
lean_dec_ref(v_arg_1931_);
return v___x_1945_;
}
}
}
else
{
lean_object* v___x_1952_; 
lean_dec_ref(v___x_1933_);
lean_dec_ref(v_e_1872_);
v___x_1952_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1932_, v_a_1874_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; uint8_t v___x_1954_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
v___x_1954_ = lean_unbox(v_a_1953_);
if (v___x_1954_ == 0)
{
lean_dec_ref(v_arg_1938_);
lean_dec_ref(v_arg_1931_);
return v___x_1952_;
}
else
{
lean_object* v___x_1955_; 
lean_dec_ref_known(v___x_1952_, 1);
v___x_1955_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_1931_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; uint8_t v___x_1957_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v___x_1957_ = lean_unbox(v_a_1956_);
if (v___x_1957_ == 0)
{
lean_dec_ref(v_arg_1938_);
return v___x_1955_;
}
else
{
lean_dec_ref_known(v___x_1955_, 1);
v_e_1872_ = v_arg_1938_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1938_);
return v___x_1955_;
}
}
}
else
{
lean_dec_ref(v_arg_1938_);
lean_dec_ref(v_arg_1931_);
return v___x_1952_;
}
}
}
else
{
lean_object* v___x_1959_; 
lean_dec_ref(v___x_1933_);
lean_dec_ref(v_e_1872_);
v___x_1959_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_1932_, v_a_1874_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; uint8_t v___x_1961_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
v___x_1961_ = lean_unbox(v_a_1960_);
if (v___x_1961_ == 0)
{
lean_dec_ref(v_arg_1938_);
lean_dec_ref(v_arg_1931_);
return v___x_1959_;
}
else
{
lean_object* v___x_1962_; 
lean_dec_ref_known(v___x_1959_, 1);
v___x_1962_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_1931_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; uint8_t v___x_1964_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v___x_1964_ = lean_unbox(v_a_1963_);
if (v___x_1964_ == 0)
{
lean_dec_ref(v_arg_1938_);
return v___x_1962_;
}
else
{
lean_dec_ref_known(v___x_1962_, 1);
v_e_1872_ = v_arg_1938_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1938_);
return v___x_1962_;
}
}
}
else
{
lean_dec_ref(v_arg_1938_);
lean_dec_ref(v_arg_1931_);
return v___x_1959_;
}
}
}
else
{
lean_object* v___x_1966_; 
lean_dec_ref(v___x_1933_);
lean_dec_ref(v___x_1917_);
lean_dec_ref(v_e_1872_);
v___x_1966_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_1932_, v_a_1874_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; uint8_t v___x_1968_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v___x_1968_ = lean_unbox(v_a_1967_);
if (v___x_1968_ == 0)
{
lean_dec_ref(v_arg_1931_);
return v___x_1966_;
}
else
{
lean_dec_ref_known(v___x_1966_, 1);
v_e_1872_ = v_arg_1931_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1931_);
return v___x_1966_;
}
}
}
else
{
lean_object* v___x_1970_; 
lean_dec_ref(v___x_1933_);
lean_dec_ref(v___x_1917_);
lean_dec_ref(v_e_1872_);
v___x_1970_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_1932_, v_a_1874_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; uint8_t v___x_1972_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v___x_1972_ = lean_unbox(v_a_1971_);
if (v___x_1972_ == 0)
{
lean_dec_ref(v_arg_1931_);
return v___x_1970_;
}
else
{
lean_dec_ref_known(v___x_1970_, 1);
v_e_1872_ = v_arg_1931_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1931_);
return v___x_1970_;
}
}
}
}
}
}
else
{
lean_object* v___x_1974_; 
lean_dec_ref(v___x_1923_);
lean_dec_ref(v___x_1921_);
lean_dec_ref(v___x_1919_);
lean_dec_ref(v___x_1917_);
v___x_1974_ = l_Lean_Meta_getIntValue_x3f(v_e_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1991_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1991_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1991_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
if (lean_obj_tag(v_a_1975_) == 1)
{
lean_object* v_val_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
v_val_1979_ = lean_ctor_get(v_a_1975_, 0);
lean_inc(v_val_1979_);
lean_dec_ref_known(v_a_1975_, 1);
v___x_1980_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7);
v___x_1981_ = lean_int_dec_le(v___x_1980_, v_val_1979_);
lean_dec(v_val_1979_);
v___x_1982_ = lean_box(v___x_1981_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1982_);
v___x_1984_ = v___x_1977_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
else
{
uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
lean_dec(v_a_1975_);
v___x_1986_ = 0;
v___x_1987_ = lean_box(v___x_1986_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1987_);
v___x_1989_ = v___x_1977_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
v_a_1992_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1974_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1974_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
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
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec_ref(v_e_1872_);
v_a_2000_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1915_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1915_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
v___jp_1878_:
{
uint8_t v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = 0;
v___x_1880_ = lean_box(v___x_1879_);
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
return v___x_1881_;
}
v___jp_1882_:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1872_, v___y_1883_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1906_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1906_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1906_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = l_Lean_Expr_cleanupAnnotations(v_a_1885_);
lean_dec(v_a_1885_);
v___x_1890_ = l_Lean_Expr_isApp(v___x_1889_);
if (v___x_1890_ == 0)
{
lean_dec_ref(v___x_1889_);
lean_del_object(v___x_1887_);
goto v___jp_1878_;
}
else
{
lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1889_);
lean_dec_ref(v___x_1889_);
v___x_1892_ = l_Lean_Expr_isApp(v___x_1891_);
if (v___x_1892_ == 0)
{
lean_dec_ref(v___x_1891_);
lean_del_object(v___x_1887_);
goto v___jp_1878_;
}
else
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1891_);
v___x_1894_ = l_Lean_Expr_isApp(v___x_1893_);
if (v___x_1894_ == 0)
{
lean_dec_ref(v___x_1893_);
lean_dec_ref(v___x_1891_);
lean_del_object(v___x_1887_);
goto v___jp_1878_;
}
else
{
lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1895_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1893_);
lean_dec_ref(v___x_1893_);
v___x_1896_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1897_ = l_Lean_Expr_isConstOf(v___x_1895_, v___x_1896_);
lean_dec_ref(v___x_1895_);
if (v___x_1897_ == 0)
{
lean_dec_ref(v___x_1891_);
lean_del_object(v___x_1887_);
goto v___jp_1878_;
}
else
{
lean_object* v_arg_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
v_arg_1898_ = lean_ctor_get(v___x_1891_, 1);
lean_inc_ref(v_arg_1898_);
lean_dec_ref(v___x_1891_);
v___x_1899_ = l_Lean_Expr_cleanupAnnotations(v_arg_1898_);
lean_dec_ref(v_arg_1898_);
v___x_1900_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4));
v___x_1901_ = l_Lean_Expr_isConstOf(v___x_1899_, v___x_1900_);
lean_dec_ref(v___x_1899_);
v___x_1902_ = lean_box(v___x_1901_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1902_);
v___x_1904_ = v___x_1887_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1884_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1884_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg___boxed(lean_object* v_e_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_e_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(lean_object* v_msg_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___f_2022_; lean_object* v___x_2233__overap_2023_; lean_object* v___x_2024_; 
v___f_2022_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0));
v___x_2233__overap_2023_ = lean_panic_fn_borrowed(v___f_2022_, v_msg_2016_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2019_);
lean_inc(v___y_2018_);
lean_inc_ref(v___y_2017_);
v___x_2024_ = lean_apply_5(v___x_2233__overap_2023_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, lean_box(0));
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___boxed(lean_object* v_msg_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(v_msg_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
return v_res_2031_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2));
v___x_2036_ = lean_unsigned_to_nat(43u);
v___x_2037_ = lean_unsigned_to_nat(169u);
v___x_2038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1));
v___x_2039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0));
v___x_2040_ = l_mkPanicMessageWithDecl(v___x_2039_, v___x_2038_, v___x_2037_, v___x_2036_, v___x_2035_);
return v___x_2040_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = lean_box(0);
v___x_2048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6));
v___x_2049_ = l_Lean_mkConst(v___x_2048_, v___x_2047_);
return v___x_2049_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = lean_box(0);
v___x_2056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9));
v___x_2057_ = l_Lean_mkConst(v___x_2056_, v___x_2055_);
return v___x_2057_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2063_ = lean_box(0);
v___x_2064_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12));
v___x_2065_ = l_Lean_mkConst(v___x_2064_, v___x_2063_);
return v___x_2065_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = lean_box(0);
v___x_2072_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15));
v___x_2073_ = l_Lean_mkConst(v___x_2072_, v___x_2071_);
return v___x_2073_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_box(0);
v___x_2080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18));
v___x_2081_ = l_Lean_mkConst(v___x_2080_, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = lean_box(0);
v___x_2088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21));
v___x_2089_ = l_Lean_mkConst(v___x_2088_, v___x_2087_);
return v___x_2089_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = lean_box(0);
v___x_2096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24));
v___x_2097_ = l_Lean_mkConst(v___x_2096_, v___x_2095_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(lean_object* v_e_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___x_2137_; 
lean_inc_ref(v_e_2098_);
v___x_2137_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2098_, v_a_2100_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2236_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2236_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2236_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = l_Lean_Expr_cleanupAnnotations(v_a_2138_);
lean_dec(v_a_2138_);
v___x_2143_ = l_Lean_Expr_isApp(v___x_2142_);
if (v___x_2143_ == 0)
{
lean_dec_ref(v___x_2142_);
lean_del_object(v___x_2140_);
v___y_2112_ = v_a_2099_;
v___y_2113_ = v_a_2100_;
v___y_2114_ = v_a_2101_;
v___y_2115_ = v_a_2102_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2142_);
v___x_2145_ = l_Lean_Expr_isApp(v___x_2144_);
if (v___x_2145_ == 0)
{
lean_dec_ref(v___x_2144_);
lean_dec_ref(v___x_2142_);
lean_del_object(v___x_2140_);
v___y_2112_ = v_a_2099_;
v___y_2113_ = v_a_2100_;
v___y_2114_ = v_a_2101_;
v___y_2115_ = v_a_2102_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2144_);
v___x_2147_ = l_Lean_Expr_isApp(v___x_2146_);
if (v___x_2147_ == 0)
{
lean_dec_ref(v___x_2146_);
lean_dec_ref(v___x_2144_);
lean_dec_ref(v___x_2142_);
lean_del_object(v___x_2140_);
v___y_2112_ = v_a_2099_;
v___y_2113_ = v_a_2100_;
v___y_2114_ = v_a_2101_;
v___y_2115_ = v_a_2102_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2148_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2146_);
lean_dec_ref(v___x_2146_);
v___x_2149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__2));
v___x_2150_ = l_Lean_Expr_isConstOf(v___x_2148_, v___x_2149_);
if (v___x_2150_ == 0)
{
uint8_t v___x_2151_; 
lean_del_object(v___x_2140_);
v___x_2151_ = l_Lean_Expr_isApp(v___x_2148_);
if (v___x_2151_ == 0)
{
lean_dec_ref(v___x_2148_);
lean_dec_ref(v___x_2144_);
lean_dec_ref(v___x_2142_);
v___y_2112_ = v_a_2099_;
v___y_2113_ = v_a_2100_;
v___y_2114_ = v_a_2101_;
v___y_2115_ = v_a_2102_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2148_);
lean_dec_ref(v___x_2148_);
v___x_2153_ = l_Lean_Expr_isApp(v___x_2152_);
if (v___x_2153_ == 0)
{
lean_dec_ref(v___x_2152_);
lean_dec_ref(v___x_2144_);
lean_dec_ref(v___x_2142_);
v___y_2112_ = v_a_2099_;
v___y_2113_ = v_a_2100_;
v___y_2114_ = v_a_2101_;
v___y_2115_ = v_a_2102_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2152_);
lean_dec_ref(v___x_2152_);
v___x_2155_ = l_Lean_Expr_isApp(v___x_2154_);
if (v___x_2155_ == 0)
{
lean_dec_ref(v___x_2154_);
lean_dec_ref(v___x_2144_);
lean_dec_ref(v___x_2142_);
v___y_2112_ = v_a_2099_;
v___y_2113_ = v_a_2100_;
v___y_2114_ = v_a_2101_;
v___y_2115_ = v_a_2102_;
goto v___jp_2111_;
}
else
{
lean_object* v_arg_2156_; lean_object* v_arg_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v_arg_2156_ = lean_ctor_get(v___x_2142_, 1);
lean_inc_ref(v_arg_2156_);
lean_dec_ref(v___x_2142_);
v_arg_2157_ = lean_ctor_get(v___x_2144_, 1);
lean_inc_ref(v_arg_2157_);
lean_dec_ref(v___x_2144_);
v___x_2158_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2154_);
lean_dec_ref(v___x_2154_);
v___x_2159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__5));
v___x_2160_ = l_Lean_Expr_isConstOf(v___x_2158_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__8));
v___x_2162_ = l_Lean_Expr_isConstOf(v___x_2158_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__11));
v___x_2164_ = l_Lean_Expr_isConstOf(v___x_2158_, v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__14));
v___x_2166_ = l_Lean_Expr_isConstOf(v___x_2158_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__17));
v___x_2168_ = l_Lean_Expr_isConstOf(v___x_2158_, v___x_2167_);
lean_dec_ref(v___x_2158_);
if (v___x_2168_ == 0)
{
lean_dec_ref(v_arg_2157_);
lean_dec_ref(v_arg_2156_);
v___y_2112_ = v_a_2099_;
v___y_2113_ = v_a_2100_;
v___y_2114_ = v_a_2101_;
v___y_2115_ = v_a_2102_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2169_; 
lean_dec_ref(v_e_2098_);
lean_inc_ref(v_arg_2157_);
v___x_2169_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_2157_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
lean_inc_ref(v_arg_2156_);
v___x_2171_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_2156_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2181_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2181_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2181_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2176_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10);
v___x_2177_ = l_Lean_mkApp4(v___x_2176_, v_arg_2157_, v_arg_2156_, v_a_2170_, v_a_2172_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2177_);
v___x_2179_ = v___x_2174_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
else
{
lean_dec(v_a_2170_);
lean_dec_ref(v_arg_2157_);
lean_dec_ref(v_arg_2156_);
return v___x_2171_;
}
}
else
{
lean_dec_ref(v_arg_2157_);
lean_dec_ref(v_arg_2156_);
return v___x_2169_;
}
}
}
else
{
lean_object* v___x_2182_; 
lean_dec_ref(v___x_2158_);
lean_dec_ref(v_e_2098_);
lean_inc_ref(v_arg_2157_);
v___x_2182_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_2157_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
lean_inc_ref(v_arg_2156_);
v___x_2184_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_2156_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2194_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2194_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2194_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2189_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13);
v___x_2190_ = l_Lean_mkApp4(v___x_2189_, v_arg_2157_, v_arg_2156_, v_a_2183_, v_a_2185_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2190_);
v___x_2192_ = v___x_2187_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
else
{
lean_dec(v_a_2183_);
lean_dec_ref(v_arg_2157_);
lean_dec_ref(v_arg_2156_);
return v___x_2184_;
}
}
else
{
lean_dec_ref(v_arg_2157_);
lean_dec_ref(v_arg_2156_);
return v___x_2182_;
}
}
}
else
{
lean_object* v___x_2195_; 
lean_dec_ref(v___x_2158_);
lean_dec_ref(v_e_2098_);
lean_inc_ref(v_arg_2157_);
v___x_2195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_2157_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
lean_inc_ref(v_arg_2156_);
v___x_2197_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_2156_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2207_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2207_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2207_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2202_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16);
v___x_2203_ = l_Lean_mkApp4(v___x_2202_, v_arg_2157_, v_arg_2156_, v_a_2196_, v_a_2198_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2203_);
v___x_2205_ = v___x_2200_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
else
{
lean_dec(v_a_2196_);
lean_dec_ref(v_arg_2157_);
lean_dec_ref(v_arg_2156_);
return v___x_2197_;
}
}
else
{
lean_dec_ref(v_arg_2157_);
lean_dec_ref(v_arg_2156_);
return v___x_2195_;
}
}
}
else
{
lean_object* v___x_2208_; 
lean_dec_ref(v___x_2158_);
lean_dec_ref(v_e_2098_);
lean_inc_ref(v_arg_2157_);
v___x_2208_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_2157_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2218_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2211_ = v___x_2208_;
v_isShared_2212_ = v_isSharedCheck_2218_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2218_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2213_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19);
v___x_2214_ = l_Lean_mkApp3(v___x_2213_, v_arg_2157_, v_arg_2156_, v_a_2209_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2214_);
v___x_2216_ = v___x_2211_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
else
{
lean_dec_ref(v_arg_2157_);
lean_dec_ref(v_arg_2156_);
return v___x_2208_;
}
}
}
else
{
lean_object* v___x_2219_; 
lean_dec_ref(v___x_2158_);
lean_dec_ref(v_e_2098_);
lean_inc_ref(v_arg_2157_);
v___x_2219_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_2157_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2229_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2229_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2229_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2224_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22);
v___x_2225_ = l_Lean_mkApp3(v___x_2224_, v_arg_2157_, v_arg_2156_, v_a_2220_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2225_);
v___x_2227_ = v___x_2222_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
else
{
lean_dec_ref(v_arg_2157_);
lean_dec_ref(v_arg_2156_);
return v___x_2219_;
}
}
}
}
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
lean_dec_ref(v___x_2148_);
lean_dec_ref(v___x_2144_);
lean_dec_ref(v___x_2142_);
v___x_2230_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25);
v___x_2231_ = l_Lean_eagerReflBoolTrue;
v___x_2232_ = l_Lean_mkAppB(v___x_2230_, v_e_2098_, v___x_2231_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2232_);
v___x_2234_ = v___x_2140_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
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
}
}
}
else
{
lean_dec_ref(v_e_2098_);
return v___x_2137_;
}
v___jp_2104_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3);
v___x_2110_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(v___x_2109_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
return v___x_2110_;
}
v___jp_2111_:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2098_, v___y_2113_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2136_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2136_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2136_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = l_Lean_Expr_cleanupAnnotations(v_a_2117_);
lean_dec(v_a_2117_);
v___x_2122_ = l_Lean_Expr_isApp(v___x_2121_);
if (v___x_2122_ == 0)
{
lean_dec_ref(v___x_2121_);
lean_del_object(v___x_2119_);
v___y_2105_ = v___y_2112_;
v___y_2106_ = v___y_2113_;
v___y_2107_ = v___y_2114_;
v___y_2108_ = v___y_2115_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2121_);
v___x_2124_ = l_Lean_Expr_isApp(v___x_2123_);
if (v___x_2124_ == 0)
{
lean_dec_ref(v___x_2123_);
lean_dec_ref(v___x_2121_);
lean_del_object(v___x_2119_);
v___y_2105_ = v___y_2112_;
v___y_2106_ = v___y_2113_;
v___y_2107_ = v___y_2114_;
v___y_2108_ = v___y_2115_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2123_);
lean_dec_ref(v___x_2123_);
v___x_2126_ = l_Lean_Expr_isApp(v___x_2125_);
if (v___x_2126_ == 0)
{
lean_dec_ref(v___x_2125_);
lean_dec_ref(v___x_2121_);
lean_del_object(v___x_2119_);
v___y_2105_ = v___y_2112_;
v___y_2106_ = v___y_2113_;
v___y_2107_ = v___y_2114_;
v___y_2108_ = v___y_2115_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2127_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2125_);
lean_dec_ref(v___x_2125_);
v___x_2128_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_2129_ = l_Lean_Expr_isConstOf(v___x_2127_, v___x_2128_);
lean_dec_ref(v___x_2127_);
if (v___x_2129_ == 0)
{
lean_dec_ref(v___x_2121_);
lean_del_object(v___x_2119_);
v___y_2105_ = v___y_2112_;
v___y_2106_ = v___y_2113_;
v___y_2107_ = v___y_2114_;
v___y_2108_ = v___y_2115_;
goto v___jp_2104_;
}
else
{
lean_object* v_arg_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2134_; 
v_arg_2130_ = lean_ctor_get(v___x_2121_, 1);
lean_inc_ref(v_arg_2130_);
lean_dec_ref(v___x_2121_);
v___x_2131_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7);
v___x_2132_ = l_Lean_Expr_app___override(v___x_2131_, v_arg_2130_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2132_);
v___x_2134_ = v___x_2119_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
}
}
else
{
return v___x_2116_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___boxed(lean_object* v_e_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_e_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(lean_object* v_e_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___x_2250_; 
lean_inc_ref(v_e_2244_);
v___x_2250_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_e_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2278_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2278_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2278_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
uint8_t v___x_2255_; 
v___x_2255_ = lean_unbox(v_a_2251_);
lean_dec(v_a_2251_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
lean_dec_ref(v_e_2244_);
v___x_2256_ = lean_box(0);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2256_);
v___x_2258_ = v___x_2253_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
else
{
lean_object* v___x_2260_; 
lean_del_object(v___x_2253_);
v___x_2260_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_e_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2269_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2263_ = v___x_2260_;
v_isShared_2264_ = v_isSharedCheck_2269_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2269_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_a_2261_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2265_);
v___x_2267_ = v___x_2263_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
v_a_2270_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2260_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2260_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
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
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec_ref(v_e_2244_);
v_a_2279_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2250_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2250_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg___boxed(lean_object* v_e_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(v_e_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f(lean_object* v_e_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(v_e_2294_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___boxed(lean_object* v_e_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f(v_e_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec(v_a_2308_);
return v_res_2319_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = lean_box(0);
v___x_2326_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1));
v___x_2327_ = l_Lean_mkConst(v___x_2326_, v___x_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(lean_object* v_e_2328_, lean_object* v_x_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2341_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_2342_ = l_Lean_Expr_isAppOf(v_e_2328_, v___x_2341_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToIntAux___redArg___lam__12___closed__2));
v___x_2344_ = l_Lean_Expr_isAppOf(v_e_2328_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_inc_ref(v_e_2328_);
v___x_2345_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(v_e_2328_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2370_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2370_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2370_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
if (lean_obj_tag(v_a_2346_) == 1)
{
lean_object* v_val_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2365_; 
lean_del_object(v___x_2348_);
v_val_2350_ = lean_ctor_get(v_a_2346_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_a_2346_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2352_ = v_a_2346_;
v_isShared_2353_ = v_isSharedCheck_2365_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_val_2350_);
lean_dec(v_a_2346_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2365_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2354_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2);
v___x_2355_ = l_Lean_mkAppB(v___x_2354_, v_e_2328_, v_val_2350_);
v___x_2356_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6);
v___x_2357_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8);
v___x_2358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v_x_2329_);
lean_ctor_set(v___x_2358_, 2, v___x_2357_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set_tag(v___x_2352_, 6);
lean_ctor_set(v___x_2352_, 0, v___x_2355_);
v___x_2360_ = v___x_2352_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2355_);
v___x_2360_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2361_ = lean_box(0);
v___x_2362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2358_);
lean_ctor_set(v___x_2362_, 1, v___x_2360_);
lean_ctor_set(v___x_2362_, 2, v___x_2361_);
lean_inc(v_a_2339_);
lean_inc_ref(v_a_2338_);
lean_inc(v_a_2337_);
lean_inc_ref(v_a_2336_);
lean_inc(v_a_2335_);
lean_inc_ref(v_a_2334_);
lean_inc(v_a_2333_);
lean_inc_ref(v_a_2332_);
lean_inc(v_a_2331_);
lean_inc(v_a_2330_);
v___x_2363_ = lean_grind_cutsat_assert_le(v___x_2362_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
return v___x_2363_;
}
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
lean_dec(v_a_2346_);
lean_dec(v_x_2329_);
lean_dec_ref(v_e_2328_);
v___x_2366_ = lean_box(0);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2366_);
v___x_2368_ = v___x_2348_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_dec(v_x_2329_);
lean_dec_ref(v_e_2328_);
v_a_2371_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2345_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2345_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
lean_dec(v_x_2329_);
lean_dec_ref(v_e_2328_);
v___x_2379_ = lean_box(0);
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
return v___x_2380_;
}
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec(v_x_2329_);
lean_dec_ref(v_e_2328_);
v___x_2381_ = lean_box(0);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___boxed(lean_object* v_e_2383_, lean_object* v_x_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_e_2383_, v_x_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec(v_a_2385_);
return v_res_2396_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
}
#ifdef __cplusplus
}
#endif
