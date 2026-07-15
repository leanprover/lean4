// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Init.Data.Int.OfNat import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt import Lean.Meta.NatInstTesters
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_mkIntNatCast(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntDiv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntMod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntPowNat(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6;
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
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__1_value),LEAN_SCALAR_PTR_LITERAL(165, 91, 87, 132, 175, 103, 206, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__6_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__7_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__9_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__10_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__12_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__15_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__16_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__18_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__19_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__23_value),LEAN_SCALAR_PTR_LITERAL(34, 126, 174, 185, 27, 56, 123, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mul_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__26_value),LEAN_SCALAR_PTR_LITERAL(246, 119, 195, 92, 68, 86, 209, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "div_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__29_value),LEAN_SCALAR_PTR_LITERAL(34, 168, 146, 132, 240, 126, 147, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mod_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__32_value),LEAN_SCALAR_PTR_LITERAL(88, 250, 102, 19, 8, 50, 252, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "pow_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__35_value),LEAN_SCALAR_PTR_LITERAL(252, 58, 93, 228, 192, 253, 115, 4)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "natCast_ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__38_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__38_value),LEAN_SCALAR_PTR_LITERAL(238, 161, 137, 195, 161, 239, 200, 79)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "finVal"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__43_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__43_value),LEAN_SCALAR_PTR_LITERAL(253, 227, 103, 7, 1, 145, 189, 213)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "isLt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__46_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__46_value),LEAN_SCALAR_PTR_LITERAL(222, 150, 50, 101, 25, 222, 136, 68)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_ks_5_; lean_object* v_vs_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_32_; 
v_ks_5_ = lean_ctor_get(v_x_1_, 0);
v_vs_6_ = lean_ctor_get(v_x_1_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_32_ == 0)
{
v___x_8_ = v_x_1_;
v_isShared_9_ = v_isSharedCheck_32_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_vs_6_);
lean_inc(v_ks_5_);
lean_dec(v_x_1_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_32_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = lean_array_get_size(v_ks_5_);
v___x_11_ = lean_nat_dec_lt(v_x_2_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_15_; 
lean_dec(v_x_2_);
v___x_12_ = lean_array_push(v_ks_5_, v_x_3_);
v___x_13_ = lean_array_push(v_vs_6_, v_x_4_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___x_13_);
lean_ctor_set(v___x_8_, 0, v___x_12_);
v___x_15_ = v___x_8_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v___x_12_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v___x_13_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
else
{
lean_object* v_k_x27_17_; size_t v___x_18_; size_t v___x_19_; uint8_t v___x_20_; 
v_k_x27_17_ = lean_array_fget_borrowed(v_ks_5_, v_x_2_);
v___x_18_ = lean_ptr_addr(v_x_3_);
v___x_19_ = lean_ptr_addr(v_k_x27_17_);
v___x_20_ = lean_usize_dec_eq(v___x_18_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_22_; 
if (v_isShared_9_ == 0)
{
v___x_22_ = v___x_8_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_ks_5_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v_vs_6_);
v___x_22_ = v_reuseFailAlloc_26_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_add(v_x_2_, v___x_23_);
lean_dec(v_x_2_);
v_x_1_ = v___x_22_;
v_x_2_ = v___x_24_;
goto _start;
}
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_30_; 
v___x_27_ = lean_array_fset(v_ks_5_, v_x_2_, v_x_3_);
v___x_28_ = lean_array_fset(v_vs_6_, v_x_2_, v_x_4_);
lean_dec(v_x_2_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___x_28_);
lean_ctor_set(v___x_8_, 0, v___x_27_);
v___x_30_ = v___x_8_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(lean_object* v_n_33_, lean_object* v_k_34_, lean_object* v_v_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(v_n_33_, v___x_36_, v_k_34_, v_v_35_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(lean_object* v_x_39_, size_t v_x_40_, size_t v_x_41_, lean_object* v_x_42_, lean_object* v_x_43_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v_es_44_; size_t v___x_45_; size_t v___x_46_; lean_object* v_j_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v_es_44_ = lean_ctor_get(v_x_39_, 0);
v___x_45_ = ((size_t)31ULL);
v___x_46_ = lean_usize_land(v_x_40_, v___x_45_);
v_j_47_ = lean_usize_to_nat(v___x_46_);
v___x_48_ = lean_array_get_size(v_es_44_);
v___x_49_ = lean_nat_dec_lt(v_j_47_, v___x_48_);
if (v___x_49_ == 0)
{
lean_dec(v_j_47_);
lean_dec(v_x_43_);
lean_dec_ref(v_x_42_);
return v_x_39_;
}
else
{
lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_90_; 
lean_inc_ref(v_es_44_);
v_isSharedCheck_90_ = !lean_is_exclusive(v_x_39_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v_x_39_, 0);
lean_dec(v_unused_91_);
v___x_51_ = v_x_39_;
v_isShared_52_ = v_isSharedCheck_90_;
goto v_resetjp_50_;
}
else
{
lean_dec(v_x_39_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_90_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v_v_53_; lean_object* v___x_54_; lean_object* v_xs_x27_55_; lean_object* v___y_57_; 
v_v_53_ = lean_array_fget(v_es_44_, v_j_47_);
v___x_54_ = lean_box(0);
v_xs_x27_55_ = lean_array_fset(v_es_44_, v_j_47_, v___x_54_);
switch(lean_obj_tag(v_v_53_))
{
case 0:
{
lean_object* v_key_62_; lean_object* v_val_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_75_; 
v_key_62_ = lean_ctor_get(v_v_53_, 0);
v_val_63_ = lean_ctor_get(v_v_53_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v_v_53_);
if (v_isSharedCheck_75_ == 0)
{
v___x_65_ = v_v_53_;
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_val_63_);
lean_inc(v_key_62_);
lean_dec(v_v_53_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
size_t v___x_67_; size_t v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_ptr_addr(v_x_42_);
v___x_68_ = lean_ptr_addr(v_key_62_);
v___x_69_ = lean_usize_dec_eq(v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_del_object(v___x_65_);
v___x_70_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_62_, v_val_63_, v_x_42_, v_x_43_);
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
v___y_57_ = v___x_71_;
goto v___jp_56_;
}
else
{
lean_object* v___x_73_; 
lean_dec(v_val_63_);
lean_dec(v_key_62_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v_x_43_);
lean_ctor_set(v___x_65_, 0, v_x_42_);
v___x_73_ = v___x_65_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_x_42_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_x_43_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
v___y_57_ = v___x_73_;
goto v___jp_56_;
}
}
}
}
case 1:
{
lean_object* v_node_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_88_; 
v_node_76_ = lean_ctor_get(v_v_53_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v_v_53_);
if (v_isSharedCheck_88_ == 0)
{
v___x_78_ = v_v_53_;
v_isShared_79_ = v_isSharedCheck_88_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_node_76_);
lean_dec(v_v_53_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_88_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
size_t v___x_80_; size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_80_ = ((size_t)5ULL);
v___x_81_ = lean_usize_shift_right(v_x_40_, v___x_80_);
v___x_82_ = ((size_t)1ULL);
v___x_83_ = lean_usize_add(v_x_41_, v___x_82_);
v___x_84_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_node_76_, v___x_81_, v___x_83_, v_x_42_, v_x_43_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___x_84_);
v___x_86_ = v___x_78_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
v___y_57_ = v___x_86_;
goto v___jp_56_;
}
}
}
default: 
{
lean_object* v___x_89_; 
v___x_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_89_, 0, v_x_42_);
lean_ctor_set(v___x_89_, 1, v_x_43_);
v___y_57_ = v___x_89_;
goto v___jp_56_;
}
}
v___jp_56_:
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = lean_array_fset(v_xs_x27_55_, v_j_47_, v___y_57_);
lean_dec(v_j_47_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_58_);
v___x_60_ = v___x_51_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
}
else
{
lean_object* v_ks_92_; lean_object* v_vs_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_113_; 
v_ks_92_ = lean_ctor_get(v_x_39_, 0);
v_vs_93_ = lean_ctor_get(v_x_39_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_x_39_);
if (v_isSharedCheck_113_ == 0)
{
v___x_95_ = v_x_39_;
v_isShared_96_ = v_isSharedCheck_113_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_vs_93_);
lean_inc(v_ks_92_);
lean_dec(v_x_39_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_113_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_ks_92_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_vs_93_);
v___x_98_ = v_reuseFailAlloc_112_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v_newNode_99_; uint8_t v___y_101_; size_t v___x_107_; uint8_t v___x_108_; 
v_newNode_99_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(v___x_98_, v_x_42_, v_x_43_);
v___x_107_ = ((size_t)7ULL);
v___x_108_ = lean_usize_dec_le(v___x_107_, v_x_41_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_109_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_99_);
v___x_110_ = lean_unsigned_to_nat(4u);
v___x_111_ = lean_nat_dec_lt(v___x_109_, v___x_110_);
lean_dec(v___x_109_);
v___y_101_ = v___x_111_;
goto v___jp_100_;
}
else
{
v___y_101_ = v___x_108_;
goto v___jp_100_;
}
v___jp_100_:
{
if (v___y_101_ == 0)
{
lean_object* v_ks_102_; lean_object* v_vs_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_ks_102_ = lean_ctor_get(v_newNode_99_, 0);
lean_inc_ref(v_ks_102_);
v_vs_103_ = lean_ctor_get(v_newNode_99_, 1);
lean_inc_ref(v_vs_103_);
lean_dec_ref(v_newNode_99_);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0);
v___x_106_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_x_41_, v_ks_102_, v_vs_103_, v___x_104_, v___x_105_);
lean_dec_ref(v_vs_103_);
lean_dec_ref(v_ks_102_);
return v___x_106_;
}
else
{
return v_newNode_99_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(size_t v_depth_114_, lean_object* v_keys_115_, lean_object* v_vals_116_, lean_object* v_i_117_, lean_object* v_entries_118_){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_array_get_size(v_keys_115_);
v___x_120_ = lean_nat_dec_lt(v_i_117_, v___x_119_);
if (v___x_120_ == 0)
{
lean_dec(v_i_117_);
return v_entries_118_;
}
else
{
lean_object* v_k_121_; lean_object* v_v_122_; size_t v___x_123_; size_t v___x_124_; size_t v___x_125_; uint64_t v___x_126_; size_t v_h_127_; size_t v___x_128_; lean_object* v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v___x_132_; size_t v_h_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_k_121_ = lean_array_fget_borrowed(v_keys_115_, v_i_117_);
v_v_122_ = lean_array_fget_borrowed(v_vals_116_, v_i_117_);
v___x_123_ = lean_ptr_addr(v_k_121_);
v___x_124_ = ((size_t)3ULL);
v___x_125_ = lean_usize_shift_right(v___x_123_, v___x_124_);
v___x_126_ = lean_usize_to_uint64(v___x_125_);
v_h_127_ = lean_uint64_to_usize(v___x_126_);
v___x_128_ = ((size_t)5ULL);
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_sub(v_depth_114_, v___x_130_);
v___x_132_ = lean_usize_mul(v___x_128_, v___x_131_);
v_h_133_ = lean_usize_shift_right(v_h_127_, v___x_132_);
v___x_134_ = lean_nat_add(v_i_117_, v___x_129_);
lean_dec(v_i_117_);
lean_inc(v_v_122_);
lean_inc(v_k_121_);
v___x_135_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_entries_118_, v_h_133_, v_depth_114_, v_k_121_, v_v_122_);
v_i_117_ = v___x_134_;
v_entries_118_ = v___x_135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_137_, lean_object* v_keys_138_, lean_object* v_vals_139_, lean_object* v_i_140_, lean_object* v_entries_141_){
_start:
{
size_t v_depth_boxed_142_; lean_object* v_res_143_; 
v_depth_boxed_142_ = lean_unbox_usize(v_depth_137_);
lean_dec(v_depth_137_);
v_res_143_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_depth_boxed_142_, v_keys_138_, v_vals_139_, v_i_140_, v_entries_141_);
lean_dec_ref(v_vals_139_);
lean_dec_ref(v_keys_138_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___boxed(lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
size_t v_x_6000__boxed_149_; size_t v_x_6001__boxed_150_; lean_object* v_res_151_; 
v_x_6000__boxed_149_ = lean_unbox_usize(v_x_145_);
lean_dec(v_x_145_);
v_x_6001__boxed_150_ = lean_unbox_usize(v_x_146_);
lean_dec(v_x_146_);
v_res_151_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_144_, v_x_6000__boxed_149_, v_x_6001__boxed_150_, v_x_147_, v_x_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; uint64_t v___x_158_; size_t v___x_159_; size_t v___x_160_; lean_object* v___x_161_; 
v___x_155_ = lean_ptr_addr(v_x_153_);
v___x_156_ = ((size_t)3ULL);
v___x_157_ = lean_usize_shift_right(v___x_155_, v___x_156_);
v___x_158_ = lean_usize_to_uint64(v___x_157_);
v___x_159_ = lean_uint64_to_usize(v___x_158_);
v___x_160_ = ((size_t)1ULL);
v___x_161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_152_, v___x_159_, v___x_160_, v_x_153_, v_x_154_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___lam__0(lean_object* v_e_162_, lean_object* v___x_163_, lean_object* v_s_164_){
_start:
{
lean_object* v_vars_165_; lean_object* v_varMap_166_; lean_object* v_vars_x27_167_; lean_object* v_varMap_x27_168_; lean_object* v_natToIntMap_169_; lean_object* v_natDef_170_; lean_object* v_dvds_171_; lean_object* v_lowers_172_; lean_object* v_uppers_173_; lean_object* v_diseqs_174_; lean_object* v_elimEqs_175_; lean_object* v_elimStack_176_; lean_object* v_occurs_177_; lean_object* v_assignment_178_; lean_object* v_nextCnstrId_179_; uint8_t v_caseSplits_180_; lean_object* v_conflict_x3f_181_; lean_object* v_diseqSplits_182_; lean_object* v_divMod_183_; lean_object* v_toIntIds_184_; lean_object* v_toIntInfos_185_; lean_object* v_toIntTermMap_186_; lean_object* v_toIntVarMap_187_; uint8_t v_usedCommRing_188_; lean_object* v_nonlinearOccs_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_197_; 
v_vars_165_ = lean_ctor_get(v_s_164_, 0);
v_varMap_166_ = lean_ctor_get(v_s_164_, 1);
v_vars_x27_167_ = lean_ctor_get(v_s_164_, 2);
v_varMap_x27_168_ = lean_ctor_get(v_s_164_, 3);
v_natToIntMap_169_ = lean_ctor_get(v_s_164_, 4);
v_natDef_170_ = lean_ctor_get(v_s_164_, 5);
v_dvds_171_ = lean_ctor_get(v_s_164_, 6);
v_lowers_172_ = lean_ctor_get(v_s_164_, 7);
v_uppers_173_ = lean_ctor_get(v_s_164_, 8);
v_diseqs_174_ = lean_ctor_get(v_s_164_, 9);
v_elimEqs_175_ = lean_ctor_get(v_s_164_, 10);
v_elimStack_176_ = lean_ctor_get(v_s_164_, 11);
v_occurs_177_ = lean_ctor_get(v_s_164_, 12);
v_assignment_178_ = lean_ctor_get(v_s_164_, 13);
v_nextCnstrId_179_ = lean_ctor_get(v_s_164_, 14);
v_caseSplits_180_ = lean_ctor_get_uint8(v_s_164_, sizeof(void*)*23);
v_conflict_x3f_181_ = lean_ctor_get(v_s_164_, 15);
v_diseqSplits_182_ = lean_ctor_get(v_s_164_, 16);
v_divMod_183_ = lean_ctor_get(v_s_164_, 17);
v_toIntIds_184_ = lean_ctor_get(v_s_164_, 18);
v_toIntInfos_185_ = lean_ctor_get(v_s_164_, 19);
v_toIntTermMap_186_ = lean_ctor_get(v_s_164_, 20);
v_toIntVarMap_187_ = lean_ctor_get(v_s_164_, 21);
v_usedCommRing_188_ = lean_ctor_get_uint8(v_s_164_, sizeof(void*)*23 + 1);
v_nonlinearOccs_189_ = lean_ctor_get(v_s_164_, 22);
v_isSharedCheck_197_ = !lean_is_exclusive(v_s_164_);
if (v_isSharedCheck_197_ == 0)
{
v___x_191_ = v_s_164_;
v_isShared_192_ = v_isSharedCheck_197_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_nonlinearOccs_189_);
lean_inc(v_toIntVarMap_187_);
lean_inc(v_toIntTermMap_186_);
lean_inc(v_toIntInfos_185_);
lean_inc(v_toIntIds_184_);
lean_inc(v_divMod_183_);
lean_inc(v_diseqSplits_182_);
lean_inc(v_conflict_x3f_181_);
lean_inc(v_nextCnstrId_179_);
lean_inc(v_assignment_178_);
lean_inc(v_occurs_177_);
lean_inc(v_elimStack_176_);
lean_inc(v_elimEqs_175_);
lean_inc(v_diseqs_174_);
lean_inc(v_uppers_173_);
lean_inc(v_lowers_172_);
lean_inc(v_dvds_171_);
lean_inc(v_natDef_170_);
lean_inc(v_natToIntMap_169_);
lean_inc(v_varMap_x27_168_);
lean_inc(v_vars_x27_167_);
lean_inc(v_varMap_166_);
lean_inc(v_vars_165_);
lean_dec(v_s_164_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_197_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(v_natToIntMap_169_, v_e_162_, v___x_163_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 4, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_vars_165_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_varMap_166_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_vars_x27_167_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_varMap_x27_168_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_196_, 5, v_natDef_170_);
lean_ctor_set(v_reuseFailAlloc_196_, 6, v_dvds_171_);
lean_ctor_set(v_reuseFailAlloc_196_, 7, v_lowers_172_);
lean_ctor_set(v_reuseFailAlloc_196_, 8, v_uppers_173_);
lean_ctor_set(v_reuseFailAlloc_196_, 9, v_diseqs_174_);
lean_ctor_set(v_reuseFailAlloc_196_, 10, v_elimEqs_175_);
lean_ctor_set(v_reuseFailAlloc_196_, 11, v_elimStack_176_);
lean_ctor_set(v_reuseFailAlloc_196_, 12, v_occurs_177_);
lean_ctor_set(v_reuseFailAlloc_196_, 13, v_assignment_178_);
lean_ctor_set(v_reuseFailAlloc_196_, 14, v_nextCnstrId_179_);
lean_ctor_set(v_reuseFailAlloc_196_, 15, v_conflict_x3f_181_);
lean_ctor_set(v_reuseFailAlloc_196_, 16, v_diseqSplits_182_);
lean_ctor_set(v_reuseFailAlloc_196_, 17, v_divMod_183_);
lean_ctor_set(v_reuseFailAlloc_196_, 18, v_toIntIds_184_);
lean_ctor_set(v_reuseFailAlloc_196_, 19, v_toIntInfos_185_);
lean_ctor_set(v_reuseFailAlloc_196_, 20, v_toIntTermMap_186_);
lean_ctor_set(v_reuseFailAlloc_196_, 21, v_toIntVarMap_187_);
lean_ctor_set(v_reuseFailAlloc_196_, 22, v_nonlinearOccs_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_196_, sizeof(void*)*23, v_caseSplits_180_);
lean_ctor_set_uint8(v_reuseFailAlloc_196_, sizeof(void*)*23 + 1, v_usedCommRing_188_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_198_, lean_object* v_vals_199_, lean_object* v_i_200_, lean_object* v_k_201_){
_start:
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = lean_array_get_size(v_keys_198_);
v___x_203_ = lean_nat_dec_lt(v_i_200_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
lean_dec(v_i_200_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
lean_object* v_k_x27_205_; size_t v___x_206_; size_t v___x_207_; uint8_t v___x_208_; 
v_k_x27_205_ = lean_array_fget_borrowed(v_keys_198_, v_i_200_);
v___x_206_ = lean_ptr_addr(v_k_201_);
v___x_207_ = lean_ptr_addr(v_k_x27_205_);
v___x_208_ = lean_usize_dec_eq(v___x_206_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_add(v_i_200_, v___x_209_);
lean_dec(v_i_200_);
v_i_200_ = v___x_210_;
goto _start;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_array_fget_borrowed(v_vals_199_, v_i_200_);
lean_dec(v_i_200_);
lean_inc(v___x_212_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_214_, lean_object* v_vals_215_, lean_object* v_i_216_, lean_object* v_k_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_keys_214_, v_vals_215_, v_i_216_, v_k_217_);
lean_dec_ref(v_k_217_);
lean_dec_ref(v_vals_215_);
lean_dec_ref(v_keys_214_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(lean_object* v_x_219_, size_t v_x_220_, lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
lean_object* v_es_222_; lean_object* v___x_223_; size_t v___x_224_; size_t v___x_225_; lean_object* v_j_226_; lean_object* v___x_227_; 
v_es_222_ = lean_ctor_get(v_x_219_, 0);
v___x_223_ = lean_box(2);
v___x_224_ = ((size_t)31ULL);
v___x_225_ = lean_usize_land(v_x_220_, v___x_224_);
v_j_226_ = lean_usize_to_nat(v___x_225_);
v___x_227_ = lean_array_get_borrowed(v___x_223_, v_es_222_, v_j_226_);
lean_dec(v_j_226_);
switch(lean_obj_tag(v___x_227_))
{
case 0:
{
lean_object* v_key_228_; lean_object* v_val_229_; size_t v___x_230_; size_t v___x_231_; uint8_t v___x_232_; 
v_key_228_ = lean_ctor_get(v___x_227_, 0);
v_val_229_ = lean_ctor_get(v___x_227_, 1);
v___x_230_ = lean_ptr_addr(v_x_221_);
v___x_231_ = lean_ptr_addr(v_key_228_);
v___x_232_ = lean_usize_dec_eq(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_box(0);
return v___x_233_;
}
else
{
lean_object* v___x_234_; 
lean_inc(v_val_229_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v_val_229_);
return v___x_234_;
}
}
case 1:
{
lean_object* v_node_235_; size_t v___x_236_; size_t v___x_237_; 
v_node_235_ = lean_ctor_get(v___x_227_, 0);
v___x_236_ = ((size_t)5ULL);
v___x_237_ = lean_usize_shift_right(v_x_220_, v___x_236_);
v_x_219_ = v_node_235_;
v_x_220_ = v___x_237_;
goto _start;
}
default: 
{
lean_object* v___x_239_; 
v___x_239_ = lean_box(0);
return v___x_239_;
}
}
}
else
{
lean_object* v_ks_240_; lean_object* v_vs_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_ks_240_ = lean_ctor_get(v_x_219_, 0);
v_vs_241_ = lean_ctor_get(v_x_219_, 1);
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_ks_240_, v_vs_241_, v___x_242_, v_x_221_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
size_t v_x_6223__boxed_247_; lean_object* v_res_248_; 
v_x_6223__boxed_247_ = lean_unbox_usize(v_x_245_);
lean_dec(v_x_245_);
v_res_248_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_244_, v_x_6223__boxed_247_, v_x_246_);
lean_dec_ref(v_x_246_);
lean_dec_ref(v_x_244_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; uint64_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; 
v___x_251_ = lean_ptr_addr(v_x_250_);
v___x_252_ = ((size_t)3ULL);
v___x_253_ = lean_usize_shift_right(v___x_251_, v___x_252_);
v___x_254_ = lean_usize_to_uint64(v___x_253_);
v___x_255_ = lean_uint64_to_usize(v___x_254_);
v___x_256_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_249_, v___x_255_, v_x_250_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg___boxed(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_x_257_, v_x_258_);
lean_dec_ref(v_x_258_);
lean_dec_ref(v_x_257_);
return v_res_259_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = l_Lean_Level_ofNat(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_box(0);
v___x_268_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3);
v___x_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4);
v___x_271_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2));
v___x_272_ = l_Lean_mkConst(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = l_Lean_Int_mkType;
v___x_274_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5);
v___x_275_ = l_Lean_Expr_app___override(v___x_274_, v___x_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(lean_object* v_e_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_277_, v_a_285_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_341_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_341_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_341_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_341_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_natToIntMap_293_; lean_object* v___x_294_; 
v_natToIntMap_293_ = lean_ctor_get(v_a_289_, 4);
lean_inc_ref(v_natToIntMap_293_);
lean_dec(v_a_289_);
v___x_294_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_natToIntMap_293_, v_e_276_);
lean_dec_ref(v_natToIntMap_293_);
if (lean_obj_tag(v___x_294_) == 1)
{
lean_object* v_val_295_; lean_object* v___x_297_; 
lean_dec_ref(v_e_276_);
v_val_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_val_295_);
lean_dec_ref_known(v___x_294_, 1);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v_val_295_);
v___x_297_ = v___x_291_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_val_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v___x_294_);
lean_del_object(v___x_291_);
lean_inc_ref(v_e_276_);
v___x_299_ = l_Lean_mkIntNatCast(v_e_276_);
v___x_300_ = l_Lean_Meta_Sym_shareCommon(v___x_299_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___f_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc_n(v_a_301_, 2);
lean_dec_ref_known(v___x_300_, 1);
v___x_302_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6);
v___x_303_ = l_Lean_Expr_app___override(v___x_302_, v_a_301_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_a_301_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
lean_inc_ref(v___x_304_);
lean_inc_ref(v_e_276_);
v___f_305_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___lam__0), 3, 2);
lean_closure_set(v___f_305_, 0, v_e_276_);
lean_closure_set(v___f_305_, 1, v___x_304_);
v___x_306_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_307_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_306_, v___f_305_, v_a_277_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; 
lean_dec_ref_known(v___x_307_, 1);
v___x_308_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_306_, v_e_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; 
v_unused_316_ = lean_ctor_get(v___x_308_, 0);
lean_dec(v_unused_316_);
v___x_310_ = v___x_308_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_dec(v___x_308_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_304_);
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_304_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref_known(v___x_304_, 2);
v_a_317_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_308_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_308_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref_known(v___x_304_, 2);
lean_dec_ref(v_e_276_);
v_a_325_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_307_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_307_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec_ref(v_e_276_);
v_a_333_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_300_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_300_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec_ref(v_e_276_);
v_a_342_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_288_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_288_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___boxed(lean_object* v_e_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec(v_a_351_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0(lean_object* v_00_u03b2_363_, lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_x_364_, v_x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___boxed(lean_object* v_00_u03b2_367_, lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0(v_00_u03b2_367_, v_x_368_, v_x_369_);
lean_dec_ref(v_x_369_);
lean_dec_ref(v_x_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1(lean_object* v_00_u03b2_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(v_x_372_, v_x_373_, v_x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0(lean_object* v_00_u03b2_376_, lean_object* v_x_377_, size_t v_x_378_, lean_object* v_x_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_377_, v_x_378_, v_x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_381_, lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_x_384_){
_start:
{
size_t v_x_6483__boxed_385_; lean_object* v_res_386_; 
v_x_6483__boxed_385_ = lean_unbox_usize(v_x_383_);
lean_dec(v_x_383_);
v_res_386_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0(v_00_u03b2_381_, v_x_382_, v_x_6483__boxed_385_, v_x_384_);
lean_dec_ref(v_x_384_);
lean_dec_ref(v_x_382_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2(lean_object* v_00_u03b2_387_, lean_object* v_x_388_, size_t v_x_389_, size_t v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_388_, v_x_389_, v_x_390_, v_x_391_, v_x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_394_, lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
size_t v_x_6494__boxed_400_; size_t v_x_6495__boxed_401_; lean_object* v_res_402_; 
v_x_6494__boxed_400_ = lean_unbox_usize(v_x_396_);
lean_dec(v_x_396_);
v_x_6495__boxed_401_ = lean_unbox_usize(v_x_397_);
lean_dec(v_x_397_);
v_res_402_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2(v_00_u03b2_394_, v_x_395_, v_x_6494__boxed_400_, v_x_6495__boxed_401_, v_x_398_, v_x_399_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_403_, lean_object* v_keys_404_, lean_object* v_vals_405_, lean_object* v_heq_406_, lean_object* v_i_407_, lean_object* v_k_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_keys_404_, v_vals_405_, v_i_407_, v_k_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_410_, lean_object* v_keys_411_, lean_object* v_vals_412_, lean_object* v_heq_413_, lean_object* v_i_414_, lean_object* v_k_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1(v_00_u03b2_410_, v_keys_411_, v_vals_412_, v_heq_413_, v_i_414_, v_k_415_);
lean_dec_ref(v_k_415_);
lean_dec_ref(v_vals_412_);
lean_dec_ref(v_keys_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_417_, lean_object* v_n_418_, lean_object* v_k_419_, lean_object* v_v_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(v_n_418_, v_k_419_, v_v_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_422_, size_t v_depth_423_, lean_object* v_keys_424_, lean_object* v_vals_425_, lean_object* v_heq_426_, lean_object* v_i_427_, lean_object* v_entries_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_depth_423_, v_keys_424_, v_vals_425_, v_i_427_, v_entries_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_430_, lean_object* v_depth_431_, lean_object* v_keys_432_, lean_object* v_vals_433_, lean_object* v_heq_434_, lean_object* v_i_435_, lean_object* v_entries_436_){
_start:
{
size_t v_depth_boxed_437_; lean_object* v_res_438_; 
v_depth_boxed_437_ = lean_unbox_usize(v_depth_431_);
lean_dec(v_depth_431_);
v_res_438_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5(v_00_u03b2_430_, v_depth_boxed_437_, v_keys_432_, v_vals_433_, v_heq_434_, v_i_435_, v_entries_436_);
lean_dec_ref(v_vals_433_);
lean_dec_ref(v_keys_432_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_439_, lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(v_x_440_, v_x_441_, v_x_442_, v_x_443_);
return v___x_444_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_448_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4);
v___x_449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1));
v___x_450_ = l_Lean_mkConst(v___x_449_, v___x_448_);
return v___x_450_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = l_Lean_Int_mkType;
v___x_452_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2);
v___x_453_ = l_Lean_Expr_app___override(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte(void){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__0(lean_object* v_a_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = lean_nat_to_int(v_a_455_);
return v___x_456_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_457_, lean_object* v_i_458_, lean_object* v_k_459_){
_start:
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_array_get_size(v_keys_457_);
v___x_461_ = lean_nat_dec_lt(v_i_458_, v___x_460_);
if (v___x_461_ == 0)
{
lean_dec(v_i_458_);
return v___x_461_;
}
else
{
lean_object* v_k_x27_462_; size_t v___x_463_; size_t v___x_464_; uint8_t v___x_465_; 
v_k_x27_462_ = lean_array_fget_borrowed(v_keys_457_, v_i_458_);
v___x_463_ = lean_ptr_addr(v_k_459_);
v___x_464_ = lean_ptr_addr(v_k_x27_462_);
v___x_465_ = lean_usize_dec_eq(v___x_463_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_add(v_i_458_, v___x_466_);
lean_dec(v_i_458_);
v_i_458_ = v___x_467_;
goto _start;
}
else
{
lean_dec(v_i_458_);
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_469_, lean_object* v_i_470_, lean_object* v_k_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(v_keys_469_, v_i_470_, v_k_471_);
lean_dec_ref(v_k_471_);
lean_dec_ref(v_keys_469_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(lean_object* v_x_474_, size_t v_x_475_, lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_474_) == 0)
{
lean_object* v_es_477_; lean_object* v___x_478_; size_t v___x_479_; size_t v___x_480_; lean_object* v_j_481_; lean_object* v___x_482_; 
v_es_477_ = lean_ctor_get(v_x_474_, 0);
v___x_478_ = lean_box(2);
v___x_479_ = ((size_t)31ULL);
v___x_480_ = lean_usize_land(v_x_475_, v___x_479_);
v_j_481_ = lean_usize_to_nat(v___x_480_);
v___x_482_ = lean_array_get_borrowed(v___x_478_, v_es_477_, v_j_481_);
lean_dec(v_j_481_);
switch(lean_obj_tag(v___x_482_))
{
case 0:
{
lean_object* v_key_483_; size_t v___x_484_; size_t v___x_485_; uint8_t v___x_486_; 
v_key_483_ = lean_ctor_get(v___x_482_, 0);
v___x_484_ = lean_ptr_addr(v_x_476_);
v___x_485_ = lean_ptr_addr(v_key_483_);
v___x_486_ = lean_usize_dec_eq(v___x_484_, v___x_485_);
return v___x_486_;
}
case 1:
{
lean_object* v_node_487_; size_t v___x_488_; size_t v___x_489_; 
v_node_487_ = lean_ctor_get(v___x_482_, 0);
v___x_488_ = ((size_t)5ULL);
v___x_489_ = lean_usize_shift_right(v_x_475_, v___x_488_);
v_x_474_ = v_node_487_;
v_x_475_ = v___x_489_;
goto _start;
}
default: 
{
uint8_t v___x_491_; 
v___x_491_ = 0;
return v___x_491_;
}
}
}
else
{
lean_object* v_ks_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_ks_492_ = lean_ctor_get(v_x_474_, 0);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(v_ks_492_, v___x_493_, v_x_476_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg___boxed(lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
size_t v_x_62043__boxed_498_; uint8_t v_res_499_; lean_object* v_r_500_; 
v_x_62043__boxed_498_ = lean_unbox_usize(v_x_496_);
lean_dec(v_x_496_);
v_res_499_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(v_x_495_, v_x_62043__boxed_498_, v_x_497_);
lean_dec_ref(v_x_497_);
lean_dec_ref(v_x_495_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
size_t v___x_503_; size_t v___x_504_; size_t v___x_505_; uint64_t v___x_506_; size_t v___x_507_; uint8_t v___x_508_; 
v___x_503_ = lean_ptr_addr(v_x_502_);
v___x_504_ = ((size_t)3ULL);
v___x_505_ = lean_usize_shift_right(v___x_503_, v___x_504_);
v___x_506_ = lean_usize_to_uint64(v___x_505_);
v___x_507_ = lean_uint64_to_usize(v___x_506_);
v___x_508_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(v_x_501_, v___x_507_, v_x_502_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg___boxed(lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_x_509_, v_x_510_);
lean_dec_ref(v_x_510_);
lean_dec_ref(v_x_509_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_box(0);
v___x_556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24));
v___x_557_ = l_Lean_mkConst(v___x_556_, v___x_555_);
return v___x_557_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = lean_box(0);
v___x_564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27));
v___x_565_ = l_Lean_mkConst(v___x_564_, v___x_563_);
return v___x_565_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_box(0);
v___x_572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30));
v___x_573_ = l_Lean_mkConst(v___x_572_, v___x_571_);
return v___x_573_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_box(0);
v___x_580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33));
v___x_581_ = l_Lean_mkConst(v___x_580_, v___x_579_);
return v___x_581_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_box(0);
v___x_588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36));
v___x_589_ = l_Lean_mkConst(v___x_588_, v___x_587_);
return v___x_589_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_box(0);
v___x_596_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39));
v___x_597_ = l_Lean_mkConst(v___x_596_, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_box(0);
v___x_601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41));
v___x_602_ = l_Lean_mkConst(v___x_601_, v___x_600_);
return v___x_602_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_box(0);
v___x_609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44));
v___x_610_ = l_Lean_mkConst(v___x_609_, v___x_608_);
return v___x_610_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_box(0);
v___x_616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47));
v___x_617_ = l_Lean_mkConst(v___x_616_, v___x_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(lean_object* v_e_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_630_; 
lean_inc_ref(v_e_618_);
v___x_630_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_618_, v_a_626_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = l_Lean_Expr_cleanupAnnotations(v_a_631_);
v___x_633_ = l_Lean_Expr_isApp(v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
lean_dec_ref(v___x_632_);
v___x_634_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_634_;
}
else
{
lean_object* v_arg_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_arg_635_ = lean_ctor_get(v___x_632_, 1);
lean_inc_ref(v_arg_635_);
v___x_636_ = l_Lean_Expr_appFnCleanup___redArg(v___x_632_);
v___x_637_ = l_Lean_Expr_isApp(v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec_ref(v___x_636_);
lean_dec_ref(v_arg_635_);
v___x_638_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_638_;
}
else
{
lean_object* v_arg_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_arg_639_ = lean_ctor_get(v___x_636_, 1);
lean_inc_ref(v_arg_639_);
v___x_640_ = l_Lean_Expr_appFnCleanup___redArg(v___x_636_);
v___x_641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2));
v___x_642_ = l_Lean_Expr_isConstOf(v___x_640_, v___x_641_);
if (v___x_642_ == 0)
{
uint8_t v___x_643_; 
v___x_643_ = l_Lean_Expr_isApp(v___x_640_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_dec_ref(v___x_640_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
v___x_644_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_644_;
}
else
{
lean_object* v_arg_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_arg_645_ = lean_ctor_get(v___x_640_, 1);
lean_inc_ref(v_arg_645_);
v___x_646_ = l_Lean_Expr_appFnCleanup___redArg(v___x_640_);
v___x_647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_648_ = l_Lean_Expr_isConstOf(v___x_646_, v___x_647_);
if (v___x_648_ == 0)
{
uint8_t v___x_649_; 
v___x_649_ = l_Lean_Expr_isApp(v___x_646_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
lean_dec_ref(v___x_646_);
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
v___x_650_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_650_;
}
else
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = l_Lean_Expr_appFnCleanup___redArg(v___x_646_);
v___x_652_ = l_Lean_Expr_isApp(v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
lean_dec_ref(v___x_651_);
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
v___x_653_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = l_Lean_Expr_appFnCleanup___redArg(v___x_651_);
v___x_655_ = l_Lean_Expr_isApp(v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec_ref(v___x_654_);
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
v___x_656_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_654_);
v___x_658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8));
v___x_659_ = l_Lean_Expr_isConstOf(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11));
v___x_661_ = l_Lean_Expr_isConstOf(v___x_657_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14));
v___x_663_ = l_Lean_Expr_isConstOf(v___x_657_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17));
v___x_665_ = l_Lean_Expr_isConstOf(v___x_657_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20));
v___x_667_ = l_Lean_Expr_isConstOf(v___x_657_, v___x_666_);
lean_dec_ref(v___x_657_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
v___x_668_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_645_, v_a_626_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; uint8_t v___x_671_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = lean_unbox(v_a_670_);
lean_dec(v_a_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
v___x_672_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_672_;
}
else
{
lean_object* v___x_673_; 
lean_dec_ref(v_e_618_);
lean_inc_ref(v_arg_639_);
v___x_673_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_639_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v_fst_675_; lean_object* v_snd_676_; lean_object* v___x_677_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v_fst_675_ = lean_ctor_get(v_a_674_, 0);
lean_inc(v_fst_675_);
v_snd_676_ = lean_ctor_get(v_a_674_, 1);
lean_inc(v_snd_676_);
lean_dec(v_a_674_);
lean_inc_ref(v_arg_635_);
v___x_677_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_635_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_697_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_697_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_697_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_697_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_fst_682_; lean_object* v_snd_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_696_; 
v_fst_682_ = lean_ctor_get(v_a_678_, 0);
v_snd_683_ = lean_ctor_get(v_a_678_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_696_ == 0)
{
v___x_685_ = v_a_678_;
v_isShared_686_ = v_isSharedCheck_696_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_snd_683_);
lean_inc(v_fst_682_);
lean_dec(v_a_678_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_696_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_687_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25);
lean_inc(v_fst_682_);
lean_inc(v_fst_675_);
v___x_688_ = l_Lean_mkApp6(v___x_687_, v_arg_639_, v_arg_635_, v_fst_675_, v_fst_682_, v_snd_676_, v_snd_683_);
v___x_689_ = l_Lean_mkIntAdd(v_fst_675_, v_fst_682_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_688_);
lean_ctor_set(v___x_685_, 0, v___x_689_);
v___x_691_ = v___x_685_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_688_);
v___x_691_ = v_reuseFailAlloc_695_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_691_);
v___x_693_ = v___x_680_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
else
{
lean_dec(v_snd_676_);
lean_dec(v_fst_675_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
return v___x_677_;
}
}
else
{
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
return v___x_673_;
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_e_618_);
v_a_698_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_669_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_669_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
else
{
lean_object* v___x_706_; 
lean_dec_ref(v___x_657_);
v___x_706_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_645_, v_a_626_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; uint8_t v___x_708_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = lean_unbox(v_a_707_);
lean_dec(v_a_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
v___x_709_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; 
lean_dec_ref(v_e_618_);
lean_inc_ref(v_arg_639_);
v___x_710_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_639_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v_fst_712_; lean_object* v_snd_713_; lean_object* v___x_714_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v_fst_712_ = lean_ctor_get(v_a_711_, 0);
lean_inc(v_fst_712_);
v_snd_713_ = lean_ctor_get(v_a_711_, 1);
lean_inc(v_snd_713_);
lean_dec(v_a_711_);
lean_inc_ref(v_arg_635_);
v___x_714_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_635_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_734_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_734_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_734_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_734_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_fst_719_; lean_object* v_snd_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_733_; 
v_fst_719_ = lean_ctor_get(v_a_715_, 0);
v_snd_720_ = lean_ctor_get(v_a_715_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_a_715_);
if (v_isSharedCheck_733_ == 0)
{
v___x_722_ = v_a_715_;
v_isShared_723_ = v_isSharedCheck_733_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_snd_720_);
lean_inc(v_fst_719_);
lean_dec(v_a_715_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_733_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_724_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28);
lean_inc(v_fst_719_);
lean_inc(v_fst_712_);
v___x_725_ = l_Lean_mkApp6(v___x_724_, v_arg_639_, v_arg_635_, v_fst_712_, v_fst_719_, v_snd_713_, v_snd_720_);
v___x_726_ = l_Lean_mkIntMul(v_fst_712_, v_fst_719_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_725_);
lean_ctor_set(v___x_722_, 0, v___x_726_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_725_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_728_);
v___x_730_ = v___x_717_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
else
{
lean_dec(v_snd_713_);
lean_dec(v_fst_712_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
return v___x_714_;
}
}
else
{
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
return v___x_710_;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_e_618_);
v_a_735_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_706_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_706_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
else
{
lean_object* v___x_743_; 
lean_dec_ref(v___x_657_);
v___x_743_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_645_, v_a_626_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; uint8_t v___x_745_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = lean_unbox(v_a_744_);
lean_dec(v_a_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
v___x_746_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_746_;
}
else
{
lean_object* v___x_747_; 
lean_dec_ref(v_e_618_);
lean_inc_ref(v_arg_639_);
v___x_747_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_639_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v_fst_749_; lean_object* v_snd_750_; lean_object* v___x_751_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v_fst_749_ = lean_ctor_get(v_a_748_, 0);
lean_inc(v_fst_749_);
v_snd_750_ = lean_ctor_get(v_a_748_, 1);
lean_inc(v_snd_750_);
lean_dec(v_a_748_);
lean_inc_ref(v_arg_635_);
v___x_751_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_635_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_771_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_771_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_771_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_771_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_fst_756_; lean_object* v_snd_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_770_; 
v_fst_756_ = lean_ctor_get(v_a_752_, 0);
v_snd_757_ = lean_ctor_get(v_a_752_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_a_752_);
if (v_isSharedCheck_770_ == 0)
{
v___x_759_ = v_a_752_;
v_isShared_760_ = v_isSharedCheck_770_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_snd_757_);
lean_inc(v_fst_756_);
lean_dec(v_a_752_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_770_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_761_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31);
lean_inc(v_fst_756_);
lean_inc(v_fst_749_);
v___x_762_ = l_Lean_mkApp6(v___x_761_, v_arg_639_, v_arg_635_, v_fst_749_, v_fst_756_, v_snd_750_, v_snd_757_);
v___x_763_ = l_Lean_mkIntDiv(v_fst_749_, v_fst_756_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v___x_762_);
lean_ctor_set(v___x_759_, 0, v___x_763_);
v___x_765_ = v___x_759_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_762_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_765_);
v___x_767_ = v___x_754_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
else
{
lean_dec(v_snd_750_);
lean_dec(v_fst_749_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
return v___x_751_;
}
}
else
{
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
return v___x_747_;
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_e_618_);
v_a_772_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_743_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_743_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
else
{
lean_object* v___x_780_; 
lean_dec_ref(v___x_657_);
v___x_780_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_645_, v_a_626_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; uint8_t v___x_782_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
v___x_782_ = lean_unbox(v_a_781_);
lean_dec(v_a_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
v___x_783_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_783_;
}
else
{
lean_object* v___x_784_; 
lean_dec_ref(v_e_618_);
lean_inc_ref(v_arg_639_);
v___x_784_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_639_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v_fst_786_; lean_object* v_snd_787_; lean_object* v___x_788_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
v_fst_786_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_fst_786_);
v_snd_787_ = lean_ctor_get(v_a_785_, 1);
lean_inc(v_snd_787_);
lean_dec(v_a_785_);
lean_inc_ref(v_arg_635_);
v___x_788_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_635_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_808_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_808_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_808_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_808_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_fst_793_; lean_object* v_snd_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_807_; 
v_fst_793_ = lean_ctor_get(v_a_789_, 0);
v_snd_794_ = lean_ctor_get(v_a_789_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_a_789_);
if (v_isSharedCheck_807_ == 0)
{
v___x_796_ = v_a_789_;
v_isShared_797_ = v_isSharedCheck_807_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_snd_794_);
lean_inc(v_fst_793_);
lean_dec(v_a_789_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_807_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_798_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34);
lean_inc(v_fst_793_);
lean_inc(v_fst_786_);
v___x_799_ = l_Lean_mkApp6(v___x_798_, v_arg_639_, v_arg_635_, v_fst_786_, v_fst_793_, v_snd_787_, v_snd_794_);
v___x_800_ = l_Lean_mkIntMod(v_fst_786_, v_fst_793_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_799_);
lean_ctor_set(v___x_796_, 0, v___x_800_);
v___x_802_ = v___x_796_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_799_);
v___x_802_ = v_reuseFailAlloc_806_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_804_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_802_);
v___x_804_ = v___x_791_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
else
{
lean_dec(v_snd_787_);
lean_dec(v_fst_786_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
return v___x_788_;
}
}
else
{
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
return v___x_784_;
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_e_618_);
v_a_809_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_780_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_780_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
else
{
lean_object* v___x_817_; 
lean_dec_ref(v___x_657_);
v___x_817_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_645_, v_a_626_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; uint8_t v___x_819_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
v___x_819_ = lean_unbox(v_a_818_);
lean_dec(v_a_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
v___x_820_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; 
lean_dec_ref(v_e_618_);
lean_inc_ref(v_arg_639_);
v___x_821_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_639_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_841_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_841_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_841_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_841_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_fst_826_; lean_object* v_snd_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_840_; 
v_fst_826_ = lean_ctor_get(v_a_822_, 0);
v_snd_827_ = lean_ctor_get(v_a_822_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_a_822_);
if (v_isSharedCheck_840_ == 0)
{
v___x_829_ = v_a_822_;
v_isShared_830_ = v_isSharedCheck_840_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_snd_827_);
lean_inc(v_fst_826_);
lean_dec(v_a_822_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_840_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_831_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37);
lean_inc(v_fst_826_);
lean_inc_ref(v_arg_635_);
v___x_832_ = l_Lean_mkApp4(v___x_831_, v_arg_639_, v_arg_635_, v_fst_826_, v_snd_827_);
v___x_833_ = l_Lean_mkIntPowNat(v_fst_826_, v_arg_635_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v___x_832_);
lean_ctor_set(v___x_829_, 0, v___x_833_);
v___x_835_ = v___x_829_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_832_);
v___x_835_ = v_reuseFailAlloc_839_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_837_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_835_);
v___x_837_ = v___x_824_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
return v___x_821_;
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_e_618_);
v_a_842_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_817_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_817_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
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
lean_object* v___x_850_; 
lean_dec_ref(v___x_646_);
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
v___x_850_ = l_Lean_Meta_getNatValue_x3f(v_e_618_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_865_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_865_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_865_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_865_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
if (lean_obj_tag(v_a_851_) == 1)
{
lean_object* v_val_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v_val_855_ = lean_ctor_get(v_a_851_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v_a_851_, 1);
v___x_856_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40);
v___x_857_ = l_Lean_Expr_app___override(v___x_856_, v_e_618_);
v___x_858_ = lean_nat_to_int(v_val_855_);
v___x_859_ = l_Lean_mkIntLit(v___x_858_);
lean_dec(v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_857_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_860_);
v___x_862_ = v___x_853_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
else
{
lean_object* v___x_864_; 
lean_del_object(v___x_853_);
lean_dec(v_a_851_);
v___x_864_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_864_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v_e_618_);
v_a_866_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_850_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_850_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec_ref(v___x_640_);
v___x_874_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42);
lean_inc_ref(v_arg_639_);
v___x_875_ = l_Lean_Expr_app___override(v___x_874_, v_arg_639_);
v___x_876_ = l_Lean_Meta_Sym_shareCommon(v___x_875_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
lean_inc_ref(v_arg_635_);
v___x_878_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt_x3f(v_arg_635_, v_a_877_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_932_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_932_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_932_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_932_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
if (lean_obj_tag(v_a_879_) == 1)
{
lean_object* v_val_883_; lean_object* v_fst_884_; lean_object* v_snd_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v_e_618_);
v_val_883_ = lean_ctor_get(v_a_879_, 0);
lean_inc(v_val_883_);
lean_dec_ref_known(v_a_879_, 1);
v_fst_884_ = lean_ctor_get(v_val_883_, 0);
v_snd_885_ = lean_ctor_get(v_val_883_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_val_883_);
if (v_isSharedCheck_897_ == 0)
{
v___x_887_ = v_val_883_;
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_snd_885_);
lean_inc(v_fst_884_);
lean_dec(v_val_883_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_889_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45);
lean_inc(v_fst_884_);
v___x_890_ = l_Lean_mkApp4(v___x_889_, v_arg_639_, v_arg_635_, v_fst_884_, v_snd_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v___x_890_);
v___x_892_ = v___x_887_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_fst_884_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_890_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_892_);
v___x_894_ = v___x_881_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_object* v___x_898_; 
lean_del_object(v___x_881_);
lean_dec(v_a_879_);
v___x_898_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_619_, v_a_627_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
lean_inc_ref(v_e_618_);
v___x_900_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v_natToIntMap_902_; uint8_t v___x_903_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
v_natToIntMap_902_ = lean_ctor_get(v_a_899_, 4);
lean_inc_ref(v_natToIntMap_902_);
lean_dec(v_a_899_);
v___x_903_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_natToIntMap_902_, v_e_618_);
lean_dec_ref(v_e_618_);
lean_dec_ref(v_natToIntMap_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec_ref_known(v___x_900_, 1);
v___x_904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48);
v___x_905_ = l_Lean_mkAppB(v___x_904_, v_arg_639_, v_arg_635_);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = l_Lean_Meta_Grind_pushNewFact(v___x_905_, v___x_906_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v___x_907_, 0);
lean_dec(v_unused_915_);
v___x_909_ = v___x_907_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_dec(v___x_907_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v_a_901_);
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_901_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_a_901_);
v_a_916_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_907_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_907_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
lean_dec(v_a_901_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
return v___x_900_;
}
}
else
{
lean_dec(v_a_899_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_e_618_);
return v___x_900_;
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_e_618_);
v_a_924_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_898_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_898_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_e_618_);
v_a_933_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_878_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_878_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_arg_635_);
lean_dec_ref(v_e_618_);
v_a_941_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_876_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_876_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref(v_e_618_);
v_a_949_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_630_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_630_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___boxed(lean_object* v_e_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_e_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec(v_a_958_);
return v_res_969_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1(lean_object* v_00_u03b2_970_, lean_object* v_x_971_, lean_object* v_x_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_x_971_, v_x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___boxed(lean_object* v_00_u03b2_974_, lean_object* v_x_975_, lean_object* v_x_976_){
_start:
{
uint8_t v_res_977_; lean_object* v_r_978_; 
v_res_977_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1(v_00_u03b2_974_, v_x_975_, v_x_976_);
lean_dec_ref(v_x_976_);
lean_dec_ref(v_x_975_);
v_r_978_ = lean_box(v_res_977_);
return v_r_978_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1(lean_object* v_00_u03b2_979_, lean_object* v_x_980_, size_t v_x_981_, lean_object* v_x_982_){
_start:
{
uint8_t v___x_983_; 
v___x_983_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(v_x_980_, v_x_981_, v_x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___boxed(lean_object* v_00_u03b2_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
size_t v_x_63110__boxed_988_; uint8_t v_res_989_; lean_object* v_r_990_; 
v_x_63110__boxed_988_ = lean_unbox_usize(v_x_986_);
lean_dec(v_x_986_);
v_res_989_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1(v_00_u03b2_984_, v_x_985_, v_x_63110__boxed_988_, v_x_987_);
lean_dec_ref(v_x_987_);
lean_dec_ref(v_x_985_);
v_r_990_ = lean_box(v_res_989_);
return v_r_990_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_991_, lean_object* v_keys_992_, lean_object* v_vals_993_, lean_object* v_heq_994_, lean_object* v_i_995_, lean_object* v_k_996_){
_start:
{
uint8_t v___x_997_; 
v___x_997_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(v_keys_992_, v_i_995_, v_k_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_998_, lean_object* v_keys_999_, lean_object* v_vals_1000_, lean_object* v_heq_1001_, lean_object* v_i_1002_, lean_object* v_k_1003_){
_start:
{
uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_res_1004_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2(v_00_u03b2_998_, v_keys_999_, v_vals_1000_, v_heq_1001_, v_i_1002_, v_k_1003_);
lean_dec_ref(v_k_1003_);
lean_dec_ref(v_vals_1000_);
lean_dec_ref(v_keys_999_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v_fst_1020_; lean_object* v_snd_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1045_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v_fst_1020_ = lean_ctor_get(v_a_1019_, 0);
v_snd_1021_ = lean_ctor_get(v_a_1019_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_a_1019_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1023_ = v_a_1019_;
v_isShared_1024_ = v_isSharedCheck_1045_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_snd_1021_);
lean_inc(v_fst_1020_);
lean_dec(v_a_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1045_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Meta_Sym_shareCommon(v_fst_1020_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1036_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1036_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1036_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v_a_1026_);
v___x_1031_ = v___x_1023_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1026_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_snd_1021_);
v___x_1031_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1033_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1031_);
v___x_1033_ = v___x_1028_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_del_object(v___x_1023_);
lean_dec(v_snd_1021_);
v_a_1037_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1025_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1025_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
else
{
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt___boxed(lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec(v_a_1047_);
return v_res_1058_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_unsigned_to_nat(1u);
v___x_1068_ = lean_nat_to_int(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5);
v___x_1070_ = lean_int_neg(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = lean_nat_to_int(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object* v_e_1075_, lean_object* v_x_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = l_Lean_Expr_cleanupAnnotations(v_e_1075_);
v___x_1092_ = l_Lean_Expr_isApp(v___x_1091_);
if (v___x_1092_ == 0)
{
lean_dec_ref(v___x_1091_);
lean_dec(v_x_1076_);
goto v___jp_1088_;
}
else
{
lean_object* v_arg_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_arg_1093_ = lean_ctor_get(v___x_1091_, 1);
lean_inc_ref(v_arg_1093_);
v___x_1094_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1091_);
v___x_1095_ = l_Lean_Expr_isApp(v___x_1094_);
if (v___x_1095_ == 0)
{
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_arg_1093_);
lean_dec(v_x_1076_);
goto v___jp_1088_;
}
else
{
lean_object* v_arg_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v_arg_1096_ = lean_ctor_get(v___x_1094_, 1);
lean_inc_ref(v_arg_1096_);
v___x_1097_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1094_);
v___x_1098_ = l_Lean_Expr_isApp(v___x_1097_);
if (v___x_1098_ == 0)
{
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_arg_1096_);
lean_dec_ref(v_arg_1093_);
lean_dec(v_x_1076_);
goto v___jp_1088_;
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1097_);
v___x_1100_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1101_ = l_Lean_Expr_isConstOf(v___x_1099_, v___x_1100_);
lean_dec_ref(v___x_1099_);
if (v___x_1101_ == 0)
{
lean_dec_ref(v_arg_1096_);
lean_dec_ref(v_arg_1093_);
lean_dec(v_x_1076_);
goto v___jp_1088_;
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1102_ = l_Lean_Expr_cleanupAnnotations(v_arg_1096_);
v___x_1103_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4));
v___x_1104_ = l_Lean_Expr_isConstOf(v___x_1102_, v___x_1103_);
lean_dec_ref(v___x_1102_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec_ref(v_arg_1093_);
lean_dec(v_x_1076_);
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_1108_ = l_Lean_Expr_isAppOf(v_arg_1093_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1077_, v_a_1085_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1135_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1135_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1135_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_natDef_1114_; uint8_t v___x_1115_; 
v_natDef_1114_ = lean_ctor_get(v_a_1110_, 5);
lean_inc_ref(v_natDef_1114_);
lean_dec(v_a_1110_);
v___x_1115_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_natDef_1114_, v_arg_1093_);
lean_dec_ref(v_natDef_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
lean_del_object(v___x_1112_);
lean_inc_ref(v_arg_1093_);
v___x_1116_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_1093_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec_ref_known(v___x_1116_, 1);
v___x_1117_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6);
v___x_1118_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8);
v___x_1119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v_x_1076_);
lean_ctor_set(v___x_1119_, 2, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_arg_1093_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
lean_inc(v_a_1086_);
lean_inc_ref(v_a_1085_);
lean_inc(v_a_1084_);
lean_inc_ref(v_a_1083_);
lean_inc(v_a_1082_);
lean_inc_ref(v_a_1081_);
lean_inc(v_a_1080_);
lean_inc_ref(v_a_1079_);
lean_inc(v_a_1078_);
lean_inc(v_a_1077_);
v___x_1122_ = lean_grind_cutsat_assert_le(v___x_1121_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1122_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v_arg_1093_);
lean_dec(v_x_1076_);
v_a_1123_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1116_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1116_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
lean_dec_ref(v_arg_1093_);
lean_dec(v_x_1076_);
v___x_1131_ = lean_box(0);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1131_);
v___x_1133_ = v___x_1112_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v_arg_1093_);
lean_dec(v_x_1076_);
v_a_1136_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1109_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1109_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec_ref(v_arg_1093_);
lean_dec(v_x_1076_);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
}
}
}
}
v___jp_1088_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___boxed(lean_object* v_e_1146_, lean_object* v_x_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_e_1146_, v_x_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec(v_a_1148_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(lean_object* v_e_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1175_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1175_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1175_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_natToIntMap_1169_; uint8_t v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v_natToIntMap_1169_ = lean_ctor_get(v_a_1165_, 4);
lean_inc_ref(v_natToIntMap_1169_);
lean_dec(v_a_1165_);
v___x_1170_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_natToIntMap_1169_, v_e_1160_);
lean_dec_ref(v_natToIntMap_1169_);
v___x_1171_ = lean_box(v___x_1170_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1171_);
v___x_1173_ = v___x_1167_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg___boxed(lean_object* v_e_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(v_e_1184_, v_a_1185_, v_a_1186_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_e_1184_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(lean_object* v_e_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(v_e_1189_, v_a_1190_, v_a_1198_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___boxed(lean_object* v_e_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(v_e_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_e_1202_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(lean_object* v_e_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1225_; 
lean_inc_ref(v_e_1215_);
v___x_1225_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1215_, v_a_1217_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___y_1228_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1260_ = l_Lean_Expr_cleanupAnnotations(v_a_1226_);
v___x_1261_ = l_Lean_Expr_isApp(v___x_1260_);
if (v___x_1261_ == 0)
{
lean_dec_ref(v___x_1260_);
v___y_1228_ = v_a_1217_;
goto v___jp_1227_;
}
else
{
lean_object* v_arg_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v_arg_1262_ = lean_ctor_get(v___x_1260_, 1);
lean_inc_ref(v_arg_1262_);
v___x_1263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1260_);
v___x_1264_ = l_Lean_Expr_isApp(v___x_1263_);
if (v___x_1264_ == 0)
{
lean_dec_ref(v___x_1263_);
lean_dec_ref(v_arg_1262_);
v___y_1228_ = v_a_1217_;
goto v___jp_1227_;
}
else
{
lean_object* v_arg_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_arg_1265_ = lean_ctor_get(v___x_1263_, 1);
lean_inc_ref(v_arg_1265_);
v___x_1266_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1263_);
v___x_1267_ = l_Lean_Expr_isApp(v___x_1266_);
if (v___x_1267_ == 0)
{
lean_dec_ref(v___x_1266_);
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_arg_1262_);
v___y_1228_ = v_a_1217_;
goto v___jp_1227_;
}
else
{
lean_object* v_arg_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v_arg_1268_ = lean_ctor_get(v___x_1266_, 1);
lean_inc_ref(v_arg_1268_);
v___x_1269_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1266_);
v___x_1270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_1271_ = l_Lean_Expr_isConstOf(v___x_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
uint8_t v___x_1272_; 
v___x_1272_ = l_Lean_Expr_isApp(v___x_1269_);
if (v___x_1272_ == 0)
{
lean_dec_ref(v___x_1269_);
lean_dec_ref(v_arg_1268_);
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_arg_1262_);
v___y_1228_ = v_a_1217_;
goto v___jp_1227_;
}
else
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1269_);
v___x_1274_ = l_Lean_Expr_isApp(v___x_1273_);
if (v___x_1274_ == 0)
{
lean_dec_ref(v___x_1273_);
lean_dec_ref(v_arg_1268_);
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_arg_1262_);
v___y_1228_ = v_a_1217_;
goto v___jp_1227_;
}
else
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1273_);
v___x_1276_ = l_Lean_Expr_isApp(v___x_1275_);
if (v___x_1276_ == 0)
{
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_arg_1268_);
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_arg_1262_);
v___y_1228_ = v_a_1217_;
goto v___jp_1227_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1275_);
v___x_1278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8));
v___x_1279_ = l_Lean_Expr_isConstOf(v___x_1277_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11));
v___x_1281_ = l_Lean_Expr_isConstOf(v___x_1277_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14));
v___x_1283_ = l_Lean_Expr_isConstOf(v___x_1277_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17));
v___x_1285_ = l_Lean_Expr_isConstOf(v___x_1277_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20));
v___x_1287_ = l_Lean_Expr_isConstOf(v___x_1277_, v___x_1286_);
lean_dec_ref(v___x_1277_);
if (v___x_1287_ == 0)
{
lean_dec_ref(v_arg_1268_);
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_arg_1262_);
v___y_1228_ = v_a_1217_;
goto v___jp_1227_;
}
else
{
lean_object* v___x_1288_; 
lean_dec_ref(v_e_1215_);
v___x_1288_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1268_, v_a_1217_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; uint8_t v___x_1290_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
v___x_1290_ = lean_unbox(v_a_1289_);
lean_dec(v_a_1289_);
if (v___x_1290_ == 0)
{
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_arg_1262_);
return v___x_1288_;
}
else
{
lean_object* v___x_1291_; 
lean_dec_ref_known(v___x_1288_, 1);
v___x_1291_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_1265_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; uint8_t v___x_1293_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
v___x_1293_ = lean_unbox(v_a_1292_);
lean_dec(v_a_1292_);
if (v___x_1293_ == 0)
{
lean_dec_ref(v_arg_1262_);
return v___x_1291_;
}
else
{
lean_dec_ref_known(v___x_1291_, 1);
v_e_1215_ = v_arg_1262_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1262_);
return v___x_1291_;
}
}
}
else
{
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_arg_1262_);
return v___x_1288_;
}
}
}
else
{
lean_object* v___x_1295_; 
lean_dec_ref(v___x_1277_);
lean_dec_ref(v_e_1215_);
v___x_1295_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1268_, v_a_1217_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; uint8_t v___x_1297_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
v___x_1297_ = lean_unbox(v_a_1296_);
lean_dec(v_a_1296_);
if (v___x_1297_ == 0)
{
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_arg_1262_);
return v___x_1295_;
}
else
{
lean_object* v___x_1298_; 
lean_dec_ref_known(v___x_1295_, 1);
v___x_1298_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_1265_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; uint8_t v___x_1300_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
v___x_1300_ = lean_unbox(v_a_1299_);
lean_dec(v_a_1299_);
if (v___x_1300_ == 0)
{
lean_dec_ref(v_arg_1262_);
return v___x_1298_;
}
else
{
lean_dec_ref_known(v___x_1298_, 1);
v_e_1215_ = v_arg_1262_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1262_);
return v___x_1298_;
}
}
}
else
{
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_arg_1262_);
return v___x_1295_;
}
}
}
else
{
lean_object* v___x_1302_; 
lean_dec_ref(v___x_1277_);
lean_dec_ref(v_e_1215_);
v___x_1302_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_1268_, v_a_1217_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; uint8_t v___x_1304_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
v___x_1304_ = lean_unbox(v_a_1303_);
lean_dec(v_a_1303_);
if (v___x_1304_ == 0)
{
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_arg_1262_);
return v___x_1302_;
}
else
{
lean_object* v___x_1305_; 
lean_dec_ref_known(v___x_1302_, 1);
v___x_1305_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_1265_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; uint8_t v___x_1307_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
v___x_1307_ = lean_unbox(v_a_1306_);
lean_dec(v_a_1306_);
if (v___x_1307_ == 0)
{
lean_dec_ref(v_arg_1262_);
return v___x_1305_;
}
else
{
lean_dec_ref_known(v___x_1305_, 1);
v_e_1215_ = v_arg_1262_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1262_);
return v___x_1305_;
}
}
}
else
{
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_arg_1262_);
return v___x_1302_;
}
}
}
else
{
lean_object* v___x_1309_; 
lean_dec_ref(v___x_1277_);
lean_dec_ref(v_arg_1262_);
lean_dec_ref(v_e_1215_);
v___x_1309_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_1268_, v_a_1217_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; uint8_t v___x_1311_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
v___x_1311_ = lean_unbox(v_a_1310_);
lean_dec(v_a_1310_);
if (v___x_1311_ == 0)
{
lean_dec_ref(v_arg_1265_);
return v___x_1309_;
}
else
{
lean_dec_ref_known(v___x_1309_, 1);
v_e_1215_ = v_arg_1265_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1265_);
return v___x_1309_;
}
}
}
else
{
lean_object* v___x_1313_; 
lean_dec_ref(v___x_1277_);
lean_dec_ref(v_arg_1262_);
lean_dec_ref(v_e_1215_);
v___x_1313_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_1268_, v_a_1217_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; uint8_t v___x_1315_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
v___x_1315_ = lean_unbox(v_a_1314_);
lean_dec(v_a_1314_);
if (v___x_1315_ == 0)
{
lean_dec_ref(v_arg_1265_);
return v___x_1313_;
}
else
{
lean_dec_ref_known(v___x_1313_, 1);
v_e_1215_ = v_arg_1265_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1265_);
return v___x_1313_;
}
}
}
}
}
}
else
{
lean_object* v___x_1317_; 
lean_dec_ref(v___x_1269_);
lean_dec_ref(v_arg_1268_);
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_arg_1262_);
v___x_1317_ = l_Lean_Meta_getIntValue_x3f(v_e_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1334_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1334_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1334_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
if (lean_obj_tag(v_a_1318_) == 1)
{
lean_object* v_val_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v_val_1322_ = lean_ctor_get(v_a_1318_, 0);
lean_inc(v_val_1322_);
lean_dec_ref_known(v_a_1318_, 1);
v___x_1323_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7);
v___x_1324_ = lean_int_dec_le(v___x_1323_, v_val_1322_);
lean_dec(v_val_1322_);
v___x_1325_ = lean_box(v___x_1324_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1325_);
v___x_1327_ = v___x_1320_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
else
{
uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
lean_dec(v_a_1318_);
v___x_1329_ = 0;
v___x_1330_ = lean_box(v___x_1329_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1330_);
v___x_1332_ = v___x_1320_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
v_a_1335_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1317_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1317_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
}
}
v___jp_1227_:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1215_, v___y_1228_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1251_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1232_ = v___x_1229_;
v_isShared_1233_ = v_isSharedCheck_1251_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1251_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = l_Lean_Expr_cleanupAnnotations(v_a_1230_);
v___x_1235_ = l_Lean_Expr_isApp(v___x_1234_);
if (v___x_1235_ == 0)
{
lean_dec_ref(v___x_1234_);
lean_del_object(v___x_1232_);
goto v___jp_1221_;
}
else
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1234_);
v___x_1237_ = l_Lean_Expr_isApp(v___x_1236_);
if (v___x_1237_ == 0)
{
lean_dec_ref(v___x_1236_);
lean_del_object(v___x_1232_);
goto v___jp_1221_;
}
else
{
lean_object* v_arg_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v_arg_1238_ = lean_ctor_get(v___x_1236_, 1);
lean_inc_ref(v_arg_1238_);
v___x_1239_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1236_);
v___x_1240_ = l_Lean_Expr_isApp(v___x_1239_);
if (v___x_1240_ == 0)
{
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_arg_1238_);
lean_del_object(v___x_1232_);
goto v___jp_1221_;
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1239_);
v___x_1242_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1243_ = l_Lean_Expr_isConstOf(v___x_1241_, v___x_1242_);
lean_dec_ref(v___x_1241_);
if (v___x_1243_ == 0)
{
lean_dec_ref(v_arg_1238_);
lean_del_object(v___x_1232_);
goto v___jp_1221_;
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1244_ = l_Lean_Expr_cleanupAnnotations(v_arg_1238_);
v___x_1245_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4));
v___x_1246_ = l_Lean_Expr_isConstOf(v___x_1244_, v___x_1245_);
lean_dec_ref(v___x_1244_);
v___x_1247_ = lean_box(v___x_1246_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1247_);
v___x_1249_ = v___x_1232_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
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
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
v_a_1252_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1229_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1229_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v_e_1215_);
v_a_1343_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1225_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1225_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
v___jp_1221_:
{
uint8_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = 0;
v___x_1223_ = lean_box(v___x_1222_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg___boxed(lean_object* v_e_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_e_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(lean_object* v_msg_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___f_1365_; lean_object* v___x_5805__overap_1366_; lean_object* v___x_1367_; 
v___f_1365_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0));
v___x_5805__overap_1366_ = lean_panic_fn_borrowed(v___f_1365_, v_msg_1359_);
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
v___x_1367_ = lean_apply_5(v___x_5805__overap_1366_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, lean_box(0));
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___boxed(lean_object* v_msg_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(v_msg_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2));
v___x_1379_ = lean_unsigned_to_nat(43u);
v___x_1380_ = lean_unsigned_to_nat(154u);
v___x_1381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1));
v___x_1382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0));
v___x_1383_ = l_mkPanicMessageWithDecl(v___x_1382_, v___x_1381_, v___x_1380_, v___x_1379_, v___x_1378_);
return v___x_1383_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_box(0);
v___x_1391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6));
v___x_1392_ = l_Lean_mkConst(v___x_1391_, v___x_1390_);
return v___x_1392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_box(0);
v___x_1399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9));
v___x_1400_ = l_Lean_mkConst(v___x_1399_, v___x_1398_);
return v___x_1400_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_box(0);
v___x_1407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12));
v___x_1408_ = l_Lean_mkConst(v___x_1407_, v___x_1406_);
return v___x_1408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15));
v___x_1416_ = l_Lean_mkConst(v___x_1415_, v___x_1414_);
return v___x_1416_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_box(0);
v___x_1423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18));
v___x_1424_ = l_Lean_mkConst(v___x_1423_, v___x_1422_);
return v___x_1424_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21));
v___x_1432_ = l_Lean_mkConst(v___x_1431_, v___x_1430_);
return v___x_1432_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = lean_box(0);
v___x_1439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24));
v___x_1440_ = l_Lean_mkConst(v___x_1439_, v___x_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(lean_object* v_e_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___x_1454_; 
lean_inc_ref(v_e_1441_);
v___x_1454_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1441_, v_a_1443_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1579_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1579_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1579_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = l_Lean_Expr_cleanupAnnotations(v_a_1455_);
v___x_1486_ = l_Lean_Expr_isApp(v___x_1485_);
if (v___x_1486_ == 0)
{
lean_dec_ref(v___x_1485_);
lean_del_object(v___x_1457_);
v___y_1460_ = v_a_1442_;
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
goto v___jp_1459_;
}
else
{
lean_object* v_arg_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v_arg_1487_ = lean_ctor_get(v___x_1485_, 1);
lean_inc_ref(v_arg_1487_);
v___x_1488_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1485_);
v___x_1489_ = l_Lean_Expr_isApp(v___x_1488_);
if (v___x_1489_ == 0)
{
lean_dec_ref(v___x_1488_);
lean_dec_ref(v_arg_1487_);
lean_del_object(v___x_1457_);
v___y_1460_ = v_a_1442_;
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
goto v___jp_1459_;
}
else
{
lean_object* v_arg_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v_arg_1490_ = lean_ctor_get(v___x_1488_, 1);
lean_inc_ref(v_arg_1490_);
v___x_1491_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1488_);
v___x_1492_ = l_Lean_Expr_isApp(v___x_1491_);
if (v___x_1492_ == 0)
{
lean_dec_ref(v___x_1491_);
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
lean_del_object(v___x_1457_);
v___y_1460_ = v_a_1442_;
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1493_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1491_);
v___x_1494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_1495_ = l_Lean_Expr_isConstOf(v___x_1493_, v___x_1494_);
if (v___x_1495_ == 0)
{
uint8_t v___x_1496_; 
lean_del_object(v___x_1457_);
v___x_1496_ = l_Lean_Expr_isApp(v___x_1493_);
if (v___x_1496_ == 0)
{
lean_dec_ref(v___x_1493_);
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
v___y_1460_ = v_a_1442_;
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1497_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1493_);
v___x_1498_ = l_Lean_Expr_isApp(v___x_1497_);
if (v___x_1498_ == 0)
{
lean_dec_ref(v___x_1497_);
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
v___y_1460_ = v_a_1442_;
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1499_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1497_);
v___x_1500_ = l_Lean_Expr_isApp(v___x_1499_);
if (v___x_1500_ == 0)
{
lean_dec_ref(v___x_1499_);
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
v___y_1460_ = v_a_1442_;
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1501_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1499_);
v___x_1502_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8));
v___x_1503_ = l_Lean_Expr_isConstOf(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11));
v___x_1505_ = l_Lean_Expr_isConstOf(v___x_1501_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14));
v___x_1507_ = l_Lean_Expr_isConstOf(v___x_1501_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1508_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17));
v___x_1509_ = l_Lean_Expr_isConstOf(v___x_1501_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20));
v___x_1511_ = l_Lean_Expr_isConstOf(v___x_1501_, v___x_1510_);
lean_dec_ref(v___x_1501_);
if (v___x_1511_ == 0)
{
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
v___y_1460_ = v_a_1442_;
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1512_; 
lean_dec_ref(v_e_1441_);
lean_inc_ref(v_arg_1490_);
v___x_1512_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1490_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
lean_inc_ref(v_arg_1487_);
v___x_1514_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1487_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1524_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1524_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1524_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1519_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10);
v___x_1520_ = l_Lean_mkApp4(v___x_1519_, v_arg_1490_, v_arg_1487_, v_a_1513_, v_a_1515_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1520_);
v___x_1522_ = v___x_1517_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
else
{
lean_dec(v_a_1513_);
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
return v___x_1514_;
}
}
else
{
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
return v___x_1512_;
}
}
}
else
{
lean_object* v___x_1525_; 
lean_dec_ref(v___x_1501_);
lean_dec_ref(v_e_1441_);
lean_inc_ref(v_arg_1490_);
v___x_1525_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1490_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1527_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref_known(v___x_1525_, 1);
lean_inc_ref(v_arg_1487_);
v___x_1527_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1487_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1537_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1532_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13);
v___x_1533_ = l_Lean_mkApp4(v___x_1532_, v_arg_1490_, v_arg_1487_, v_a_1526_, v_a_1528_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1533_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
else
{
lean_dec(v_a_1526_);
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
return v___x_1527_;
}
}
else
{
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
return v___x_1525_;
}
}
}
else
{
lean_object* v___x_1538_; 
lean_dec_ref(v___x_1501_);
lean_dec_ref(v_e_1441_);
lean_inc_ref(v_arg_1490_);
v___x_1538_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1490_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1540_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
lean_inc_ref(v_arg_1487_);
v___x_1540_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1487_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1550_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1550_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1550_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16);
v___x_1546_ = l_Lean_mkApp4(v___x_1545_, v_arg_1490_, v_arg_1487_, v_a_1539_, v_a_1541_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1546_);
v___x_1548_ = v___x_1543_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
else
{
lean_dec(v_a_1539_);
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
return v___x_1540_;
}
}
else
{
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
return v___x_1538_;
}
}
}
else
{
lean_object* v___x_1551_; 
lean_dec_ref(v___x_1501_);
lean_dec_ref(v_e_1441_);
lean_inc_ref(v_arg_1490_);
v___x_1551_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1490_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1561_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1561_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1561_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1556_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19);
v___x_1557_ = l_Lean_mkApp3(v___x_1556_, v_arg_1490_, v_arg_1487_, v_a_1552_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1557_);
v___x_1559_ = v___x_1554_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
return v___x_1551_;
}
}
}
else
{
lean_object* v___x_1562_; 
lean_dec_ref(v___x_1501_);
lean_dec_ref(v_e_1441_);
lean_inc_ref(v_arg_1490_);
v___x_1562_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1490_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1572_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1572_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1572_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1567_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22);
v___x_1568_ = l_Lean_mkApp3(v___x_1567_, v_arg_1490_, v_arg_1487_, v_a_1563_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1568_);
v___x_1570_ = v___x_1565_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
else
{
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
return v___x_1562_;
}
}
}
}
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
lean_dec_ref(v___x_1493_);
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1487_);
v___x_1573_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25);
v___x_1574_ = l_Lean_eagerReflBoolTrue;
v___x_1575_ = l_Lean_mkAppB(v___x_1573_, v_e_1441_, v___x_1574_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1575_);
v___x_1577_ = v___x_1457_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
v___jp_1459_:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1441_, v___y_1461_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1484_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1484_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1484_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = l_Lean_Expr_cleanupAnnotations(v_a_1465_);
v___x_1470_ = l_Lean_Expr_isApp(v___x_1469_);
if (v___x_1470_ == 0)
{
lean_dec_ref(v___x_1469_);
lean_del_object(v___x_1467_);
v___y_1448_ = v___y_1460_;
v___y_1449_ = v___y_1461_;
v___y_1450_ = v___y_1462_;
v___y_1451_ = v___y_1463_;
goto v___jp_1447_;
}
else
{
lean_object* v_arg_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_arg_1471_ = lean_ctor_get(v___x_1469_, 1);
lean_inc_ref(v_arg_1471_);
v___x_1472_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1469_);
v___x_1473_ = l_Lean_Expr_isApp(v___x_1472_);
if (v___x_1473_ == 0)
{
lean_dec_ref(v___x_1472_);
lean_dec_ref(v_arg_1471_);
lean_del_object(v___x_1467_);
v___y_1448_ = v___y_1460_;
v___y_1449_ = v___y_1461_;
v___y_1450_ = v___y_1462_;
v___y_1451_ = v___y_1463_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1474_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1472_);
v___x_1475_ = l_Lean_Expr_isApp(v___x_1474_);
if (v___x_1475_ == 0)
{
lean_dec_ref(v___x_1474_);
lean_dec_ref(v_arg_1471_);
lean_del_object(v___x_1467_);
v___y_1448_ = v___y_1460_;
v___y_1449_ = v___y_1461_;
v___y_1450_ = v___y_1462_;
v___y_1451_ = v___y_1463_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1476_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1474_);
v___x_1477_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1478_ = l_Lean_Expr_isConstOf(v___x_1476_, v___x_1477_);
lean_dec_ref(v___x_1476_);
if (v___x_1478_ == 0)
{
lean_dec_ref(v_arg_1471_);
lean_del_object(v___x_1467_);
v___y_1448_ = v___y_1460_;
v___y_1449_ = v___y_1461_;
v___y_1450_ = v___y_1462_;
v___y_1451_ = v___y_1463_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1479_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7);
v___x_1480_ = l_Lean_Expr_app___override(v___x_1479_, v_arg_1471_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1480_);
v___x_1482_ = v___x_1467_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
}
}
else
{
return v___x_1464_;
}
}
}
}
else
{
lean_dec_ref(v_e_1441_);
return v___x_1454_;
}
v___jp_1447_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3);
v___x_1453_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(v___x_1452_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
return v___x_1453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___boxed(lean_object* v_e_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_e_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(lean_object* v_e_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v___x_1593_; 
lean_inc_ref(v_e_1587_);
v___x_1593_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_e_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1621_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1621_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1621_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_unbox(v_a_1594_);
lean_dec(v_a_1594_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
lean_dec_ref(v_e_1587_);
v___x_1599_ = lean_box(0);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1599_);
v___x_1601_ = v___x_1596_;
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
else
{
lean_object* v___x_1603_; 
lean_del_object(v___x_1596_);
v___x_1603_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_e_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1612_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1612_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1612_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_a_1604_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1608_);
v___x_1610_ = v___x_1606_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_a_1613_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1603_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1603_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v_e_1587_);
v_a_1622_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1593_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1593_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg___boxed(lean_object* v_e_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(v_e_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f(lean_object* v_e_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(v_e_1637_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___boxed(lean_object* v_e_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f(v_e_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec(v_a_1651_);
return v_res_1662_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = lean_box(0);
v___x_1669_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1));
v___x_1670_ = l_Lean_mkConst(v___x_1669_, v___x_1668_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(lean_object* v_e_1671_, lean_object* v_x_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1685_ = l_Lean_Expr_isAppOf(v_e_1671_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_1687_ = l_Lean_Expr_isAppOf(v_e_1671_, v___x_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
lean_inc_ref(v_e_1671_);
v___x_1688_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(v_e_1671_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1712_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1712_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1712_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
if (lean_obj_tag(v_a_1689_) == 1)
{
lean_object* v_val_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1707_; 
lean_del_object(v___x_1691_);
v_val_1693_ = lean_ctor_get(v_a_1689_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_a_1689_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1695_ = v_a_1689_;
v_isShared_1696_ = v_isSharedCheck_1707_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_val_1693_);
lean_dec(v_a_1689_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1707_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1697_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2);
v___x_1698_ = l_Lean_mkAppB(v___x_1697_, v_e_1671_, v_val_1693_);
v___x_1699_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6);
v___x_1700_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8);
v___x_1701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v_x_1672_);
lean_ctor_set(v___x_1701_, 2, v___x_1700_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 4);
lean_ctor_set(v___x_1695_, 0, v___x_1698_);
v___x_1703_ = v___x_1695_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1698_);
v___x_1703_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1701_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
lean_inc(v_a_1682_);
lean_inc_ref(v_a_1681_);
lean_inc(v_a_1680_);
lean_inc_ref(v_a_1679_);
lean_inc(v_a_1678_);
lean_inc_ref(v_a_1677_);
lean_inc(v_a_1676_);
lean_inc_ref(v_a_1675_);
lean_inc(v_a_1674_);
lean_inc(v_a_1673_);
v___x_1705_ = lean_grind_cutsat_assert_le(v___x_1704_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
return v___x_1705_;
}
}
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1710_; 
lean_dec(v_a_1689_);
lean_dec(v_x_1672_);
lean_dec_ref(v_e_1671_);
v___x_1708_ = lean_box(0);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1708_);
v___x_1710_ = v___x_1691_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_x_1672_);
lean_dec_ref(v_e_1671_);
v_a_1713_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1688_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1688_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec(v_x_1672_);
lean_dec_ref(v_e_1671_);
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
return v___x_1722_;
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v_x_1672_);
lean_dec_ref(v_e_1671_);
v___x_1723_ = lean_box(0);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
return v___x_1724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___boxed(lean_object* v_e_1725_, lean_object* v_x_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_e_1725_, v_x_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec(v_a_1727_);
return v_res_1738_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
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
