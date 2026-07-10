// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Inv
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM import Lean.Meta.Sym.Arith.Poly
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_Poly_isSorted(lean_object*);
uint8_t l_Lean_Grind_CommRing_Poly_checkCoeffs(lean_object*);
uint8_t l_Lean_Grind_CommRing_Poly_checkNoUnitMon(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.Meta.Tactic.Grind.Arith.CommRing.Inv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.CommRing.Inv.0.Lean.Meta.Grind.Arith.CommRing.checkVars"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "assertion violation: isSameExpr expr expr'\n    "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: s.vars.size == num\n\n"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.CommRing.Inv.0.Lean.Meta.Grind.Arith.CommRing.checkPoly"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "assertion violation: !(p matches .num _)\n\n"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "assertion violation: p.isSorted\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "assertion violation: p.checkCoeffs\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: p.checkNoUnitMon\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Lean.Meta.Grind.Arith.CommRing.checkInvariants"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Tactic.Grind.Arith.CommRing.Inv.3119225764._hygCtx._hyg.60.0 ) == ringId\n      "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInvariants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___boxed(lean_object**);
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v___x_15_; lean_object* v___f_16_; lean_object* v___x_6983__overap_17_; lean_object* v___x_18_; 
v___x_15_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0);
v___f_16_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_16_, 0, v___x_15_);
v___x_6983__overap_17_ = lean_panic_fn_borrowed(v___f_16_, v_msg_2_);
lean_dec_ref(v___f_16_);
lean_inc(v___y_13_);
lean_inc_ref(v___y_12_);
lean_inc(v___y_11_);
lean_inc_ref(v___y_10_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_18_ = lean_apply_12(v___x_6983__overap_17_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, lean_box(0));
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___boxed(lean_object* v_msg_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v_msg_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_32_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___closed__0(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1(lean_object* v_msg_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; lean_object* v___f_48_; lean_object* v___x_7001__overap_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___closed__0);
v___f_48_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_48_, 0, v___x_47_);
v___x_7001__overap_49_ = lean_panic_fn_borrowed(v___f_48_, v_msg_34_);
lean_dec_ref(v___f_48_);
lean_inc(v___y_45_);
lean_inc_ref(v___y_44_);
lean_inc(v___y_43_);
lean_inc_ref(v___y_42_);
lean_inc(v___y_41_);
lean_inc_ref(v___y_40_);
lean_inc(v___y_39_);
lean_inc_ref(v___y_38_);
lean_inc(v___y_37_);
lean_inc(v___y_36_);
lean_inc_ref(v___y_35_);
v___x_50_ = lean_apply_12(v___x_7001__overap_49_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___boxed(lean_object* v_msg_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1(v_msg_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_64_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__2));
v___x_69_ = lean_unsigned_to_nat(6u);
v___x_70_ = lean_unsigned_to_nat(21u);
v___x_71_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1));
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_73_ = l_mkPanicMessageWithDecl(v___x_72_, v___x_71_, v___x_70_, v___x_69_, v___x_68_);
return v___x_73_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__4));
v___x_76_ = lean_unsigned_to_nat(6u);
v___x_77_ = lean_unsigned_to_nat(19u);
v___x_78_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1));
v___x_79_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_80_ = l_mkPanicMessageWithDecl(v___x_79_, v___x_78_, v___x_77_, v___x_76_, v___x_75_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0(lean_object* v_vars_81_, lean_object* v_x_82_, lean_object* v_____s_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_fst_101_; lean_object* v_snd_102_; lean_object* v_size_103_; uint8_t v___x_104_; 
v_fst_101_ = lean_ctor_get(v_x_82_, 0);
v_snd_102_ = lean_ctor_get(v_x_82_, 1);
v_size_103_ = lean_ctor_get(v_vars_81_, 2);
v___x_104_ = lean_nat_dec_lt(v_snd_102_, v_size_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3);
v___x_106_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_105_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_dec_ref_known(v___x_106_, 1);
goto v___jp_96_;
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = l_Lean_instInhabitedExpr;
v___x_116_ = l_Lean_PersistentArray_get_x21___redArg(v___x_115_, v_vars_81_, v_snd_102_);
v___x_117_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_101_, v___x_116_);
lean_dec(v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5);
v___x_119_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1(v___x_118_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
return v___x_119_;
}
else
{
goto v___jp_96_;
}
}
v___jp_96_:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_add(v_____s_83_, v___x_97_);
v___x_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___boxed(lean_object* v_vars_120_, lean_object* v_x_121_, lean_object* v_____s_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0(v_vars_120_, v_x_121_, v_____s_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v_____s_122_);
lean_dec_ref(v_x_121_);
lean_dec_ref(v_vars_120_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(lean_object* v_f_136_, lean_object* v_keys_137_, lean_object* v_vals_138_, lean_object* v_i_139_, lean_object* v_acc_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = lean_array_get_size(v_keys_137_);
v___x_154_ = lean_nat_dec_lt(v_i_139_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_i_139_);
lean_dec_ref(v_f_136_);
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v_acc_140_);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
else
{
lean_object* v_k_157_; lean_object* v_v_158_; lean_object* v___x_159_; 
v_k_157_ = lean_array_fget_borrowed(v_keys_137_, v_i_139_);
v_v_158_ = lean_array_fget_borrowed(v_vals_138_, v_i_139_);
lean_inc_ref(v_f_136_);
lean_inc(v___y_151_);
lean_inc_ref(v___y_150_);
lean_inc(v___y_149_);
lean_inc_ref(v___y_148_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
lean_inc(v___y_143_);
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
lean_inc(v_v_158_);
lean_inc(v_k_157_);
v___x_159_ = lean_apply_15(v_f_136_, v_acc_140_, v_k_157_, v_v_158_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, lean_box(0));
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
if (lean_obj_tag(v_a_160_) == 0)
{
lean_dec_ref_known(v_a_160_, 1);
lean_dec(v_i_139_);
lean_dec_ref(v_f_136_);
return v___x_159_;
}
else
{
lean_object* v_a_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec_ref_known(v___x_159_, 1);
v_a_161_ = lean_ctor_get(v_a_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v_a_160_, 1);
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_add(v_i_139_, v___x_162_);
lean_dec(v_i_139_);
v_i_139_ = v___x_163_;
v_acc_140_ = v_a_161_;
goto _start;
}
}
else
{
lean_dec(v_i_139_);
lean_dec_ref(v_f_136_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_f_165_ = _args[0];
lean_object* v_keys_166_ = _args[1];
lean_object* v_vals_167_ = _args[2];
lean_object* v_i_168_ = _args[3];
lean_object* v_acc_169_ = _args[4];
lean_object* v___y_170_ = _args[5];
lean_object* v___y_171_ = _args[6];
lean_object* v___y_172_ = _args[7];
lean_object* v___y_173_ = _args[8];
lean_object* v___y_174_ = _args[9];
lean_object* v___y_175_ = _args[10];
lean_object* v___y_176_ = _args[11];
lean_object* v___y_177_ = _args[12];
lean_object* v___y_178_ = _args[13];
lean_object* v___y_179_ = _args[14];
lean_object* v___y_180_ = _args[15];
lean_object* v___y_181_ = _args[16];
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_165_, v_keys_166_, v_vals_167_, v_i_168_, v_acc_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec_ref(v_vals_167_);
lean_dec_ref(v_keys_166_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(lean_object* v_f_183_, lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_object* v_es_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_220_; 
v_es_198_ = lean_ctor_get(v_x_184_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_220_ == 0)
{
v___x_200_ = v_x_184_;
v_isShared_201_ = v_isSharedCheck_220_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_es_198_);
lean_dec(v_x_184_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_220_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_array_get_size(v_es_198_);
v___x_204_ = lean_nat_dec_lt(v___x_202_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_206_; 
lean_dec_ref(v_es_198_);
lean_dec_ref(v_f_183_);
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 1);
lean_ctor_set(v___x_200_, 0, v_x_185_);
v___x_206_ = v___x_200_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_x_185_);
v___x_206_ = v_reuseFailAlloc_208_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; 
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
else
{
uint8_t v___x_209_; 
v___x_209_ = lean_nat_dec_le(v___x_203_, v___x_203_);
if (v___x_209_ == 0)
{
if (v___x_204_ == 0)
{
lean_object* v___x_211_; 
lean_dec_ref(v_es_198_);
lean_dec_ref(v_f_183_);
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 1);
lean_ctor_set(v___x_200_, 0, v_x_185_);
v___x_211_ = v___x_200_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_x_185_);
v___x_211_ = v_reuseFailAlloc_213_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; 
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
else
{
size_t v___x_214_; size_t v___x_215_; lean_object* v___x_216_; 
lean_del_object(v___x_200_);
v___x_214_ = ((size_t)0ULL);
v___x_215_ = lean_usize_of_nat(v___x_203_);
v___x_216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_183_, v_es_198_, v___x_214_, v___x_215_, v_x_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec_ref(v_es_198_);
return v___x_216_;
}
}
else
{
size_t v___x_217_; size_t v___x_218_; lean_object* v___x_219_; 
lean_del_object(v___x_200_);
v___x_217_ = ((size_t)0ULL);
v___x_218_ = lean_usize_of_nat(v___x_203_);
v___x_219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_183_, v_es_198_, v___x_217_, v___x_218_, v_x_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec_ref(v_es_198_);
return v___x_219_;
}
}
}
}
else
{
lean_object* v_ks_221_; lean_object* v_vs_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_ks_221_ = lean_ctor_get(v_x_184_, 0);
lean_inc_ref(v_ks_221_);
v_vs_222_ = lean_ctor_get(v_x_184_, 1);
lean_inc_ref(v_vs_222_);
lean_dec_ref_known(v_x_184_, 2);
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_183_, v_ks_221_, v_vs_222_, v___x_223_, v_x_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec_ref(v_vs_222_);
lean_dec_ref(v_ks_221_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_f_225_, lean_object* v_as_226_, size_t v_i_227_, size_t v_stop_228_, lean_object* v_b_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_a_243_; lean_object* v___y_248_; uint8_t v___x_251_; 
v___x_251_ = lean_usize_dec_eq(v_i_227_, v_stop_228_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
v___x_252_ = lean_array_uget_borrowed(v_as_226_, v_i_227_);
switch(lean_obj_tag(v___x_252_))
{
case 0:
{
lean_object* v_key_253_; lean_object* v_val_254_; lean_object* v___x_255_; 
v_key_253_ = lean_ctor_get(v___x_252_, 0);
v_val_254_ = lean_ctor_get(v___x_252_, 1);
lean_inc_ref(v_f_225_);
lean_inc(v___y_240_);
lean_inc_ref(v___y_239_);
lean_inc(v___y_238_);
lean_inc_ref(v___y_237_);
lean_inc(v___y_236_);
lean_inc_ref(v___y_235_);
lean_inc(v___y_234_);
lean_inc_ref(v___y_233_);
lean_inc(v___y_232_);
lean_inc(v___y_231_);
lean_inc_ref(v___y_230_);
lean_inc(v_val_254_);
lean_inc(v_key_253_);
v___x_255_ = lean_apply_15(v_f_225_, v_b_229_, v_key_253_, v_val_254_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, lean_box(0));
v___y_248_ = v___x_255_;
goto v___jp_247_;
}
case 1:
{
lean_object* v_node_256_; lean_object* v___x_257_; 
v_node_256_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_node_256_);
lean_inc_ref(v_f_225_);
v___x_257_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_225_, v_node_256_, v_b_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
v___y_248_ = v___x_257_;
goto v___jp_247_;
}
default: 
{
v_a_243_ = v_b_229_;
goto v___jp_242_;
}
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref(v_f_225_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v_b_229_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
v___jp_242_:
{
size_t v___x_244_; size_t v___x_245_; 
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_add(v_i_227_, v___x_244_);
v_i_227_ = v___x_245_;
v_b_229_ = v_a_243_;
goto _start;
}
v___jp_247_:
{
if (lean_obj_tag(v___y_248_) == 0)
{
lean_object* v_a_249_; 
v_a_249_ = lean_ctor_get(v___y_248_, 0);
if (lean_obj_tag(v_a_249_) == 0)
{
lean_dec_ref(v_f_225_);
return v___y_248_;
}
else
{
lean_object* v_a_250_; 
lean_inc_ref(v_a_249_);
lean_dec_ref_known(v___y_248_, 1);
v_a_250_ = lean_ctor_get(v_a_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v_a_249_, 1);
v_a_243_ = v_a_250_;
goto v___jp_242_;
}
}
else
{
lean_dec_ref(v_f_225_);
return v___y_248_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_f_260_ = _args[0];
lean_object* v_as_261_ = _args[1];
lean_object* v_i_262_ = _args[2];
lean_object* v_stop_263_ = _args[3];
lean_object* v_b_264_ = _args[4];
lean_object* v___y_265_ = _args[5];
lean_object* v___y_266_ = _args[6];
lean_object* v___y_267_ = _args[7];
lean_object* v___y_268_ = _args[8];
lean_object* v___y_269_ = _args[9];
lean_object* v___y_270_ = _args[10];
lean_object* v___y_271_ = _args[11];
lean_object* v___y_272_ = _args[12];
lean_object* v___y_273_ = _args[13];
lean_object* v___y_274_ = _args[14];
lean_object* v___y_275_ = _args[15];
lean_object* v___y_276_ = _args[16];
_start:
{
size_t v_i_boxed_277_; size_t v_stop_boxed_278_; lean_object* v_res_279_; 
v_i_boxed_277_ = lean_unbox_usize(v_i_262_);
lean_dec(v_i_262_);
v_stop_boxed_278_ = lean_unbox_usize(v_stop_263_);
lean_dec(v_stop_263_);
v_res_279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_260_, v_as_261_, v_i_boxed_277_, v_stop_boxed_278_, v_b_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec_ref(v_as_261_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_f_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_280_, v_x_281_, v_x_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0(lean_object* v_f_296_, lean_object* v_s_297_, lean_object* v_a_298_, lean_object* v_b_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_a_298_);
lean_ctor_set(v___x_312_, 1, v_b_299_);
lean_inc(v___y_310_);
lean_inc_ref(v___y_309_);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
lean_inc(v___y_302_);
lean_inc(v___y_301_);
lean_inc_ref(v___y_300_);
v___x_313_ = lean_apply_14(v_f_296_, v___x_312_, v_s_297_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, lean_box(0));
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_340_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_340_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_340_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_340_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
if (lean_obj_tag(v_a_314_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_328_; 
v_a_318_ = lean_ctor_get(v_a_314_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_a_314_);
if (v_isSharedCheck_328_ == 0)
{
v___x_320_ = v_a_314_;
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v_a_314_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_328_;
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
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_325_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_323_);
v___x_325_ = v___x_316_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_339_; 
v_a_329_ = lean_ctor_get(v_a_314_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v_a_314_);
if (v_isSharedCheck_339_ == 0)
{
v___x_331_ = v_a_314_;
v_isShared_332_ = v_isSharedCheck_339_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v_a_314_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_339_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_334_);
v___x_336_ = v___x_316_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_a_341_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_313_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_313_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0___boxed(lean_object* v_f_349_, lean_object* v_s_350_, lean_object* v_a_351_, lean_object* v_b_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0(v_f_349_, v_s_350_, v_a_351_, v_b_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(lean_object* v_map_366_, lean_object* v_init_367_, lean_object* v_f_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___f_381_; lean_object* v___x_382_; 
v___f_381_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0___boxed), 16, 1);
lean_closure_set(v___f_381_, 0, v_f_368_);
lean_inc_ref(v_map_366_);
v___x_382_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v___f_381_, v_map_366_, v_init_367_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_391_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_391_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v_a_387_; lean_object* v___x_389_; 
v_a_387_ = lean_ctor_get(v_a_383_, 0);
lean_inc(v_a_387_);
lean_dec(v_a_383_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v_a_387_);
v___x_389_ = v___x_385_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_a_392_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_382_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_382_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___boxed(lean_object* v_map_400_, lean_object* v_init_401_, lean_object* v_f_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(v_map_400_, v_init_401_, v_f_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec_ref(v_map_400_);
return v_res_415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__0));
v___x_418_ = lean_unsigned_to_nat(2u);
v___x_419_ = lean_unsigned_to_nat(23u);
v___x_420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1));
v___x_421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_422_ = l_mkPanicMessageWithDecl(v___x_421_, v___x_420_, v___x_419_, v___x_418_, v___x_417_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars(lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v_toRing_437_; lean_object* v_vars_438_; lean_object* v_varMap_439_; lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v_toRing_437_ = lean_ctor_get(v_a_436_, 0);
lean_inc_ref(v_toRing_437_);
lean_dec(v_a_436_);
v_vars_438_ = lean_ctor_get(v_toRing_437_, 14);
lean_inc_ref_n(v_vars_438_, 2);
v_varMap_439_ = lean_ctor_get(v_toRing_437_, 15);
lean_inc_ref(v_varMap_439_);
lean_dec_ref(v_toRing_437_);
v___f_440_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___boxed), 15, 1);
lean_closure_set(v___f_440_, 0, v_vars_438_);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(v_varMap_439_, v___x_441_, v___f_440_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
lean_dec_ref(v_varMap_439_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_455_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_455_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_455_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_455_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_size_447_; uint8_t v___x_448_; 
v_size_447_ = lean_ctor_get(v_vars_438_, 2);
lean_inc(v_size_447_);
lean_dec_ref(v_vars_438_);
v___x_448_ = lean_nat_dec_eq(v_size_447_, v_a_443_);
lean_dec(v_a_443_);
lean_dec(v_size_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_del_object(v___x_445_);
v___x_449_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1);
v___x_450_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_449_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = lean_box(0);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_451_);
v___x_453_ = v___x_445_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec_ref(v_vars_438_);
v_a_456_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_442_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_442_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
v_a_464_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_435_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_435_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___boxed(lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars(v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2(lean_object* v_00_u03c3_485_, lean_object* v_00_u03b2_486_, lean_object* v_map_487_, lean_object* v_init_488_, lean_object* v_f_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(v_map_487_, v_init_488_, v_f_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_503_ = _args[0];
lean_object* v_00_u03b2_504_ = _args[1];
lean_object* v_map_505_ = _args[2];
lean_object* v_init_506_ = _args[3];
lean_object* v_f_507_ = _args[4];
lean_object* v___y_508_ = _args[5];
lean_object* v___y_509_ = _args[6];
lean_object* v___y_510_ = _args[7];
lean_object* v___y_511_ = _args[8];
lean_object* v___y_512_ = _args[9];
lean_object* v___y_513_ = _args[10];
lean_object* v___y_514_ = _args[11];
lean_object* v___y_515_ = _args[12];
lean_object* v___y_516_ = _args[13];
lean_object* v___y_517_ = _args[14];
lean_object* v___y_518_ = _args[15];
lean_object* v___y_519_ = _args[16];
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2(v_00_u03c3_503_, v_00_u03b2_504_, v_map_505_, v_init_506_, v_f_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_map_505_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg(lean_object* v_map_521_, lean_object* v_f_522_, lean_object* v_init_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_522_, v_map_521_, v_init_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg___boxed(lean_object* v_map_537_, lean_object* v_f_538_, lean_object* v_init_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg(v_map_537_, v_f_538_, v_init_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2(lean_object* v_00_u03c3_553_, lean_object* v_00_u03c3_554_, lean_object* v_00_u03b2_555_, lean_object* v_map_556_, lean_object* v_f_557_, lean_object* v_init_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_557_, v_map_556_, v_init_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_572_ = _args[0];
lean_object* v_00_u03c3_573_ = _args[1];
lean_object* v_00_u03b2_574_ = _args[2];
lean_object* v_map_575_ = _args[3];
lean_object* v_f_576_ = _args[4];
lean_object* v_init_577_ = _args[5];
lean_object* v___y_578_ = _args[6];
lean_object* v___y_579_ = _args[7];
lean_object* v___y_580_ = _args[8];
lean_object* v___y_581_ = _args[9];
lean_object* v___y_582_ = _args[10];
lean_object* v___y_583_ = _args[11];
lean_object* v___y_584_ = _args[12];
lean_object* v___y_585_ = _args[13];
lean_object* v___y_586_ = _args[14];
lean_object* v___y_587_ = _args[15];
lean_object* v___y_588_ = _args[16];
lean_object* v___y_589_ = _args[17];
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2(v_00_u03c3_572_, v_00_u03c3_573_, v_00_u03b2_574_, v_map_575_, v_f_576_, v_init_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3(lean_object* v_00_u03c3_591_, lean_object* v_00_u03c3_592_, lean_object* v_00_u03b1_593_, lean_object* v_00_u03b2_594_, lean_object* v_f_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_595_, v_x_596_, v_x_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03c3_611_ = _args[0];
lean_object* v_00_u03c3_612_ = _args[1];
lean_object* v_00_u03b1_613_ = _args[2];
lean_object* v_00_u03b2_614_ = _args[3];
lean_object* v_f_615_ = _args[4];
lean_object* v_x_616_ = _args[5];
lean_object* v_x_617_ = _args[6];
lean_object* v___y_618_ = _args[7];
lean_object* v___y_619_ = _args[8];
lean_object* v___y_620_ = _args[9];
lean_object* v___y_621_ = _args[10];
lean_object* v___y_622_ = _args[11];
lean_object* v___y_623_ = _args[12];
lean_object* v___y_624_ = _args[13];
lean_object* v___y_625_ = _args[14];
lean_object* v___y_626_ = _args[15];
lean_object* v___y_627_ = _args[16];
lean_object* v___y_628_ = _args[17];
lean_object* v___y_629_ = _args[18];
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3(v_00_u03c3_611_, v_00_u03c3_612_, v_00_u03b1_613_, v_00_u03b2_614_, v_f_615_, v_x_616_, v_x_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_631_, lean_object* v_00_u03b2_632_, lean_object* v_00_u03c3_633_, lean_object* v_00_u03c3_634_, lean_object* v_f_635_, lean_object* v_as_636_, size_t v_i_637_, size_t v_stop_638_, lean_object* v_b_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_635_, v_as_636_, v_i_637_, v_stop_638_, v_b_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_00_u03b1_653_ = _args[0];
lean_object* v_00_u03b2_654_ = _args[1];
lean_object* v_00_u03c3_655_ = _args[2];
lean_object* v_00_u03c3_656_ = _args[3];
lean_object* v_f_657_ = _args[4];
lean_object* v_as_658_ = _args[5];
lean_object* v_i_659_ = _args[6];
lean_object* v_stop_660_ = _args[7];
lean_object* v_b_661_ = _args[8];
lean_object* v___y_662_ = _args[9];
lean_object* v___y_663_ = _args[10];
lean_object* v___y_664_ = _args[11];
lean_object* v___y_665_ = _args[12];
lean_object* v___y_666_ = _args[13];
lean_object* v___y_667_ = _args[14];
lean_object* v___y_668_ = _args[15];
lean_object* v___y_669_ = _args[16];
lean_object* v___y_670_ = _args[17];
lean_object* v___y_671_ = _args[18];
lean_object* v___y_672_ = _args[19];
lean_object* v___y_673_ = _args[20];
_start:
{
size_t v_i_boxed_674_; size_t v_stop_boxed_675_; lean_object* v_res_676_; 
v_i_boxed_674_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_stop_boxed_675_ = lean_unbox_usize(v_stop_660_);
lean_dec(v_stop_660_);
v_res_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4(v_00_u03b1_653_, v_00_u03b2_654_, v_00_u03c3_655_, v_00_u03c3_656_, v_f_657_, v_as_658_, v_i_boxed_674_, v_stop_boxed_675_, v_b_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v_as_658_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_677_, lean_object* v_00_u03c3_678_, lean_object* v_00_u03b1_679_, lean_object* v_00_u03b2_680_, lean_object* v_f_681_, lean_object* v_keys_682_, lean_object* v_vals_683_, lean_object* v_heq_684_, lean_object* v_i_685_, lean_object* v_acc_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_681_, v_keys_682_, v_vals_683_, v_i_685_, v_acc_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_00_u03c3_700_ = _args[0];
lean_object* v_00_u03c3_701_ = _args[1];
lean_object* v_00_u03b1_702_ = _args[2];
lean_object* v_00_u03b2_703_ = _args[3];
lean_object* v_f_704_ = _args[4];
lean_object* v_keys_705_ = _args[5];
lean_object* v_vals_706_ = _args[6];
lean_object* v_heq_707_ = _args[7];
lean_object* v_i_708_ = _args[8];
lean_object* v_acc_709_ = _args[9];
lean_object* v___y_710_ = _args[10];
lean_object* v___y_711_ = _args[11];
lean_object* v___y_712_ = _args[12];
lean_object* v___y_713_ = _args[13];
lean_object* v___y_714_ = _args[14];
lean_object* v___y_715_ = _args[15];
lean_object* v___y_716_ = _args[16];
lean_object* v___y_717_ = _args[17];
lean_object* v___y_718_ = _args[18];
lean_object* v___y_719_ = _args[19];
lean_object* v___y_720_ = _args[20];
lean_object* v___y_721_ = _args[21];
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5(v_00_u03c3_700_, v_00_u03c3_701_, v_00_u03b1_702_, v_00_u03b2_703_, v_f_704_, v_keys_705_, v_vals_706_, v_heq_707_, v_i_708_, v_acc_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v_vals_706_);
lean_dec_ref(v_keys_705_);
return v_res_722_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__1));
v___x_726_ = lean_unsigned_to_nat(2u);
v___x_727_ = lean_unsigned_to_nat(29u);
v___x_728_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0));
v___x_729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_730_ = l_mkPanicMessageWithDecl(v___x_729_, v___x_728_, v___x_727_, v___x_726_, v___x_725_);
return v___x_730_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__3));
v___x_733_ = lean_unsigned_to_nat(2u);
v___x_734_ = lean_unsigned_to_nat(26u);
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0));
v___x_736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_737_ = l_mkPanicMessageWithDecl(v___x_736_, v___x_735_, v___x_734_, v___x_733_, v___x_732_);
return v___x_737_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__5));
v___x_740_ = lean_unsigned_to_nat(2u);
v___x_741_ = lean_unsigned_to_nat(27u);
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0));
v___x_743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_744_ = l_mkPanicMessageWithDecl(v___x_743_, v___x_742_, v___x_741_, v___x_740_, v___x_739_);
return v___x_744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_746_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__7));
v___x_747_ = lean_unsigned_to_nat(2u);
v___x_748_ = lean_unsigned_to_nat(28u);
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0));
v___x_750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_751_ = l_mkPanicMessageWithDecl(v___x_750_, v___x_749_, v___x_748_, v___x_747_, v___x_746_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(lean_object* v_p_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
uint8_t v___y_766_; uint8_t v___x_772_; 
v___x_772_ = l_Lean_Grind_CommRing_Poly_isSorted(v_p_752_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4);
v___x_774_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_773_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
return v___x_774_;
}
else
{
uint8_t v___x_775_; 
v___x_775_ = l_Lean_Grind_CommRing_Poly_checkCoeffs(v_p_752_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6);
v___x_777_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_776_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
return v___x_777_;
}
else
{
uint8_t v___x_778_; 
v___x_778_ = l_Lean_Grind_CommRing_Poly_checkNoUnitMon(v_p_752_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8);
v___x_780_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_779_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
return v___x_780_;
}
else
{
if (lean_obj_tag(v_p_752_) == 0)
{
v___y_766_ = v___x_778_;
goto v___jp_765_;
}
else
{
uint8_t v___x_781_; 
v___x_781_ = 0;
v___y_766_ = v___x_781_;
goto v___jp_765_;
}
}
}
}
v___jp_765_:
{
uint8_t v___x_767_; 
v___x_767_ = lean_bool_not(v___y_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2);
v___x_769_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_768_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___boxed(lean_object* v_p_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v_p_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec_ref(v_p_782_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(lean_object* v_as_x27_796_, lean_object* v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
if (lean_obj_tag(v_as_x27_796_) == 0)
{
lean_object* v___x_810_; 
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v_b_797_);
return v___x_810_;
}
else
{
lean_object* v_head_811_; lean_object* v_tail_812_; lean_object* v_p_813_; lean_object* v___x_814_; 
v_head_811_ = lean_ctor_get(v_as_x27_796_, 0);
v_tail_812_ = lean_ctor_get(v_as_x27_796_, 1);
v_p_813_ = lean_ctor_get(v_head_811_, 0);
v___x_814_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v_p_813_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec_ref_known(v___x_814_, 1);
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_add(v_b_797_, v___x_815_);
lean_dec(v_b_797_);
v_as_x27_796_ = v_tail_812_;
v_b_797_ = v___x_816_;
goto _start;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_b_797_);
v_a_818_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_814_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_814_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg___boxed(lean_object* v_as_x27_826_, lean_object* v_b_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(v_as_x27_826_, v_b_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v_as_x27_826_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis(lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v_basis_855_; lean_object* v_x_856_; lean_object* v___x_857_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v_basis_855_ = lean_ctor_get(v_a_854_, 12);
lean_inc(v_basis_855_);
lean_dec(v_a_854_);
v_x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(v_basis_855_, v_x_856_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
lean_dec(v_basis_855_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_865_; 
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; 
v_unused_866_ = lean_ctor_get(v___x_857_, 0);
lean_dec(v_unused_866_);
v___x_859_ = v___x_857_;
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
else
{
lean_dec(v___x_857_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_861_ = lean_box(0);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_861_);
v___x_863_ = v___x_859_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_a_867_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_857_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_857_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_853_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_853_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis___boxed(lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis(v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0(lean_object* v_as_896_, lean_object* v_as_x27_897_, lean_object* v_b_898_, lean_object* v_a_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(v_as_x27_897_, v_b_898_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___boxed(lean_object* v_as_913_, lean_object* v_as_x27_914_, lean_object* v_b_915_, lean_object* v_a_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0(v_as_913_, v_as_x27_914_, v_b_915_, v_a_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v_as_x27_914_);
lean_dec(v_as_913_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(lean_object* v_init_930_, lean_object* v_x_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
if (lean_obj_tag(v_x_931_) == 0)
{
lean_object* v_k_944_; lean_object* v_l_945_; lean_object* v_r_946_; lean_object* v___x_947_; 
v_k_944_ = lean_ctor_get(v_x_931_, 1);
v_l_945_ = lean_ctor_get(v_x_931_, 3);
v_r_946_ = lean_ctor_get(v_x_931_, 4);
v___x_947_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(v_init_930_, v_l_945_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_p_948_; lean_object* v___x_949_; 
lean_dec_ref_known(v___x_947_, 1);
v_p_948_ = lean_ctor_get(v_k_944_, 0);
v___x_949_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v_p_948_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v___x_950_; 
lean_dec_ref_known(v___x_949_, 1);
v___x_950_ = lean_box(0);
v_init_930_ = v___x_950_;
v_x_931_ = v_r_946_;
goto _start;
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v_a_952_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_949_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_949_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
return v___x_947_;
}
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_960_, 0, v_init_930_);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0___boxed(lean_object* v_init_962_, lean_object* v_x_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(v_init_962_, v_x_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v_x_963_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue(lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v_queue_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v_queue_991_ = lean_ctor_get(v_a_990_, 11);
lean_inc(v_queue_991_);
lean_dec(v_a_990_);
v___x_992_ = lean_box(0);
v___x_993_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(v___x_992_, v_queue_991_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec(v_queue_991_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v___x_993_, 0);
lean_dec(v_unused_1001_);
v___x_995_ = v___x_993_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_dec(v___x_993_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_992_);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_992_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_993_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_993_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_989_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_989_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue___boxed(lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue(v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_1034_, size_t v_sz_1035_, size_t v_i_1036_, lean_object* v_b_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_usize_dec_lt(v_i_1036_, v_sz_1035_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v_b_1037_);
return v___x_1051_;
}
else
{
lean_object* v_a_1052_; lean_object* v_d_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref(v_b_1037_);
v_a_1052_ = lean_array_uget_borrowed(v_as_1034_, v_i_1036_);
v_d_1053_ = lean_ctor_get(v_a_1052_, 4);
v___x_1054_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_1053_);
v___x_1055_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v___x_1054_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec_ref(v___x_1054_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; 
lean_dec_ref_known(v___x_1055_, 1);
v___x_1056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_1036_, v___x_1057_);
v_i_1036_ = v___x_1058_;
v_b_1037_ = v___x_1056_;
goto _start;
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1055_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1055_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_1068_, lean_object* v_sz_1069_, lean_object* v_i_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
size_t v_sz_boxed_1084_; size_t v_i_boxed_1085_; lean_object* v_res_1086_; 
v_sz_boxed_1084_ = lean_unbox_usize(v_sz_1069_);
lean_dec(v_sz_1069_);
v_i_boxed_1085_ = lean_unbox_usize(v_i_1070_);
lean_dec(v_i_1070_);
v_res_1086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_1068_, v_sz_boxed_1084_, v_i_boxed_1085_, v_b_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec_ref(v_as_1068_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2(lean_object* v_as_1087_, size_t v_sz_1088_, size_t v_i_1089_, lean_object* v_b_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_usize_dec_lt(v_i_1089_, v_sz_1088_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_b_1090_);
return v___x_1104_;
}
else
{
lean_object* v_a_1105_; lean_object* v_d_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec_ref(v_b_1090_);
v_a_1105_ = lean_array_uget_borrowed(v_as_1087_, v_i_1089_);
v_d_1106_ = lean_ctor_get(v_a_1105_, 4);
v___x_1107_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_1106_);
v___x_1108_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v___x_1107_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec_ref(v___x_1107_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; lean_object* v___x_1112_; 
lean_dec_ref_known(v___x_1108_, 1);
v___x_1109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_1110_ = ((size_t)1ULL);
v___x_1111_ = lean_usize_add(v_i_1089_, v___x_1110_);
v___x_1112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_1087_, v_sz_1088_, v___x_1111_, v___x_1109_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
return v___x_1112_;
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
v_a_1113_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1108_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1108_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1121_, lean_object* v_sz_1122_, lean_object* v_i_1123_, lean_object* v_b_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
size_t v_sz_boxed_1137_; size_t v_i_boxed_1138_; lean_object* v_res_1139_; 
v_sz_boxed_1137_ = lean_unbox_usize(v_sz_1122_);
lean_dec(v_sz_1122_);
v_i_boxed_1138_ = lean_unbox_usize(v_i_1123_);
lean_dec(v_i_1123_);
v_res_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2(v_as_1121_, v_sz_boxed_1137_, v_i_boxed_1138_, v_b_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec_ref(v_as_1121_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(lean_object* v_init_1140_, lean_object* v_n_1141_, lean_object* v_b_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
if (lean_obj_tag(v_n_1141_) == 0)
{
lean_object* v_cs_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; size_t v_sz_1158_; size_t v___x_1159_; lean_object* v___x_1160_; 
v_cs_1155_ = lean_ctor_get(v_n_1141_, 0);
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v_b_1142_);
v_sz_1158_ = lean_array_size(v_cs_1155_);
v___x_1159_ = ((size_t)0ULL);
v___x_1160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(v_init_1140_, v_cs_1155_, v_sz_1158_, v___x_1159_, v___x_1157_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1175_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1175_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1175_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v_fst_1165_; 
v_fst_1165_ = lean_ctor_get(v_a_1161_, 0);
if (lean_obj_tag(v_fst_1165_) == 0)
{
lean_object* v_snd_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v_snd_1166_ = lean_ctor_get(v_a_1161_, 1);
lean_inc(v_snd_1166_);
lean_dec(v_a_1161_);
v___x_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_snd_1166_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1167_);
v___x_1169_ = v___x_1163_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
else
{
lean_object* v_val_1171_; lean_object* v___x_1173_; 
lean_inc_ref(v_fst_1165_);
lean_dec(v_a_1161_);
v_val_1171_ = lean_ctor_get(v_fst_1165_, 0);
lean_inc(v_val_1171_);
lean_dec_ref_known(v_fst_1165_, 1);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v_val_1171_);
v___x_1173_ = v___x_1163_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_val_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
v_a_1176_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1160_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1160_);
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
lean_object* v_vs_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; size_t v_sz_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v_vs_1184_ = lean_ctor_get(v_n_1141_, 0);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v_b_1142_);
v_sz_1187_ = lean_array_size(v_vs_1184_);
v___x_1188_ = ((size_t)0ULL);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2(v_vs_1184_, v_sz_1187_, v___x_1188_, v___x_1186_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1204_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1204_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1204_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_fst_1194_; 
v_fst_1194_ = lean_ctor_get(v_a_1190_, 0);
if (lean_obj_tag(v_fst_1194_) == 0)
{
lean_object* v_snd_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v_snd_1195_ = lean_ctor_get(v_a_1190_, 1);
lean_inc(v_snd_1195_);
lean_dec(v_a_1190_);
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_snd_1195_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1196_);
v___x_1198_ = v___x_1192_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
else
{
lean_object* v_val_1200_; lean_object* v___x_1202_; 
lean_inc_ref(v_fst_1194_);
lean_dec(v_a_1190_);
v_val_1200_ = lean_ctor_get(v_fst_1194_, 0);
lean_inc(v_val_1200_);
lean_dec_ref_known(v_fst_1194_, 1);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v_val_1200_);
v___x_1202_ = v___x_1192_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_val_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
v_a_1205_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1189_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1189_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_1213_, lean_object* v_as_1214_, size_t v_sz_1215_, size_t v_i_1216_, lean_object* v_b_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
uint8_t v___x_1230_; 
v___x_1230_ = lean_usize_dec_lt(v_i_1216_, v_sz_1215_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_b_1217_);
return v___x_1231_;
}
else
{
lean_object* v_snd_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1266_; 
v_snd_1232_ = lean_ctor_get(v_b_1217_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_b_1217_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v_b_1217_, 0);
lean_dec(v_unused_1267_);
v___x_1234_ = v_b_1217_;
v_isShared_1235_ = v_isSharedCheck_1266_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_snd_1232_);
lean_dec(v_b_1217_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1266_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v_a_1236_; lean_object* v___x_1237_; 
v_a_1236_ = lean_array_uget_borrowed(v_as_1214_, v_i_1216_);
lean_inc(v_snd_1232_);
v___x_1237_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(v_init_1213_, v_a_1236_, v_snd_1232_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1257_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1257_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1257_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
if (lean_obj_tag(v_a_1238_) == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1242_, 0, v_a_1238_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1242_);
v___x_1244_ = v___x_1234_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_snd_1232_);
v___x_1244_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1244_);
v___x_1246_ = v___x_1240_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
lean_del_object(v___x_1240_);
lean_dec(v_snd_1232_);
v_a_1249_ = lean_ctor_get(v_a_1238_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v_a_1238_, 1);
v___x_1250_ = lean_box(0);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 1, v_a_1249_);
lean_ctor_set(v___x_1234_, 0, v___x_1250_);
v___x_1252_ = v___x_1234_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_a_1249_);
v___x_1252_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
size_t v___x_1253_; size_t v___x_1254_; 
v___x_1253_ = ((size_t)1ULL);
v___x_1254_ = lean_usize_add(v_i_1216_, v___x_1253_);
v_i_1216_ = v___x_1254_;
v_b_1217_ = v___x_1252_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_del_object(v___x_1234_);
lean_dec(v_snd_1232_);
v_a_1258_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1237_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1237_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1268_ = _args[0];
lean_object* v_as_1269_ = _args[1];
lean_object* v_sz_1270_ = _args[2];
lean_object* v_i_1271_ = _args[3];
lean_object* v_b_1272_ = _args[4];
lean_object* v___y_1273_ = _args[5];
lean_object* v___y_1274_ = _args[6];
lean_object* v___y_1275_ = _args[7];
lean_object* v___y_1276_ = _args[8];
lean_object* v___y_1277_ = _args[9];
lean_object* v___y_1278_ = _args[10];
lean_object* v___y_1279_ = _args[11];
lean_object* v___y_1280_ = _args[12];
lean_object* v___y_1281_ = _args[13];
lean_object* v___y_1282_ = _args[14];
lean_object* v___y_1283_ = _args[15];
lean_object* v___y_1284_ = _args[16];
_start:
{
size_t v_sz_boxed_1285_; size_t v_i_boxed_1286_; lean_object* v_res_1287_; 
v_sz_boxed_1285_ = lean_unbox_usize(v_sz_1270_);
lean_dec(v_sz_1270_);
v_i_boxed_1286_ = lean_unbox_usize(v_i_1271_);
lean_dec(v_i_1271_);
v_res_1287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(v_init_1268_, v_as_1269_, v_sz_boxed_1285_, v_i_boxed_1286_, v_b_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec_ref(v_as_1269_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___boxed(lean_object* v_init_1288_, lean_object* v_n_1289_, lean_object* v_b_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(v_init_1288_, v_n_1289_, v_b_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec_ref(v_n_1289_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4(lean_object* v_as_1307_, size_t v_sz_1308_, size_t v_i_1309_, lean_object* v_b_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_usize_dec_lt(v_i_1309_, v_sz_1308_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_b_1310_);
return v___x_1324_;
}
else
{
lean_object* v_a_1325_; lean_object* v_d_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec_ref(v_b_1310_);
v_a_1325_ = lean_array_uget_borrowed(v_as_1307_, v_i_1309_);
v_d_1326_ = lean_ctor_get(v_a_1325_, 4);
v___x_1327_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_1326_);
v___x_1328_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v___x_1327_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec_ref(v___x_1327_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; 
lean_dec_ref_known(v___x_1328_, 1);
v___x_1329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___closed__0));
v___x_1330_ = ((size_t)1ULL);
v___x_1331_ = lean_usize_add(v_i_1309_, v___x_1330_);
v_i_1309_ = v___x_1331_;
v_b_1310_ = v___x_1329_;
goto _start;
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
v_a_1333_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1328_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1328_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1341_, lean_object* v_sz_1342_, lean_object* v_i_1343_, lean_object* v_b_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
size_t v_sz_boxed_1357_; size_t v_i_boxed_1358_; lean_object* v_res_1359_; 
v_sz_boxed_1357_ = lean_unbox_usize(v_sz_1342_);
lean_dec(v_sz_1342_);
v_i_boxed_1358_ = lean_unbox_usize(v_i_1343_);
lean_dec(v_i_1343_);
v_res_1359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4(v_as_1341_, v_sz_boxed_1357_, v_i_boxed_1358_, v_b_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec_ref(v_as_1341_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1(lean_object* v_as_1360_, size_t v_sz_1361_, size_t v_i_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_usize_dec_lt(v_i_1362_, v_sz_1361_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v_b_1363_);
return v___x_1377_;
}
else
{
lean_object* v_a_1378_; lean_object* v_d_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_dec_ref(v_b_1363_);
v_a_1378_ = lean_array_uget_borrowed(v_as_1360_, v_i_1362_);
v_d_1379_ = lean_ctor_get(v_a_1378_, 4);
v___x_1380_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_1379_);
v___x_1381_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v___x_1380_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec_ref(v___x_1380_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; lean_object* v___x_1385_; 
lean_dec_ref_known(v___x_1381_, 1);
v___x_1382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___closed__0));
v___x_1383_ = ((size_t)1ULL);
v___x_1384_ = lean_usize_add(v_i_1362_, v___x_1383_);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4(v_as_1360_, v_sz_1361_, v___x_1384_, v___x_1382_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
return v___x_1385_;
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
v_a_1386_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1381_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1381_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1___boxed(lean_object* v_as_1394_, lean_object* v_sz_1395_, lean_object* v_i_1396_, lean_object* v_b_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
size_t v_sz_boxed_1410_; size_t v_i_boxed_1411_; lean_object* v_res_1412_; 
v_sz_boxed_1410_ = lean_unbox_usize(v_sz_1395_);
lean_dec(v_sz_1395_);
v_i_boxed_1411_ = lean_unbox_usize(v_i_1396_);
lean_dec(v_i_1396_);
v_res_1412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1(v_as_1394_, v_sz_boxed_1410_, v_i_boxed_1411_, v_b_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec_ref(v_as_1394_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(lean_object* v_t_1413_, lean_object* v_init_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_root_1427_; lean_object* v_tail_1428_; lean_object* v___x_1429_; 
v_root_1427_ = lean_ctor_get(v_t_1413_, 0);
v_tail_1428_ = lean_ctor_get(v_t_1413_, 1);
v___x_1429_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(v_init_1414_, v_root_1427_, v_init_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1466_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1466_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1466_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
if (lean_obj_tag(v_a_1430_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; 
v_a_1434_ = lean_ctor_get(v_a_1430_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v_a_1430_, 1);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v_a_1434_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; size_t v_sz_1441_; size_t v___x_1442_; lean_object* v___x_1443_; 
lean_del_object(v___x_1432_);
v_a_1438_ = lean_ctor_get(v_a_1430_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v_a_1430_, 1);
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v_a_1438_);
v_sz_1441_ = lean_array_size(v_tail_1428_);
v___x_1442_ = ((size_t)0ULL);
v___x_1443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1(v_tail_1428_, v_sz_1441_, v___x_1442_, v___x_1440_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1457_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1446_ = v___x_1443_;
v_isShared_1447_ = v_isSharedCheck_1457_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1443_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1457_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v_fst_1448_; 
v_fst_1448_ = lean_ctor_get(v_a_1444_, 0);
if (lean_obj_tag(v_fst_1448_) == 0)
{
lean_object* v_snd_1449_; lean_object* v___x_1451_; 
v_snd_1449_ = lean_ctor_get(v_a_1444_, 1);
lean_inc(v_snd_1449_);
lean_dec(v_a_1444_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v_snd_1449_);
v___x_1451_ = v___x_1446_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_snd_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
else
{
lean_object* v_val_1453_; lean_object* v___x_1455_; 
lean_inc_ref(v_fst_1448_);
lean_dec(v_a_1444_);
v_val_1453_ = lean_ctor_get(v_fst_1448_, 0);
lean_inc(v_val_1453_);
lean_dec_ref_known(v_fst_1448_, 1);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v_val_1453_);
v___x_1455_ = v___x_1446_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_val_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_a_1458_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1443_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1443_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
v_a_1467_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1429_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1429_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0___boxed(lean_object* v_t_1475_, lean_object* v_init_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(v_t_1475_, v_init_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec_ref(v_t_1475_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v_diseqs_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1502_, 1);
v_diseqs_1504_ = lean_ctor_get(v_a_1503_, 13);
lean_inc_ref(v_diseqs_1504_);
lean_dec(v_a_1503_);
v___x_1505_ = lean_box(0);
v___x_1506_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(v_diseqs_1504_, v___x_1505_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
lean_dec_ref(v_diseqs_1504_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
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
lean_ctor_set(v___x_1508_, 0, v___x_1505_);
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1505_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
else
{
return v___x_1506_;
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
v_a_1515_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1502_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1502_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___boxed(lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs(lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars(v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v___x_1549_; 
lean_dec_ref_known(v___x_1548_, 1);
v___x_1549_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis(v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1550_; 
lean_dec_ref_known(v___x_1549_, 1);
v___x_1550_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue(v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; 
lean_dec_ref_known(v___x_1550_, 1);
v___x_1551_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
return v___x_1551_;
}
else
{
return v___x_1550_;
}
}
else
{
return v___x_1549_;
}
}
else
{
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs___boxed(lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs(v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
return v_res_1564_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1567_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__1));
v___x_1568_ = lean_unsigned_to_nat(6u);
v___x_1569_ = lean_unsigned_to_nat(55u);
v___x_1570_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__0));
v___x_1571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_1572_ = l_mkPanicMessageWithDecl(v___x_1571_, v___x_1570_, v___x_1569_, v___x_1568_, v___x_1567_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(lean_object* v_upperBound_1573_, lean_object* v_a_1574_, lean_object* v_b_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
uint8_t v___x_1587_; 
v___x_1587_ = lean_nat_dec_lt(v_a_1574_, v_upperBound_1573_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
lean_dec(v_a_1574_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v_b_1575_);
return v___x_1588_;
}
else
{
lean_object* v___x_1589_; lean_object* v___y_1591_; uint8_t v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1589_ = lean_box(0);
v___x_1595_ = 0;
lean_inc(v_a_1574_);
v___x_1596_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1596_, 0, v_a_1574_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*1, v___x_1595_);
v___x_1597_ = lean_nat_dec_eq(v_a_1574_, v_a_1574_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2);
v___x_1599_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_1598_, v___x_1596_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec_ref_known(v___x_1596_, 1);
v___y_1591_ = v___x_1599_;
goto v___jp_1590_;
}
else
{
lean_object* v___x_1600_; 
v___x_1600_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs(v___x_1596_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec_ref_known(v___x_1596_, 1);
v___y_1591_ = v___x_1600_;
goto v___jp_1590_;
}
v___jp_1590_:
{
if (lean_obj_tag(v___y_1591_) == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec_ref_known(v___y_1591_, 1);
v___x_1592_ = lean_unsigned_to_nat(1u);
v___x_1593_ = lean_nat_add(v_a_1574_, v___x_1592_);
lean_dec(v_a_1574_);
v_a_1574_ = v___x_1593_;
v_b_1575_ = v___x_1589_;
goto _start;
}
else
{
lean_dec(v_a_1574_);
return v___y_1591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___boxed(lean_object* v_upperBound_1601_, lean_object* v_a_1602_, lean_object* v_b_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(v_upperBound_1601_, v_a_1602_, v_b_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec(v_upperBound_1601_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
uint8_t v_debug_1627_; 
v_debug_1627_ = lean_ctor_get_uint8(v_a_1618_, sizeof(void*)*8 + 2);
if (v_debug_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = lean_box(0);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1616_, v_a_1624_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v_rings_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v_rings_1632_ = lean_ctor_get(v_a_1631_, 0);
lean_inc_ref(v_rings_1632_);
lean_dec(v_a_1631_);
v___x_1633_ = lean_array_get_size(v_rings_1632_);
lean_dec_ref(v_rings_1632_);
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = lean_box(0);
v___x_1636_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(v___x_1633_, v___x_1634_, v___x_1635_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; 
v_unused_1644_ = lean_ctor_get(v___x_1636_, 0);
lean_dec(v_unused_1644_);
v___x_1638_ = v___x_1636_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_dec(v___x_1636_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1635_);
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1635_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
else
{
return v___x_1636_;
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1630_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1630_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInvariants___boxed(lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec(v_a_1653_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0(lean_object* v_upperBound_1665_, lean_object* v_inst_1666_, lean_object* v_R_1667_, lean_object* v_a_1668_, lean_object* v_b_1669_, lean_object* v_c_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(v_upperBound_1665_, v_a_1668_, v_b_1669_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1683_ = _args[0];
lean_object* v_inst_1684_ = _args[1];
lean_object* v_R_1685_ = _args[2];
lean_object* v_a_1686_ = _args[3];
lean_object* v_b_1687_ = _args[4];
lean_object* v_c_1688_ = _args[5];
lean_object* v___y_1689_ = _args[6];
lean_object* v___y_1690_ = _args[7];
lean_object* v___y_1691_ = _args[8];
lean_object* v___y_1692_ = _args[9];
lean_object* v___y_1693_ = _args[10];
lean_object* v___y_1694_ = _args[11];
lean_object* v___y_1695_ = _args[12];
lean_object* v___y_1696_ = _args[13];
lean_object* v___y_1697_ = _args[14];
lean_object* v___y_1698_ = _args[15];
lean_object* v___y_1699_ = _args[16];
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0(v_upperBound_1683_, v_inst_1684_, v_R_1685_, v_a_1686_, v_b_1687_, v_c_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec(v_upperBound_1683_);
return v_res_1700_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin);
}
#ifdef __cplusplus
}
#endif
