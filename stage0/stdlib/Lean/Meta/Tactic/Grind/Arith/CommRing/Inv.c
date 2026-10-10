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
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_Poly_isSorted(lean_object*);
uint8_t l_Lean_Grind_CommRing_Poly_checkCoeffs(lean_object*);
uint8_t l_Lean_Grind_CommRing_Poly_checkNoUnitMon(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object**);
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
v___x_1_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v___x_15_; lean_object* v___f_16_; lean_object* v___x_6211__overap_17_; lean_object* v___x_18_; 
v___x_15_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0);
v___f_16_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_16_, 0, v___x_15_);
v___x_6211__overap_17_ = lean_panic_fn_borrowed(v___f_16_, v_msg_2_);
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
v___x_18_ = lean_apply_12(v___x_6211__overap_17_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, lean_box(0));
return v___x_18_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2_ = stack[0].m_obj;
lean_object* v___y_3_ = stack[1].m_obj;
lean_object* v___y_4_ = stack[2].m_obj;
lean_object* v___y_5_ = stack[3].m_obj;
lean_object* v___y_6_ = stack[4].m_obj;
lean_object* v___y_7_ = stack[5].m_obj;
lean_object* v___y_8_ = stack[6].m_obj;
lean_object* v___y_9_ = stack[7].m_obj;
lean_object* v___y_10_ = stack[8].m_obj;
lean_object* v___y_11_ = stack[9].m_obj;
lean_object* v___y_12_ = stack[10].m_obj;
lean_object* v___y_13_ = stack[11].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v_msg_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___boxed(lean_object* v_msg_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v_msg_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_33_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1(lean_object* v_msg_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; lean_object* v___f_48_; lean_object* v___x_6229__overap_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0);
v___f_48_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_48_, 0, v___x_47_);
v___x_6229__overap_49_ = lean_panic_fn_borrowed(v___f_48_, v_msg_34_);
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
v___x_50_ = lean_apply_12(v___x_6229__overap_49_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
return v___x_50_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_34_ = stack[0].m_obj;
lean_object* v___y_35_ = stack[1].m_obj;
lean_object* v___y_36_ = stack[2].m_obj;
lean_object* v___y_37_ = stack[3].m_obj;
lean_object* v___y_38_ = stack[4].m_obj;
lean_object* v___y_39_ = stack[5].m_obj;
lean_object* v___y_40_ = stack[6].m_obj;
lean_object* v___y_41_ = stack[7].m_obj;
lean_object* v___y_42_ = stack[8].m_obj;
lean_object* v___y_43_ = stack[9].m_obj;
lean_object* v___y_44_ = stack[10].m_obj;
lean_object* v___y_45_ = stack[11].m_obj;
lean_object* v_res_51_;
v_res_51_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1(v_msg_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___boxed(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1(v_msg_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_65_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_69_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__2));
v___x_70_ = lean_unsigned_to_nat(6u);
v___x_71_ = lean_unsigned_to_nat(21u);
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1));
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_74_ = l_mkPanicMessageWithDecl(v___x_73_, v___x_72_, v___x_71_, v___x_70_, v___x_69_);
return v___x_74_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__4));
v___x_77_ = lean_unsigned_to_nat(6u);
v___x_78_ = lean_unsigned_to_nat(19u);
v___x_79_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1));
v___x_80_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_81_ = l_mkPanicMessageWithDecl(v___x_80_, v___x_79_, v___x_78_, v___x_77_, v___x_76_);
return v___x_81_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0(lean_object* v_vars_82_, lean_object* v___x_83_, lean_object* v_x_84_, lean_object* v_____s_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_fst_103_; lean_object* v_snd_104_; lean_object* v_size_105_; uint8_t v___x_106_; 
v_fst_103_ = lean_ctor_get(v_x_84_, 0);
v_snd_104_ = lean_ctor_get(v_x_84_, 1);
v_size_105_ = lean_ctor_get(v_vars_82_, 2);
v___x_106_ = lean_nat_dec_lt(v_snd_104_, v_size_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3);
v___x_108_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_107_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_dec_ref_known(v___x_108_, 1);
goto v___jp_98_;
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
else
{
lean_object* v___x_117_; size_t v___x_118_; size_t v___x_119_; uint8_t v___x_120_; 
v___x_117_ = l_Lean_PersistentArray_get_x21___redArg(v___x_83_, v_vars_82_, v_snd_104_);
v___x_118_ = lean_ptr_addr(v_fst_103_);
v___x_119_ = lean_ptr_addr(v___x_117_);
lean_dec(v___x_117_);
v___x_120_ = lean_usize_dec_eq(v___x_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5);
v___x_122_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1(v___x_121_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
return v___x_122_;
}
else
{
goto v___jp_98_;
}
}
v___jp_98_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_____s_85_, v___x_99_);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_vars_82_ = stack[0].m_obj;
lean_object* v___x_83_ = stack[1].m_obj;
lean_object* v_x_84_ = stack[2].m_obj;
lean_object* v_____s_85_ = stack[3].m_obj;
lean_object* v___y_86_ = stack[4].m_obj;
lean_object* v___y_87_ = stack[5].m_obj;
lean_object* v___y_88_ = stack[6].m_obj;
lean_object* v___y_89_ = stack[7].m_obj;
lean_object* v___y_90_ = stack[8].m_obj;
lean_object* v___y_91_ = stack[9].m_obj;
lean_object* v___y_92_ = stack[10].m_obj;
lean_object* v___y_93_ = stack[11].m_obj;
lean_object* v___y_94_ = stack[12].m_obj;
lean_object* v___y_95_ = stack[13].m_obj;
lean_object* v___y_96_ = stack[14].m_obj;
lean_object* v_res_123_;
v_res_123_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0(v_vars_82_, v___x_83_, v_x_84_, v_____s_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___boxed(lean_object* v_vars_124_, lean_object* v___x_125_, lean_object* v_x_126_, lean_object* v_____s_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0(v_vars_124_, v___x_125_, v_x_126_, v_____s_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v_____s_127_);
lean_dec_ref(v_x_126_);
lean_dec_ref(v___x_125_);
lean_dec_ref(v_vars_124_);
return v_res_140_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(lean_object* v_f_141_, lean_object* v_keys_142_, lean_object* v_vals_143_, lean_object* v_i_144_, lean_object* v_acc_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = lean_array_get_size(v_keys_142_);
v___x_159_ = lean_nat_dec_lt(v_i_144_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v_i_144_);
lean_dec_ref(v_f_141_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v_acc_145_);
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
else
{
lean_object* v_k_162_; lean_object* v_v_163_; lean_object* v___x_164_; 
v_k_162_ = lean_array_fget_borrowed(v_keys_142_, v_i_144_);
v_v_163_ = lean_array_fget_borrowed(v_vals_143_, v_i_144_);
lean_inc_ref(v_f_141_);
lean_inc(v___y_156_);
lean_inc_ref(v___y_155_);
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
lean_inc(v___y_148_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v_v_163_);
lean_inc(v_k_162_);
v___x_164_ = lean_apply_15(v_f_141_, v_acc_145_, v_k_162_, v_v_163_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, lean_box(0));
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
if (lean_obj_tag(v_a_165_) == 0)
{
lean_dec_ref_known(v_a_165_, 1);
lean_dec(v_i_144_);
lean_dec_ref(v_f_141_);
return v___x_164_;
}
else
{
lean_object* v_a_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec_ref_known(v___x_164_, 1);
v_a_166_ = lean_ctor_get(v_a_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v_a_165_, 1);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_add(v_i_144_, v___x_167_);
lean_dec(v_i_144_);
v_i_144_ = v___x_168_;
v_acc_145_ = v_a_166_;
goto _start;
}
}
else
{
lean_dec(v_i_144_);
lean_dec_ref(v_f_141_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_141_ = stack[0].m_obj;
lean_object* v_keys_142_ = stack[1].m_obj;
lean_object* v_vals_143_ = stack[2].m_obj;
lean_object* v_i_144_ = stack[3].m_obj;
lean_object* v_acc_145_ = stack[4].m_obj;
lean_object* v___y_146_ = stack[5].m_obj;
lean_object* v___y_147_ = stack[6].m_obj;
lean_object* v___y_148_ = stack[7].m_obj;
lean_object* v___y_149_ = stack[8].m_obj;
lean_object* v___y_150_ = stack[9].m_obj;
lean_object* v___y_151_ = stack[10].m_obj;
lean_object* v___y_152_ = stack[11].m_obj;
lean_object* v___y_153_ = stack[12].m_obj;
lean_object* v___y_154_ = stack[13].m_obj;
lean_object* v___y_155_ = stack[14].m_obj;
lean_object* v___y_156_ = stack[15].m_obj;
lean_object* v_res_170_;
v_res_170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_141_, v_keys_142_, v_vals_143_, v_i_144_, v_acc_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_f_171_ = _args[0];
lean_object* v_keys_172_ = _args[1];
lean_object* v_vals_173_ = _args[2];
lean_object* v_i_174_ = _args[3];
lean_object* v_acc_175_ = _args[4];
lean_object* v___y_176_ = _args[5];
lean_object* v___y_177_ = _args[6];
lean_object* v___y_178_ = _args[7];
lean_object* v___y_179_ = _args[8];
lean_object* v___y_180_ = _args[9];
lean_object* v___y_181_ = _args[10];
lean_object* v___y_182_ = _args[11];
lean_object* v___y_183_ = _args[12];
lean_object* v___y_184_ = _args[13];
lean_object* v___y_185_ = _args[14];
lean_object* v___y_186_ = _args[15];
lean_object* v___y_187_ = _args[16];
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_171_, v_keys_172_, v_vals_173_, v_i_174_, v_acc_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec_ref(v_vals_173_);
lean_dec_ref(v_keys_172_);
return v_res_188_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_f_189_, lean_object* v_as_190_, size_t v_i_191_, size_t v_stop_192_, lean_object* v_b_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_a_207_; lean_object* v___y_212_; uint8_t v___x_215_; 
v___x_215_ = lean_usize_dec_eq(v_i_191_, v_stop_192_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_array_uget_borrowed(v_as_190_, v_i_191_);
switch(lean_obj_tag(v___x_216_))
{
case 0:
{
lean_object* v_key_217_; lean_object* v_val_218_; lean_object* v___x_219_; 
v_key_217_ = lean_ctor_get(v___x_216_, 0);
v_val_218_ = lean_ctor_get(v___x_216_, 1);
lean_inc_ref(v_f_189_);
lean_inc(v___y_204_);
lean_inc_ref(v___y_203_);
lean_inc(v___y_202_);
lean_inc_ref(v___y_201_);
lean_inc(v___y_200_);
lean_inc_ref(v___y_199_);
lean_inc(v___y_198_);
lean_inc_ref(v___y_197_);
lean_inc(v___y_196_);
lean_inc(v___y_195_);
lean_inc_ref(v___y_194_);
lean_inc(v_val_218_);
lean_inc(v_key_217_);
v___x_219_ = lean_apply_15(v_f_189_, v_b_193_, v_key_217_, v_val_218_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, lean_box(0));
v___y_212_ = v___x_219_;
goto v___jp_211_;
}
case 1:
{
lean_object* v_node_220_; lean_object* v___x_221_; 
v_node_220_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_node_220_);
lean_inc_ref(v_f_189_);
v___x_221_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_189_, v_node_220_, v_b_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
v___y_212_ = v___x_221_;
goto v___jp_211_;
}
default: 
{
v_a_207_ = v_b_193_;
goto v___jp_206_;
}
}
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec_ref(v_f_189_);
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v_b_193_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
v___jp_206_:
{
size_t v___x_208_; size_t v___x_209_; 
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_add(v_i_191_, v___x_208_);
v_i_191_ = v___x_209_;
v_b_193_ = v_a_207_;
goto _start;
}
v___jp_211_:
{
if (lean_obj_tag(v___y_212_) == 0)
{
lean_object* v_a_213_; 
v_a_213_ = lean_ctor_get(v___y_212_, 0);
if (lean_obj_tag(v_a_213_) == 0)
{
lean_dec_ref(v_f_189_);
return v___y_212_;
}
else
{
lean_object* v_a_214_; 
lean_inc_ref(v_a_213_);
lean_dec_ref_known(v___y_212_, 1);
v_a_214_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v_a_213_, 1);
v_a_207_ = v_a_214_;
goto v___jp_206_;
}
}
else
{
lean_dec_ref(v_f_189_);
return v___y_212_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_189_ = stack[0].m_obj;
lean_object* v_as_190_ = stack[1].m_obj;
size_t v_i_191_ = stack[2].m_num;
size_t v_stop_192_ = stack[3].m_num;
lean_object* v_b_193_ = stack[4].m_obj;
lean_object* v___y_194_ = stack[5].m_obj;
lean_object* v___y_195_ = stack[6].m_obj;
lean_object* v___y_196_ = stack[7].m_obj;
lean_object* v___y_197_ = stack[8].m_obj;
lean_object* v___y_198_ = stack[9].m_obj;
lean_object* v___y_199_ = stack[10].m_obj;
lean_object* v___y_200_ = stack[11].m_obj;
lean_object* v___y_201_ = stack[12].m_obj;
lean_object* v___y_202_ = stack[13].m_obj;
lean_object* v___y_203_ = stack[14].m_obj;
lean_object* v___y_204_ = stack[15].m_obj;
lean_object* v_res_224_;
v_res_224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_189_, v_as_190_, v_i_191_, v_stop_192_, v_b_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
stack->m_obj
 = v_res_224_;
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(lean_object* v_f_225_, lean_object* v_x_226_, lean_object* v_x_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v_es_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_254_; 
v_es_240_ = lean_ctor_get(v_x_226_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_254_ == 0)
{
v___x_242_ = v_x_226_;
v_isShared_243_ = v_isSharedCheck_254_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_es_240_);
lean_dec(v_x_226_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_254_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_array_get_size(v_es_240_);
v___x_246_ = lean_nat_dec_lt(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_248_; 
lean_dec_ref(v_es_240_);
lean_dec_ref(v_f_225_);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 1);
lean_ctor_set(v___x_242_, 0, v_x_227_);
v___x_248_ = v___x_242_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_x_227_);
v___x_248_ = v_reuseFailAlloc_250_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
else
{
size_t v___x_251_; size_t v___x_252_; lean_object* v___x_253_; 
lean_del_object(v___x_242_);
v___x_251_ = ((size_t)0ULL);
v___x_252_ = lean_usize_of_nat(v___x_245_);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_225_, v_es_240_, v___x_251_, v___x_252_, v_x_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec_ref(v_es_240_);
return v___x_253_;
}
}
}
else
{
lean_object* v_ks_255_; lean_object* v_vs_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_ks_255_ = lean_ctor_get(v_x_226_, 0);
lean_inc_ref(v_ks_255_);
v_vs_256_ = lean_ctor_get(v_x_226_, 1);
lean_inc_ref(v_vs_256_);
lean_dec_ref_known(v_x_226_, 2);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_225_, v_ks_255_, v_vs_256_, v___x_257_, v_x_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec_ref(v_vs_256_);
lean_dec_ref(v_ks_255_);
return v___x_258_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_225_ = stack[0].m_obj;
lean_object* v_x_226_ = stack[1].m_obj;
lean_object* v_x_227_ = stack[2].m_obj;
lean_object* v___y_228_ = stack[3].m_obj;
lean_object* v___y_229_ = stack[4].m_obj;
lean_object* v___y_230_ = stack[5].m_obj;
lean_object* v___y_231_ = stack[6].m_obj;
lean_object* v___y_232_ = stack[7].m_obj;
lean_object* v___y_233_ = stack[8].m_obj;
lean_object* v___y_234_ = stack[9].m_obj;
lean_object* v___y_235_ = stack[10].m_obj;
lean_object* v___y_236_ = stack[11].m_obj;
lean_object* v___y_237_ = stack[12].m_obj;
lean_object* v___y_238_ = stack[13].m_obj;
lean_object* v_res_259_;
v_res_259_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_225_, v_x_226_, v_x_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_f_260_, lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_260_, v_x_261_, v_x_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_f_276_ = _args[0];
lean_object* v_as_277_ = _args[1];
lean_object* v_i_278_ = _args[2];
lean_object* v_stop_279_ = _args[3];
lean_object* v_b_280_ = _args[4];
lean_object* v___y_281_ = _args[5];
lean_object* v___y_282_ = _args[6];
lean_object* v___y_283_ = _args[7];
lean_object* v___y_284_ = _args[8];
lean_object* v___y_285_ = _args[9];
lean_object* v___y_286_ = _args[10];
lean_object* v___y_287_ = _args[11];
lean_object* v___y_288_ = _args[12];
lean_object* v___y_289_ = _args[13];
lean_object* v___y_290_ = _args[14];
lean_object* v___y_291_ = _args[15];
lean_object* v___y_292_ = _args[16];
_start:
{
size_t v_i_boxed_293_; size_t v_stop_boxed_294_; lean_object* v_res_295_; 
v_i_boxed_293_ = lean_unbox_usize(v_i_278_);
lean_dec(v_i_278_);
v_stop_boxed_294_ = lean_unbox_usize(v_stop_279_);
lean_dec(v_stop_279_);
v_res_295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_276_, v_as_277_, v_i_boxed_293_, v_stop_boxed_294_, v_b_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec_ref(v_as_277_);
return v_res_295_;
}
}
lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0(lean_object* v_f_296_, lean_object* v_s_297_, lean_object* v_a_298_, lean_object* v_b_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
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
LEAN_EXPORT void l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_296_ = stack[0].m_obj;
lean_object* v_s_297_ = stack[1].m_obj;
lean_object* v_a_298_ = stack[2].m_obj;
lean_object* v_b_299_ = stack[3].m_obj;
lean_object* v___y_300_ = stack[4].m_obj;
lean_object* v___y_301_ = stack[5].m_obj;
lean_object* v___y_302_ = stack[6].m_obj;
lean_object* v___y_303_ = stack[7].m_obj;
lean_object* v___y_304_ = stack[8].m_obj;
lean_object* v___y_305_ = stack[9].m_obj;
lean_object* v___y_306_ = stack[10].m_obj;
lean_object* v___y_307_ = stack[11].m_obj;
lean_object* v___y_308_ = stack[12].m_obj;
lean_object* v___y_309_ = stack[13].m_obj;
lean_object* v___y_310_ = stack[14].m_obj;
lean_object* v_res_349_;
v_res_349_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0(v_f_296_, v_s_297_, v_a_298_, v_b_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0___boxed(lean_object* v_f_350_, lean_object* v_s_351_, lean_object* v_a_352_, lean_object* v_b_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0(v_f_350_, v_s_351_, v_a_352_, v_b_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_366_;
}
}
lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(lean_object* v_map_367_, lean_object* v_init_368_, lean_object* v_f_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___f_382_; lean_object* v___x_383_; 
v___f_382_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0___boxed), 16, 1);
lean_closure_set(v___f_382_, 0, v_f_369_);
lean_inc_ref(v_map_367_);
v___x_383_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v___f_382_, v_map_367_, v_init_368_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_392_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_392_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v_a_388_; lean_object* v___x_390_; 
v_a_388_ = lean_ctor_get(v_a_384_, 0);
lean_inc(v_a_388_);
lean_dec(v_a_384_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v_a_388_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
v_a_393_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_383_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_383_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_367_ = stack[0].m_obj;
lean_object* v_init_368_ = stack[1].m_obj;
lean_object* v_f_369_ = stack[2].m_obj;
lean_object* v___y_370_ = stack[3].m_obj;
lean_object* v___y_371_ = stack[4].m_obj;
lean_object* v___y_372_ = stack[5].m_obj;
lean_object* v___y_373_ = stack[6].m_obj;
lean_object* v___y_374_ = stack[7].m_obj;
lean_object* v___y_375_ = stack[8].m_obj;
lean_object* v___y_376_ = stack[9].m_obj;
lean_object* v___y_377_ = stack[10].m_obj;
lean_object* v___y_378_ = stack[11].m_obj;
lean_object* v___y_379_ = stack[12].m_obj;
lean_object* v___y_380_ = stack[13].m_obj;
lean_object* v_res_401_;
v_res_401_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(v_map_367_, v_init_368_, v_f_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___boxed(lean_object* v_map_402_, lean_object* v_init_403_, lean_object* v_f_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(v_map_402_, v_init_403_, v_f_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec_ref(v_map_402_);
return v_res_417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__0));
v___x_420_ = lean_unsigned_to_nat(2u);
v___x_421_ = lean_unsigned_to_nat(23u);
v___x_422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1));
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_424_ = l_mkPanicMessageWithDecl(v___x_423_, v___x_422_, v___x_421_, v___x_420_, v___x_419_);
return v___x_424_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars(lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = l_Lean_instInhabitedExpr;
v___x_438_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_425_, v_a_426_, v_a_434_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v_toRingState_440_; lean_object* v_vars_441_; lean_object* v_varMap_442_; lean_object* v___f_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v_toRingState_440_ = lean_ctor_get(v_a_439_, 0);
lean_inc_ref(v_toRingState_440_);
lean_dec(v_a_439_);
v_vars_441_ = lean_ctor_get(v_toRingState_440_, 0);
lean_inc_ref_n(v_vars_441_, 2);
v_varMap_442_ = lean_ctor_get(v_toRingState_440_, 1);
lean_inc_ref(v_varMap_442_);
lean_dec_ref(v_toRingState_440_);
v___f_443_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___boxed), 16, 2);
lean_closure_set(v___f_443_, 0, v_vars_441_);
lean_closure_set(v___f_443_, 1, v___x_437_);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(v_varMap_442_, v___x_444_, v___f_443_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec_ref(v_varMap_442_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_458_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_458_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_458_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_458_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v_size_450_; uint8_t v___x_451_; 
v_size_450_ = lean_ctor_get(v_vars_441_, 2);
lean_inc(v_size_450_);
lean_dec_ref(v_vars_441_);
v___x_451_ = lean_nat_dec_eq(v_size_450_, v_a_446_);
lean_dec(v_a_446_);
lean_dec(v_size_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_del_object(v___x_448_);
v___x_452_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1);
v___x_453_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_452_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = lean_box(0);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_454_);
v___x_456_ = v___x_448_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref(v_vars_441_);
v_a_459_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_445_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_445_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
v_a_467_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_438_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_438_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_425_ = stack[0].m_obj;
lean_object* v_a_426_ = stack[1].m_obj;
lean_object* v_a_427_ = stack[2].m_obj;
lean_object* v_a_428_ = stack[3].m_obj;
lean_object* v_a_429_ = stack[4].m_obj;
lean_object* v_a_430_ = stack[5].m_obj;
lean_object* v_a_431_ = stack[6].m_obj;
lean_object* v_a_432_ = stack[7].m_obj;
lean_object* v_a_433_ = stack[8].m_obj;
lean_object* v_a_434_ = stack[9].m_obj;
lean_object* v_a_435_ = stack[10].m_obj;
lean_object* v_res_475_;
v_res_475_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars(v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___boxed(lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars(v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
return v_res_488_;
}
}
lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2(lean_object* v_00_u03c3_489_, lean_object* v_00_u03b2_490_, lean_object* v_map_491_, lean_object* v_init_492_, lean_object* v_f_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(v_map_491_, v_init_492_, v_f_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v___x_506_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_491_ = stack[2].m_obj;
lean_object* v_init_492_ = stack[3].m_obj;
lean_object* v_f_493_ = stack[4].m_obj;
lean_object* v___y_494_ = stack[5].m_obj;
lean_object* v___y_495_ = stack[6].m_obj;
lean_object* v___y_496_ = stack[7].m_obj;
lean_object* v___y_497_ = stack[8].m_obj;
lean_object* v___y_498_ = stack[9].m_obj;
lean_object* v___y_499_ = stack[10].m_obj;
lean_object* v___y_500_ = stack[11].m_obj;
lean_object* v___y_501_ = stack[12].m_obj;
lean_object* v___y_502_ = stack[13].m_obj;
lean_object* v___y_503_ = stack[14].m_obj;
lean_object* v___y_504_ = stack[15].m_obj;
lean_object* v_res_507_;
v_res_507_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2(lean_box(0), lean_box(0), v_map_491_, v_init_492_, v_f_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_508_ = _args[0];
lean_object* v_00_u03b2_509_ = _args[1];
lean_object* v_map_510_ = _args[2];
lean_object* v_init_511_ = _args[3];
lean_object* v_f_512_ = _args[4];
lean_object* v___y_513_ = _args[5];
lean_object* v___y_514_ = _args[6];
lean_object* v___y_515_ = _args[7];
lean_object* v___y_516_ = _args[8];
lean_object* v___y_517_ = _args[9];
lean_object* v___y_518_ = _args[10];
lean_object* v___y_519_ = _args[11];
lean_object* v___y_520_ = _args[12];
lean_object* v___y_521_ = _args[13];
lean_object* v___y_522_ = _args[14];
lean_object* v___y_523_ = _args[15];
lean_object* v___y_524_ = _args[16];
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2(v_00_u03c3_508_, v_00_u03b2_509_, v_map_510_, v_init_511_, v_f_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v_map_510_);
return v_res_525_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg(lean_object* v_map_526_, lean_object* v_f_527_, lean_object* v_init_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_527_, v_map_526_, v_init_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
return v___x_541_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_526_ = stack[0].m_obj;
lean_object* v_f_527_ = stack[1].m_obj;
lean_object* v_init_528_ = stack[2].m_obj;
lean_object* v___y_529_ = stack[3].m_obj;
lean_object* v___y_530_ = stack[4].m_obj;
lean_object* v___y_531_ = stack[5].m_obj;
lean_object* v___y_532_ = stack[6].m_obj;
lean_object* v___y_533_ = stack[7].m_obj;
lean_object* v___y_534_ = stack[8].m_obj;
lean_object* v___y_535_ = stack[9].m_obj;
lean_object* v___y_536_ = stack[10].m_obj;
lean_object* v___y_537_ = stack[11].m_obj;
lean_object* v___y_538_ = stack[12].m_obj;
lean_object* v___y_539_ = stack[13].m_obj;
lean_object* v_res_542_;
v_res_542_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg(v_map_526_, v_f_527_, v_init_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
stack->m_obj
 = v_res_542_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg___boxed(lean_object* v_map_543_, lean_object* v_f_544_, lean_object* v_init_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg(v_map_543_, v_f_544_, v_init_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
return v_res_558_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2(lean_object* v_00_u03c3_559_, lean_object* v_00_u03c3_560_, lean_object* v_00_u03b2_561_, lean_object* v_map_562_, lean_object* v_f_563_, lean_object* v_init_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_563_, v_map_562_, v_init_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
return v___x_577_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_562_ = stack[3].m_obj;
lean_object* v_f_563_ = stack[4].m_obj;
lean_object* v_init_564_ = stack[5].m_obj;
lean_object* v___y_565_ = stack[6].m_obj;
lean_object* v___y_566_ = stack[7].m_obj;
lean_object* v___y_567_ = stack[8].m_obj;
lean_object* v___y_568_ = stack[9].m_obj;
lean_object* v___y_569_ = stack[10].m_obj;
lean_object* v___y_570_ = stack[11].m_obj;
lean_object* v___y_571_ = stack[12].m_obj;
lean_object* v___y_572_ = stack[13].m_obj;
lean_object* v___y_573_ = stack[14].m_obj;
lean_object* v___y_574_ = stack[15].m_obj;
lean_object* v___y_575_ = stack[16].m_obj;
lean_object* v_res_578_;
v_res_578_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2(lean_box(0), lean_box(0), lean_box(0), v_map_562_, v_f_563_, v_init_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_579_ = _args[0];
lean_object* v_00_u03c3_580_ = _args[1];
lean_object* v_00_u03b2_581_ = _args[2];
lean_object* v_map_582_ = _args[3];
lean_object* v_f_583_ = _args[4];
lean_object* v_init_584_ = _args[5];
lean_object* v___y_585_ = _args[6];
lean_object* v___y_586_ = _args[7];
lean_object* v___y_587_ = _args[8];
lean_object* v___y_588_ = _args[9];
lean_object* v___y_589_ = _args[10];
lean_object* v___y_590_ = _args[11];
lean_object* v___y_591_ = _args[12];
lean_object* v___y_592_ = _args[13];
lean_object* v___y_593_ = _args[14];
lean_object* v___y_594_ = _args[15];
lean_object* v___y_595_ = _args[16];
lean_object* v___y_596_ = _args[17];
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2(v_00_u03c3_579_, v_00_u03c3_580_, v_00_u03b2_581_, v_map_582_, v_f_583_, v_init_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_597_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3(lean_object* v_00_u03c3_598_, lean_object* v_00_u03c3_599_, lean_object* v_00_u03b1_600_, lean_object* v_00_u03b2_601_, lean_object* v_f_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_602_, v_x_603_, v_x_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_617_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_602_ = stack[4].m_obj;
lean_object* v_x_603_ = stack[5].m_obj;
lean_object* v_x_604_ = stack[6].m_obj;
lean_object* v___y_605_ = stack[7].m_obj;
lean_object* v___y_606_ = stack[8].m_obj;
lean_object* v___y_607_ = stack[9].m_obj;
lean_object* v___y_608_ = stack[10].m_obj;
lean_object* v___y_609_ = stack[11].m_obj;
lean_object* v___y_610_ = stack[12].m_obj;
lean_object* v___y_611_ = stack[13].m_obj;
lean_object* v___y_612_ = stack[14].m_obj;
lean_object* v___y_613_ = stack[15].m_obj;
lean_object* v___y_614_ = stack[16].m_obj;
lean_object* v___y_615_ = stack[17].m_obj;
lean_object* v_res_618_;
v_res_618_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_f_602_, v_x_603_, v_x_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03c3_619_ = _args[0];
lean_object* v_00_u03c3_620_ = _args[1];
lean_object* v_00_u03b1_621_ = _args[2];
lean_object* v_00_u03b2_622_ = _args[3];
lean_object* v_f_623_ = _args[4];
lean_object* v_x_624_ = _args[5];
lean_object* v_x_625_ = _args[6];
lean_object* v___y_626_ = _args[7];
lean_object* v___y_627_ = _args[8];
lean_object* v___y_628_ = _args[9];
lean_object* v___y_629_ = _args[10];
lean_object* v___y_630_ = _args[11];
lean_object* v___y_631_ = _args[12];
lean_object* v___y_632_ = _args[13];
lean_object* v___y_633_ = _args[14];
lean_object* v___y_634_ = _args[15];
lean_object* v___y_635_ = _args[16];
lean_object* v___y_636_ = _args[17];
lean_object* v___y_637_ = _args[18];
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3(v_00_u03c3_619_, v_00_u03c3_620_, v_00_u03b1_621_, v_00_u03b2_622_, v_f_623_, v_x_624_, v_x_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
return v_res_638_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_639_, lean_object* v_00_u03b2_640_, lean_object* v_00_u03c3_641_, lean_object* v_00_u03c3_642_, lean_object* v_f_643_, lean_object* v_as_644_, size_t v_i_645_, size_t v_stop_646_, lean_object* v_b_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_643_, v_as_644_, v_i_645_, v_stop_646_, v_b_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
return v___x_660_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_643_ = stack[4].m_obj;
lean_object* v_as_644_ = stack[5].m_obj;
size_t v_i_645_ = stack[6].m_num;
size_t v_stop_646_ = stack[7].m_num;
lean_object* v_b_647_ = stack[8].m_obj;
lean_object* v___y_648_ = stack[9].m_obj;
lean_object* v___y_649_ = stack[10].m_obj;
lean_object* v___y_650_ = stack[11].m_obj;
lean_object* v___y_651_ = stack[12].m_obj;
lean_object* v___y_652_ = stack[13].m_obj;
lean_object* v___y_653_ = stack[14].m_obj;
lean_object* v___y_654_ = stack[15].m_obj;
lean_object* v___y_655_ = stack[16].m_obj;
lean_object* v___y_656_ = stack[17].m_obj;
lean_object* v___y_657_ = stack[18].m_obj;
lean_object* v___y_658_ = stack[19].m_obj;
lean_object* v_res_661_;
v_res_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_f_643_, v_as_644_, v_i_645_, v_stop_646_, v_b_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
stack->m_obj
 = v_res_661_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_00_u03b1_662_ = _args[0];
lean_object* v_00_u03b2_663_ = _args[1];
lean_object* v_00_u03c3_664_ = _args[2];
lean_object* v_00_u03c3_665_ = _args[3];
lean_object* v_f_666_ = _args[4];
lean_object* v_as_667_ = _args[5];
lean_object* v_i_668_ = _args[6];
lean_object* v_stop_669_ = _args[7];
lean_object* v_b_670_ = _args[8];
lean_object* v___y_671_ = _args[9];
lean_object* v___y_672_ = _args[10];
lean_object* v___y_673_ = _args[11];
lean_object* v___y_674_ = _args[12];
lean_object* v___y_675_ = _args[13];
lean_object* v___y_676_ = _args[14];
lean_object* v___y_677_ = _args[15];
lean_object* v___y_678_ = _args[16];
lean_object* v___y_679_ = _args[17];
lean_object* v___y_680_ = _args[18];
lean_object* v___y_681_ = _args[19];
lean_object* v___y_682_ = _args[20];
_start:
{
size_t v_i_boxed_683_; size_t v_stop_boxed_684_; lean_object* v_res_685_; 
v_i_boxed_683_ = lean_unbox_usize(v_i_668_);
lean_dec(v_i_668_);
v_stop_boxed_684_ = lean_unbox_usize(v_stop_669_);
lean_dec(v_stop_669_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4(v_00_u03b1_662_, v_00_u03b2_663_, v_00_u03c3_664_, v_00_u03c3_665_, v_f_666_, v_as_667_, v_i_boxed_683_, v_stop_boxed_684_, v_b_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec_ref(v_as_667_);
return v_res_685_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_686_, lean_object* v_00_u03c3_687_, lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_f_690_, lean_object* v_keys_691_, lean_object* v_vals_692_, lean_object* v_heq_693_, lean_object* v_i_694_, lean_object* v_acc_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_690_, v_keys_691_, v_vals_692_, v_i_694_, v_acc_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_708_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_690_ = stack[4].m_obj;
lean_object* v_keys_691_ = stack[5].m_obj;
lean_object* v_vals_692_ = stack[6].m_obj;
lean_object* v_i_694_ = stack[8].m_obj;
lean_object* v_acc_695_ = stack[9].m_obj;
lean_object* v___y_696_ = stack[10].m_obj;
lean_object* v___y_697_ = stack[11].m_obj;
lean_object* v___y_698_ = stack[12].m_obj;
lean_object* v___y_699_ = stack[13].m_obj;
lean_object* v___y_700_ = stack[14].m_obj;
lean_object* v___y_701_ = stack[15].m_obj;
lean_object* v___y_702_ = stack[16].m_obj;
lean_object* v___y_703_ = stack[17].m_obj;
lean_object* v___y_704_ = stack[18].m_obj;
lean_object* v___y_705_ = stack[19].m_obj;
lean_object* v___y_706_ = stack[20].m_obj;
lean_object* v_res_709_;
v_res_709_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_f_690_, v_keys_691_, v_vals_692_, lean_box(0), v_i_694_, v_acc_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
stack->m_obj
 = v_res_709_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_00_u03c3_710_ = _args[0];
lean_object* v_00_u03c3_711_ = _args[1];
lean_object* v_00_u03b1_712_ = _args[2];
lean_object* v_00_u03b2_713_ = _args[3];
lean_object* v_f_714_ = _args[4];
lean_object* v_keys_715_ = _args[5];
lean_object* v_vals_716_ = _args[6];
lean_object* v_heq_717_ = _args[7];
lean_object* v_i_718_ = _args[8];
lean_object* v_acc_719_ = _args[9];
lean_object* v___y_720_ = _args[10];
lean_object* v___y_721_ = _args[11];
lean_object* v___y_722_ = _args[12];
lean_object* v___y_723_ = _args[13];
lean_object* v___y_724_ = _args[14];
lean_object* v___y_725_ = _args[15];
lean_object* v___y_726_ = _args[16];
lean_object* v___y_727_ = _args[17];
lean_object* v___y_728_ = _args[18];
lean_object* v___y_729_ = _args[19];
lean_object* v___y_730_ = _args[20];
lean_object* v___y_731_ = _args[21];
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5(v_00_u03c3_710_, v_00_u03c3_711_, v_00_u03b1_712_, v_00_u03b2_713_, v_f_714_, v_keys_715_, v_vals_716_, v_heq_717_, v_i_718_, v_acc_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec_ref(v_vals_716_);
lean_dec_ref(v_keys_715_);
return v_res_732_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__1));
v___x_736_ = lean_unsigned_to_nat(2u);
v___x_737_ = lean_unsigned_to_nat(29u);
v___x_738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0));
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_740_ = l_mkPanicMessageWithDecl(v___x_739_, v___x_738_, v___x_737_, v___x_736_, v___x_735_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__3));
v___x_743_ = lean_unsigned_to_nat(2u);
v___x_744_ = lean_unsigned_to_nat(26u);
v___x_745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0));
v___x_746_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_747_ = l_mkPanicMessageWithDecl(v___x_746_, v___x_745_, v___x_744_, v___x_743_, v___x_742_);
return v___x_747_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__5));
v___x_750_ = lean_unsigned_to_nat(2u);
v___x_751_ = lean_unsigned_to_nat(27u);
v___x_752_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0));
v___x_753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_754_ = l_mkPanicMessageWithDecl(v___x_753_, v___x_752_, v___x_751_, v___x_750_, v___x_749_);
return v___x_754_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__7));
v___x_757_ = lean_unsigned_to_nat(2u);
v___x_758_ = lean_unsigned_to_nat(28u);
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0));
v___x_760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_761_ = l_mkPanicMessageWithDecl(v___x_760_, v___x_759_, v___x_758_, v___x_757_, v___x_756_);
return v___x_761_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(lean_object* v_p_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = l_Lean_Grind_CommRing_Poly_isSorted(v_p_762_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4);
v___x_780_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_779_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
return v___x_780_;
}
else
{
uint8_t v___x_781_; 
v___x_781_ = l_Lean_Grind_CommRing_Poly_checkCoeffs(v_p_762_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6);
v___x_783_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_782_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
return v___x_783_;
}
else
{
uint8_t v___x_784_; 
v___x_784_ = l_Lean_Grind_CommRing_Poly_checkNoUnitMon(v_p_762_);
if (v___x_784_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8);
v___x_789_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_788_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
return v___x_789_;
}
else
{
if (lean_obj_tag(v_p_762_) == 0)
{
if (v___x_784_ == 0)
{
goto v___jp_785_;
}
else
{
goto v___jp_775_;
}
}
else
{
goto v___jp_785_;
}
}
v___jp_785_:
{
if (v___x_784_ == 0)
{
goto v___jp_775_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_box(0);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
}
}
}
v___jp_775_:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2);
v___x_777_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_776_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
return v___x_777_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_762_ = stack[0].m_obj;
lean_object* v_a_763_ = stack[1].m_obj;
lean_object* v_a_764_ = stack[2].m_obj;
lean_object* v_a_765_ = stack[3].m_obj;
lean_object* v_a_766_ = stack[4].m_obj;
lean_object* v_a_767_ = stack[5].m_obj;
lean_object* v_a_768_ = stack[6].m_obj;
lean_object* v_a_769_ = stack[7].m_obj;
lean_object* v_a_770_ = stack[8].m_obj;
lean_object* v_a_771_ = stack[9].m_obj;
lean_object* v_a_772_ = stack[10].m_obj;
lean_object* v_a_773_ = stack[11].m_obj;
lean_object* v_res_790_;
v_res_790_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v_p_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
stack->m_obj
 = v_res_790_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___boxed(lean_object* v_p_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v_p_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec_ref(v_p_791_);
return v_res_804_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(lean_object* v_as_x27_805_, lean_object* v_b_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
if (lean_obj_tag(v_as_x27_805_) == 0)
{
lean_object* v___x_819_; 
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v_b_806_);
return v___x_819_;
}
else
{
lean_object* v_head_820_; lean_object* v_tail_821_; lean_object* v_p_822_; lean_object* v___x_823_; 
v_head_820_ = lean_ctor_get(v_as_x27_805_, 0);
v_tail_821_ = lean_ctor_get(v_as_x27_805_, 1);
v_p_822_ = lean_ctor_get(v_head_820_, 0);
v___x_823_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v_p_822_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec_ref_known(v___x_823_, 1);
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_add(v_b_806_, v___x_824_);
lean_dec(v_b_806_);
v_as_x27_805_ = v_tail_821_;
v_b_806_ = v___x_825_;
goto _start;
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_b_806_);
v_a_827_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_823_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_823_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_805_ = stack[0].m_obj;
lean_object* v_b_806_ = stack[1].m_obj;
lean_object* v___y_807_ = stack[2].m_obj;
lean_object* v___y_808_ = stack[3].m_obj;
lean_object* v___y_809_ = stack[4].m_obj;
lean_object* v___y_810_ = stack[5].m_obj;
lean_object* v___y_811_ = stack[6].m_obj;
lean_object* v___y_812_ = stack[7].m_obj;
lean_object* v___y_813_ = stack[8].m_obj;
lean_object* v___y_814_ = stack[9].m_obj;
lean_object* v___y_815_ = stack[10].m_obj;
lean_object* v___y_816_ = stack[11].m_obj;
lean_object* v___y_817_ = stack[12].m_obj;
lean_object* v_res_835_;
v_res_835_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(v_as_x27_805_, v_b_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
stack->m_obj
 = v_res_835_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg___boxed(lean_object* v_as_x27_836_, lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(v_as_x27_836_, v_b_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v_as_x27_836_);
return v_res_850_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis(lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_x_863_; lean_object* v___x_864_; 
v_x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_851_, v_a_852_, v_a_860_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v_basis_866_; lean_object* v___x_867_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
v_basis_866_ = lean_ctor_get(v_a_865_, 5);
lean_inc(v_basis_866_);
lean_dec(v_a_865_);
v___x_867_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(v_basis_866_, v_x_863_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_basis_866_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_875_; 
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; 
v_unused_876_ = lean_ctor_get(v___x_867_, 0);
lean_dec(v_unused_876_);
v___x_869_ = v___x_867_;
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
else
{
lean_dec(v___x_867_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = lean_box(0);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_867_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_867_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_a_885_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_864_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_864_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_851_ = stack[0].m_obj;
lean_object* v_a_852_ = stack[1].m_obj;
lean_object* v_a_853_ = stack[2].m_obj;
lean_object* v_a_854_ = stack[3].m_obj;
lean_object* v_a_855_ = stack[4].m_obj;
lean_object* v_a_856_ = stack[5].m_obj;
lean_object* v_a_857_ = stack[6].m_obj;
lean_object* v_a_858_ = stack[7].m_obj;
lean_object* v_a_859_ = stack[8].m_obj;
lean_object* v_a_860_ = stack[9].m_obj;
lean_object* v_a_861_ = stack[10].m_obj;
lean_object* v_res_893_;
v_res_893_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis(v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
stack->m_obj
 = v_res_893_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis___boxed(lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis(v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
return v_res_906_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0(lean_object* v_as_907_, lean_object* v_as_x27_908_, lean_object* v_b_909_, lean_object* v_a_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(v_as_x27_908_, v_b_909_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_923_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_907_ = stack[0].m_obj;
lean_object* v_as_x27_908_ = stack[1].m_obj;
lean_object* v_b_909_ = stack[2].m_obj;
lean_object* v___y_911_ = stack[4].m_obj;
lean_object* v___y_912_ = stack[5].m_obj;
lean_object* v___y_913_ = stack[6].m_obj;
lean_object* v___y_914_ = stack[7].m_obj;
lean_object* v___y_915_ = stack[8].m_obj;
lean_object* v___y_916_ = stack[9].m_obj;
lean_object* v___y_917_ = stack[10].m_obj;
lean_object* v___y_918_ = stack[11].m_obj;
lean_object* v___y_919_ = stack[12].m_obj;
lean_object* v___y_920_ = stack[13].m_obj;
lean_object* v___y_921_ = stack[14].m_obj;
lean_object* v_res_924_;
v_res_924_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0(v_as_907_, v_as_x27_908_, v_b_909_, lean_box(0), v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___boxed(lean_object* v_as_925_, lean_object* v_as_x27_926_, lean_object* v_b_927_, lean_object* v_a_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0(v_as_925_, v_as_x27_926_, v_b_927_, v_a_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v_as_x27_926_);
lean_dec(v_as_925_);
return v_res_941_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(lean_object* v_init_942_, lean_object* v_x_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_object* v_k_956_; lean_object* v_l_957_; lean_object* v_r_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_k_956_ = lean_ctor_get(v_x_943_, 1);
v_l_957_ = lean_ctor_get(v_x_943_, 3);
v_r_958_ = lean_ctor_get(v_x_943_, 4);
v___x_959_ = lean_box(0);
v___x_960_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(v_init_942_, v_l_957_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_p_961_; lean_object* v___x_962_; 
lean_dec_ref_known(v___x_960_, 1);
v_p_961_ = lean_ctor_get(v_k_956_, 0);
v___x_962_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v_p_961_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_dec_ref_known(v___x_962_, 1);
v_init_942_ = v___x_959_;
v_x_943_ = v_r_958_;
goto _start;
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_a_964_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_962_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_962_);
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
else
{
return v___x_960_;
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v_init_942_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_942_ = stack[0].m_obj;
lean_object* v_x_943_ = stack[1].m_obj;
lean_object* v___y_944_ = stack[2].m_obj;
lean_object* v___y_945_ = stack[3].m_obj;
lean_object* v___y_946_ = stack[4].m_obj;
lean_object* v___y_947_ = stack[5].m_obj;
lean_object* v___y_948_ = stack[6].m_obj;
lean_object* v___y_949_ = stack[7].m_obj;
lean_object* v___y_950_ = stack[8].m_obj;
lean_object* v___y_951_ = stack[9].m_obj;
lean_object* v___y_952_ = stack[10].m_obj;
lean_object* v___y_953_ = stack[11].m_obj;
lean_object* v___y_954_ = stack[12].m_obj;
lean_object* v_res_974_;
v_res_974_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(v_init_942_, v_x_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
stack->m_obj
 = v_res_974_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0___boxed(lean_object* v_init_975_, lean_object* v_x_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(v_init_975_, v_x_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v_x_976_);
return v_res_989_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue(lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_990_, v_a_991_, v_a_999_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v_queue_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v_queue_1004_ = lean_ctor_get(v_a_1003_, 4);
lean_inc(v_queue_1004_);
lean_dec(v_a_1003_);
v___x_1005_ = lean_box(0);
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(v___x_1005_, v_queue_1004_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_queue_1004_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; 
v_unused_1014_ = lean_ctor_get(v___x_1006_, 0);
lean_dec(v_unused_1014_);
v___x_1008_ = v___x_1006_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_dec(v___x_1006_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1005_);
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1005_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1006_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1006_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1002_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1002_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_990_ = stack[0].m_obj;
lean_object* v_a_991_ = stack[1].m_obj;
lean_object* v_a_992_ = stack[2].m_obj;
lean_object* v_a_993_ = stack[3].m_obj;
lean_object* v_a_994_ = stack[4].m_obj;
lean_object* v_a_995_ = stack[5].m_obj;
lean_object* v_a_996_ = stack[6].m_obj;
lean_object* v_a_997_ = stack[7].m_obj;
lean_object* v_a_998_ = stack[8].m_obj;
lean_object* v_a_999_ = stack[9].m_obj;
lean_object* v_a_1000_ = stack[10].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue(v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
stack->m_obj
 = v_res_1031_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue___boxed(lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue(v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
return v_res_1044_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_1048_, size_t v_sz_1049_, size_t v_i_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_usize_dec_lt(v_i_1050_, v_sz_1049_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_b_1051_);
return v___x_1065_;
}
else
{
lean_object* v_a_1066_; lean_object* v_d_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_dec_ref(v_b_1051_);
v_a_1066_ = lean_array_uget_borrowed(v_as_1048_, v_i_1050_);
v_d_1067_ = lean_ctor_get(v_a_1066_, 4);
v___x_1068_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_1067_);
v___x_1069_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v___x_1068_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec_ref(v___x_1068_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v___x_1070_; size_t v___x_1071_; size_t v___x_1072_; 
lean_dec_ref_known(v___x_1069_, 1);
v___x_1070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_1071_ = ((size_t)1ULL);
v___x_1072_ = lean_usize_add(v_i_1050_, v___x_1071_);
v_i_1050_ = v___x_1072_;
v_b_1051_ = v___x_1070_;
goto _start;
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_a_1074_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1069_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1069_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1048_ = stack[0].m_obj;
size_t v_sz_1049_ = stack[1].m_num;
size_t v_i_1050_ = stack[2].m_num;
lean_object* v_b_1051_ = stack[3].m_obj;
lean_object* v___y_1052_ = stack[4].m_obj;
lean_object* v___y_1053_ = stack[5].m_obj;
lean_object* v___y_1054_ = stack[6].m_obj;
lean_object* v___y_1055_ = stack[7].m_obj;
lean_object* v___y_1056_ = stack[8].m_obj;
lean_object* v___y_1057_ = stack[9].m_obj;
lean_object* v___y_1058_ = stack[10].m_obj;
lean_object* v___y_1059_ = stack[11].m_obj;
lean_object* v___y_1060_ = stack[12].m_obj;
lean_object* v___y_1061_ = stack[13].m_obj;
lean_object* v___y_1062_ = stack[14].m_obj;
lean_object* v_res_1082_;
v_res_1082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_1048_, v_sz_1049_, v_i_1050_, v_b_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
stack->m_obj
 = v_res_1082_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_1083_, lean_object* v_sz_1084_, lean_object* v_i_1085_, lean_object* v_b_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
size_t v_sz_boxed_1099_; size_t v_i_boxed_1100_; lean_object* v_res_1101_; 
v_sz_boxed_1099_ = lean_unbox_usize(v_sz_1084_);
lean_dec(v_sz_1084_);
v_i_boxed_1100_ = lean_unbox_usize(v_i_1085_);
lean_dec(v_i_1085_);
v_res_1101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_1083_, v_sz_boxed_1099_, v_i_boxed_1100_, v_b_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec_ref(v_as_1083_);
return v_res_1101_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2(lean_object* v_as_1102_, size_t v_sz_1103_, size_t v_i_1104_, lean_object* v_b_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
uint8_t v___x_1118_; 
v___x_1118_ = lean_usize_dec_lt(v_i_1104_, v_sz_1103_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_b_1105_);
return v___x_1119_;
}
else
{
lean_object* v_a_1120_; lean_object* v_d_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec_ref(v_b_1105_);
v_a_1120_ = lean_array_uget_borrowed(v_as_1102_, v_i_1104_);
v_d_1121_ = lean_ctor_get(v_a_1120_, 4);
v___x_1122_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_1121_);
v___x_1123_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v___x_1122_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec_ref(v___x_1122_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v___x_1124_; size_t v___x_1125_; size_t v___x_1126_; lean_object* v___x_1127_; 
lean_dec_ref_known(v___x_1123_, 1);
v___x_1124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_1125_ = ((size_t)1ULL);
v___x_1126_ = lean_usize_add(v_i_1104_, v___x_1125_);
v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_1102_, v_sz_1103_, v___x_1126_, v___x_1124_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v___x_1127_;
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_a_1128_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1123_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1123_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1102_ = stack[0].m_obj;
size_t v_sz_1103_ = stack[1].m_num;
size_t v_i_1104_ = stack[2].m_num;
lean_object* v_b_1105_ = stack[3].m_obj;
lean_object* v___y_1106_ = stack[4].m_obj;
lean_object* v___y_1107_ = stack[5].m_obj;
lean_object* v___y_1108_ = stack[6].m_obj;
lean_object* v___y_1109_ = stack[7].m_obj;
lean_object* v___y_1110_ = stack[8].m_obj;
lean_object* v___y_1111_ = stack[9].m_obj;
lean_object* v___y_1112_ = stack[10].m_obj;
lean_object* v___y_1113_ = stack[11].m_obj;
lean_object* v___y_1114_ = stack[12].m_obj;
lean_object* v___y_1115_ = stack[13].m_obj;
lean_object* v___y_1116_ = stack[14].m_obj;
lean_object* v_res_1136_;
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2(v_as_1102_, v_sz_1103_, v_i_1104_, v_b_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
stack->m_obj
 = v_res_1136_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1137_, lean_object* v_sz_1138_, lean_object* v_i_1139_, lean_object* v_b_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
size_t v_sz_boxed_1153_; size_t v_i_boxed_1154_; lean_object* v_res_1155_; 
v_sz_boxed_1153_ = lean_unbox_usize(v_sz_1138_);
lean_dec(v_sz_1138_);
v_i_boxed_1154_ = lean_unbox_usize(v_i_1139_);
lean_dec(v_i_1139_);
v_res_1155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2(v_as_1137_, v_sz_boxed_1153_, v_i_boxed_1154_, v_b_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_as_1137_);
return v_res_1155_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(lean_object* v_init_1156_, lean_object* v_n_1157_, lean_object* v_b_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
if (lean_obj_tag(v_n_1157_) == 0)
{
lean_object* v_cs_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; size_t v_sz_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
v_cs_1171_ = lean_ctor_get(v_n_1157_, 0);
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v_b_1158_);
v_sz_1174_ = lean_array_size(v_cs_1171_);
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(v_init_1156_, v_cs_1171_, v_sz_1174_, v___x_1175_, v___x_1173_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1191_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1191_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1191_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_fst_1181_; 
v_fst_1181_ = lean_ctor_get(v_a_1177_, 0);
if (lean_obj_tag(v_fst_1181_) == 0)
{
lean_object* v_snd_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v_snd_1182_ = lean_ctor_get(v_a_1177_, 1);
lean_inc(v_snd_1182_);
lean_dec(v_a_1177_);
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_snd_1182_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1183_);
v___x_1185_ = v___x_1179_;
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
else
{
lean_object* v_val_1187_; lean_object* v___x_1189_; 
lean_inc_ref(v_fst_1181_);
lean_dec(v_a_1177_);
v_val_1187_ = lean_ctor_get(v_fst_1181_, 0);
lean_inc(v_val_1187_);
lean_dec_ref_known(v_fst_1181_, 1);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v_val_1187_);
v___x_1189_ = v___x_1179_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_val_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_a_1192_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1176_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1176_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_vs_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; size_t v_sz_1203_; size_t v___x_1204_; lean_object* v___x_1205_; 
v_vs_1200_ = lean_ctor_get(v_n_1157_, 0);
v___x_1201_ = lean_box(0);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v_b_1158_);
v_sz_1203_ = lean_array_size(v_vs_1200_);
v___x_1204_ = ((size_t)0ULL);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2(v_vs_1200_, v_sz_1203_, v___x_1204_, v___x_1202_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1220_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1220_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1220_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v_fst_1210_; 
v_fst_1210_ = lean_ctor_get(v_a_1206_, 0);
if (lean_obj_tag(v_fst_1210_) == 0)
{
lean_object* v_snd_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v_snd_1211_ = lean_ctor_get(v_a_1206_, 1);
lean_inc(v_snd_1211_);
lean_dec(v_a_1206_);
v___x_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1212_, 0, v_snd_1211_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1212_);
v___x_1214_ = v___x_1208_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
else
{
lean_object* v_val_1216_; lean_object* v___x_1218_; 
lean_inc_ref(v_fst_1210_);
lean_dec(v_a_1206_);
v_val_1216_ = lean_ctor_get(v_fst_1210_, 0);
lean_inc(v_val_1216_);
lean_dec_ref_known(v_fst_1210_, 1);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v_val_1216_);
v___x_1218_ = v___x_1208_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_val_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
v_a_1221_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1205_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1205_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1156_ = stack[0].m_obj;
lean_object* v_n_1157_ = stack[1].m_obj;
lean_object* v_b_1158_ = stack[2].m_obj;
lean_object* v___y_1159_ = stack[3].m_obj;
lean_object* v___y_1160_ = stack[4].m_obj;
lean_object* v___y_1161_ = stack[5].m_obj;
lean_object* v___y_1162_ = stack[6].m_obj;
lean_object* v___y_1163_ = stack[7].m_obj;
lean_object* v___y_1164_ = stack[8].m_obj;
lean_object* v___y_1165_ = stack[9].m_obj;
lean_object* v___y_1166_ = stack[10].m_obj;
lean_object* v___y_1167_ = stack[11].m_obj;
lean_object* v___y_1168_ = stack[12].m_obj;
lean_object* v___y_1169_ = stack[13].m_obj;
lean_object* v_res_1229_;
v_res_1229_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(v_init_1156_, v_n_1157_, v_b_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
stack->m_obj
 = v_res_1229_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_1230_, lean_object* v_as_1231_, size_t v_sz_1232_, size_t v_i_1233_, lean_object* v_b_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
uint8_t v___x_1247_; 
v___x_1247_ = lean_usize_dec_lt(v_i_1233_, v_sz_1232_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_b_1234_);
return v___x_1248_;
}
else
{
lean_object* v_snd_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1283_; 
v_snd_1249_ = lean_ctor_get(v_b_1234_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_b_1234_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v_b_1234_, 0);
lean_dec(v_unused_1284_);
v___x_1251_ = v_b_1234_;
v_isShared_1252_ = v_isSharedCheck_1283_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_snd_1249_);
lean_dec(v_b_1234_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1283_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v_a_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_box(0);
v_a_1254_ = lean_array_uget_borrowed(v_as_1231_, v_i_1233_);
lean_inc(v_snd_1249_);
v___x_1255_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(v_init_1230_, v_a_1254_, v_snd_1249_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1274_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1258_ = v___x_1255_;
v_isShared_1259_ = v_isSharedCheck_1274_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1274_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
if (lean_obj_tag(v_a_1256_) == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v_a_1256_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1260_);
v___x_1262_ = v___x_1251_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_snd_1249_);
v___x_1262_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1264_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1262_);
v___x_1264_ = v___x_1258_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; 
lean_del_object(v___x_1258_);
lean_dec(v_snd_1249_);
v_a_1267_ = lean_ctor_get(v_a_1256_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v_a_1256_, 1);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v_a_1267_);
lean_ctor_set(v___x_1251_, 0, v___x_1253_);
v___x_1269_ = v___x_1251_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_a_1267_);
v___x_1269_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
size_t v___x_1270_; size_t v___x_1271_; 
v___x_1270_ = ((size_t)1ULL);
v___x_1271_ = lean_usize_add(v_i_1233_, v___x_1270_);
v_i_1233_ = v___x_1271_;
v_b_1234_ = v___x_1269_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_del_object(v___x_1251_);
lean_dec(v_snd_1249_);
v_a_1275_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1255_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1255_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1230_ = stack[0].m_obj;
lean_object* v_as_1231_ = stack[1].m_obj;
size_t v_sz_1232_ = stack[2].m_num;
size_t v_i_1233_ = stack[3].m_num;
lean_object* v_b_1234_ = stack[4].m_obj;
lean_object* v___y_1235_ = stack[5].m_obj;
lean_object* v___y_1236_ = stack[6].m_obj;
lean_object* v___y_1237_ = stack[7].m_obj;
lean_object* v___y_1238_ = stack[8].m_obj;
lean_object* v___y_1239_ = stack[9].m_obj;
lean_object* v___y_1240_ = stack[10].m_obj;
lean_object* v___y_1241_ = stack[11].m_obj;
lean_object* v___y_1242_ = stack[12].m_obj;
lean_object* v___y_1243_ = stack[13].m_obj;
lean_object* v___y_1244_ = stack[14].m_obj;
lean_object* v___y_1245_ = stack[15].m_obj;
lean_object* v_res_1285_;
v_res_1285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(v_init_1230_, v_as_1231_, v_sz_1232_, v_i_1233_, v_b_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
stack->m_obj
 = v_res_1285_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1286_ = _args[0];
lean_object* v_as_1287_ = _args[1];
lean_object* v_sz_1288_ = _args[2];
lean_object* v_i_1289_ = _args[3];
lean_object* v_b_1290_ = _args[4];
lean_object* v___y_1291_ = _args[5];
lean_object* v___y_1292_ = _args[6];
lean_object* v___y_1293_ = _args[7];
lean_object* v___y_1294_ = _args[8];
lean_object* v___y_1295_ = _args[9];
lean_object* v___y_1296_ = _args[10];
lean_object* v___y_1297_ = _args[11];
lean_object* v___y_1298_ = _args[12];
lean_object* v___y_1299_ = _args[13];
lean_object* v___y_1300_ = _args[14];
lean_object* v___y_1301_ = _args[15];
lean_object* v___y_1302_ = _args[16];
_start:
{
size_t v_sz_boxed_1303_; size_t v_i_boxed_1304_; lean_object* v_res_1305_; 
v_sz_boxed_1303_ = lean_unbox_usize(v_sz_1288_);
lean_dec(v_sz_1288_);
v_i_boxed_1304_ = lean_unbox_usize(v_i_1289_);
lean_dec(v_i_1289_);
v_res_1305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(v_init_1286_, v_as_1287_, v_sz_boxed_1303_, v_i_boxed_1304_, v_b_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
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
lean_dec_ref(v_as_1287_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___boxed(lean_object* v_init_1306_, lean_object* v_n_1307_, lean_object* v_b_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(v_init_1306_, v_n_1307_, v_b_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec_ref(v_n_1307_);
return v_res_1321_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4(lean_object* v_as_1325_, size_t v_sz_1326_, size_t v_i_1327_, lean_object* v_b_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_lt(v_i_1327_, v_sz_1326_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v_b_1328_);
return v___x_1342_;
}
else
{
lean_object* v_a_1343_; lean_object* v_d_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec_ref(v_b_1328_);
v_a_1343_ = lean_array_uget_borrowed(v_as_1325_, v_i_1327_);
v_d_1344_ = lean_ctor_get(v_a_1343_, 4);
v___x_1345_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_1344_);
v___x_1346_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v___x_1345_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec_ref(v___x_1345_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v___x_1347_; size_t v___x_1348_; size_t v___x_1349_; 
lean_dec_ref_known(v___x_1346_, 1);
v___x_1347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___closed__0));
v___x_1348_ = ((size_t)1ULL);
v___x_1349_ = lean_usize_add(v_i_1327_, v___x_1348_);
v_i_1327_ = v___x_1349_;
v_b_1328_ = v___x_1347_;
goto _start;
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
v_a_1351_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1346_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1346_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1325_ = stack[0].m_obj;
size_t v_sz_1326_ = stack[1].m_num;
size_t v_i_1327_ = stack[2].m_num;
lean_object* v_b_1328_ = stack[3].m_obj;
lean_object* v___y_1329_ = stack[4].m_obj;
lean_object* v___y_1330_ = stack[5].m_obj;
lean_object* v___y_1331_ = stack[6].m_obj;
lean_object* v___y_1332_ = stack[7].m_obj;
lean_object* v___y_1333_ = stack[8].m_obj;
lean_object* v___y_1334_ = stack[9].m_obj;
lean_object* v___y_1335_ = stack[10].m_obj;
lean_object* v___y_1336_ = stack[11].m_obj;
lean_object* v___y_1337_ = stack[12].m_obj;
lean_object* v___y_1338_ = stack[13].m_obj;
lean_object* v___y_1339_ = stack[14].m_obj;
lean_object* v_res_1359_;
v_res_1359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4(v_as_1325_, v_sz_1326_, v_i_1327_, v_b_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
stack->m_obj
 = v_res_1359_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1360_, lean_object* v_sz_1361_, lean_object* v_i_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
size_t v_sz_boxed_1376_; size_t v_i_boxed_1377_; lean_object* v_res_1378_; 
v_sz_boxed_1376_ = lean_unbox_usize(v_sz_1361_);
lean_dec(v_sz_1361_);
v_i_boxed_1377_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4(v_as_1360_, v_sz_boxed_1376_, v_i_boxed_1377_, v_b_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec_ref(v_as_1360_);
return v_res_1378_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1(lean_object* v_as_1379_, size_t v_sz_1380_, size_t v_i_1381_, lean_object* v_b_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_usize_dec_lt(v_i_1381_, v_sz_1380_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_b_1382_);
return v___x_1396_;
}
else
{
lean_object* v_a_1397_; lean_object* v_d_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec_ref(v_b_1382_);
v_a_1397_ = lean_array_uget_borrowed(v_as_1379_, v_i_1381_);
v_d_1398_ = lean_ctor_get(v_a_1397_, 4);
v___x_1399_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_1398_);
v___x_1400_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v___x_1399_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec_ref(v___x_1399_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v___x_1401_; size_t v___x_1402_; size_t v___x_1403_; lean_object* v___x_1404_; 
lean_dec_ref_known(v___x_1400_, 1);
v___x_1401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___closed__0));
v___x_1402_ = ((size_t)1ULL);
v___x_1403_ = lean_usize_add(v_i_1381_, v___x_1402_);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4(v_as_1379_, v_sz_1380_, v___x_1403_, v___x_1401_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
return v___x_1404_;
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1400_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1400_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1379_ = stack[0].m_obj;
size_t v_sz_1380_ = stack[1].m_num;
size_t v_i_1381_ = stack[2].m_num;
lean_object* v_b_1382_ = stack[3].m_obj;
lean_object* v___y_1383_ = stack[4].m_obj;
lean_object* v___y_1384_ = stack[5].m_obj;
lean_object* v___y_1385_ = stack[6].m_obj;
lean_object* v___y_1386_ = stack[7].m_obj;
lean_object* v___y_1387_ = stack[8].m_obj;
lean_object* v___y_1388_ = stack[9].m_obj;
lean_object* v___y_1389_ = stack[10].m_obj;
lean_object* v___y_1390_ = stack[11].m_obj;
lean_object* v___y_1391_ = stack[12].m_obj;
lean_object* v___y_1392_ = stack[13].m_obj;
lean_object* v___y_1393_ = stack[14].m_obj;
lean_object* v_res_1413_;
v_res_1413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1(v_as_1379_, v_sz_1380_, v_i_1381_, v_b_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
stack->m_obj
 = v_res_1413_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1___boxed(lean_object* v_as_1414_, lean_object* v_sz_1415_, lean_object* v_i_1416_, lean_object* v_b_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
size_t v_sz_boxed_1430_; size_t v_i_boxed_1431_; lean_object* v_res_1432_; 
v_sz_boxed_1430_ = lean_unbox_usize(v_sz_1415_);
lean_dec(v_sz_1415_);
v_i_boxed_1431_ = lean_unbox_usize(v_i_1416_);
lean_dec(v_i_1416_);
v_res_1432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1(v_as_1414_, v_sz_boxed_1430_, v_i_boxed_1431_, v_b_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec_ref(v_as_1414_);
return v_res_1432_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(lean_object* v_t_1433_, lean_object* v_init_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_root_1447_; lean_object* v_tail_1448_; lean_object* v___x_1449_; 
v_root_1447_ = lean_ctor_get(v_t_1433_, 0);
v_tail_1448_ = lean_ctor_get(v_t_1433_, 1);
v___x_1449_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(v_init_1434_, v_root_1447_, v_init_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1486_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1486_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1486_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
if (lean_obj_tag(v_a_1450_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; 
v_a_1454_ = lean_ctor_get(v_a_1450_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v_a_1450_, 1);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v_a_1454_);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; size_t v_sz_1461_; size_t v___x_1462_; lean_object* v___x_1463_; 
lean_del_object(v___x_1452_);
v_a_1458_ = lean_ctor_get(v_a_1450_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v_a_1450_, 1);
v___x_1459_ = lean_box(0);
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v_a_1458_);
v_sz_1461_ = lean_array_size(v_tail_1448_);
v___x_1462_ = ((size_t)0ULL);
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1(v_tail_1448_, v_sz_1461_, v___x_1462_, v___x_1460_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1477_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1477_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1477_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_fst_1468_; 
v_fst_1468_ = lean_ctor_get(v_a_1464_, 0);
if (lean_obj_tag(v_fst_1468_) == 0)
{
lean_object* v_snd_1469_; lean_object* v___x_1471_; 
v_snd_1469_ = lean_ctor_get(v_a_1464_, 1);
lean_inc(v_snd_1469_);
lean_dec(v_a_1464_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v_snd_1469_);
v___x_1471_ = v___x_1466_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_snd_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
else
{
lean_object* v_val_1473_; lean_object* v___x_1475_; 
lean_inc_ref(v_fst_1468_);
lean_dec(v_a_1464_);
v_val_1473_ = lean_ctor_get(v_fst_1468_, 0);
lean_inc(v_val_1473_);
lean_dec_ref_known(v_fst_1468_, 1);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v_val_1473_);
v___x_1475_ = v___x_1466_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_val_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
v_a_1478_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1463_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1463_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1487_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1449_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1449_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1433_ = stack[0].m_obj;
lean_object* v_init_1434_ = stack[1].m_obj;
lean_object* v___y_1435_ = stack[2].m_obj;
lean_object* v___y_1436_ = stack[3].m_obj;
lean_object* v___y_1437_ = stack[4].m_obj;
lean_object* v___y_1438_ = stack[5].m_obj;
lean_object* v___y_1439_ = stack[6].m_obj;
lean_object* v___y_1440_ = stack[7].m_obj;
lean_object* v___y_1441_ = stack[8].m_obj;
lean_object* v___y_1442_ = stack[9].m_obj;
lean_object* v___y_1443_ = stack[10].m_obj;
lean_object* v___y_1444_ = stack[11].m_obj;
lean_object* v___y_1445_ = stack[12].m_obj;
lean_object* v_res_1495_;
v_res_1495_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(v_t_1433_, v_init_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
stack->m_obj
 = v_res_1495_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0___boxed(lean_object* v_t_1496_, lean_object* v_init_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(v_t_1496_, v_init_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec_ref(v_t_1496_);
return v_res_1510_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_1511_, v_a_1512_, v_a_1520_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v_diseqs_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v_diseqs_1525_ = lean_ctor_get(v_a_1524_, 6);
lean_inc_ref(v_diseqs_1525_);
lean_dec(v_a_1524_);
v___x_1526_ = lean_box(0);
v___x_1527_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(v_diseqs_1525_, v___x_1526_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
lean_dec_ref(v_diseqs_1525_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v___x_1527_, 0);
lean_dec(v_unused_1535_);
v___x_1529_ = v___x_1527_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_dec(v___x_1527_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1526_);
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1526_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
else
{
return v___x_1527_;
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
v_a_1536_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1523_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1523_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1511_ = stack[0].m_obj;
lean_object* v_a_1512_ = stack[1].m_obj;
lean_object* v_a_1513_ = stack[2].m_obj;
lean_object* v_a_1514_ = stack[3].m_obj;
lean_object* v_a_1515_ = stack[4].m_obj;
lean_object* v_a_1516_ = stack[5].m_obj;
lean_object* v_a_1517_ = stack[6].m_obj;
lean_object* v_a_1518_ = stack[7].m_obj;
lean_object* v_a_1519_ = stack[8].m_obj;
lean_object* v_a_1520_ = stack[9].m_obj;
lean_object* v_a_1521_ = stack[10].m_obj;
lean_object* v_res_1544_;
v_res_1544_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
stack->m_obj
 = v_res_1544_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___boxed(lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
lean_dec(v_a_1547_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
return v_res_1557_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs(lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars(v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v___x_1571_; 
lean_dec_ref_known(v___x_1570_, 1);
v___x_1571_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis(v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1572_; 
lean_dec_ref_known(v___x_1571_, 1);
v___x_1572_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue(v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; 
lean_dec_ref_known(v___x_1572_, 1);
v___x_1573_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
return v___x_1573_;
}
else
{
return v___x_1572_;
}
}
else
{
return v___x_1571_;
}
}
else
{
return v___x_1570_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1558_ = stack[0].m_obj;
lean_object* v_a_1559_ = stack[1].m_obj;
lean_object* v_a_1560_ = stack[2].m_obj;
lean_object* v_a_1561_ = stack[3].m_obj;
lean_object* v_a_1562_ = stack[4].m_obj;
lean_object* v_a_1563_ = stack[5].m_obj;
lean_object* v_a_1564_ = stack[6].m_obj;
lean_object* v_a_1565_ = stack[7].m_obj;
lean_object* v_a_1566_ = stack[8].m_obj;
lean_object* v_a_1567_ = stack[9].m_obj;
lean_object* v_a_1568_ = stack[10].m_obj;
lean_object* v_res_1574_;
v_res_1574_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs(v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
stack->m_obj
 = v_res_1574_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs___boxed(lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs(v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
return v_res_1587_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1590_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__1));
v___x_1591_ = lean_unsigned_to_nat(6u);
v___x_1592_ = lean_unsigned_to_nat(55u);
v___x_1593_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__0));
v___x_1594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0));
v___x_1595_ = l_mkPanicMessageWithDecl(v___x_1594_, v___x_1593_, v___x_1592_, v___x_1591_, v___x_1590_);
return v___x_1595_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(lean_object* v_upperBound_1596_, lean_object* v_a_1597_, lean_object* v_b_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_nat_dec_lt(v_a_1597_, v_upperBound_1596_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
lean_dec(v_a_1597_);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_b_1598_);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; lean_object* v___y_1614_; uint8_t v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1612_ = lean_box(0);
v___x_1618_ = 0;
lean_inc(v_a_1597_);
v___x_1619_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1619_, 0, v_a_1597_);
lean_ctor_set_uint8(v___x_1619_, sizeof(void*)*1, v___x_1618_);
v___x_1620_ = lean_nat_dec_eq(v_a_1597_, v_a_1597_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2);
v___x_1622_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_1621_, v___x_1619_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec_ref_known(v___x_1619_, 1);
v___y_1614_ = v___x_1622_;
goto v___jp_1613_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs(v___x_1619_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec_ref_known(v___x_1619_, 1);
v___y_1614_ = v___x_1623_;
goto v___jp_1613_;
}
v___jp_1613_:
{
if (lean_obj_tag(v___y_1614_) == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec_ref_known(v___y_1614_, 1);
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_nat_add(v_a_1597_, v___x_1615_);
lean_dec(v_a_1597_);
v_a_1597_ = v___x_1616_;
v_b_1598_ = v___x_1612_;
goto _start;
}
else
{
lean_dec(v_a_1597_);
return v___y_1614_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1596_ = stack[0].m_obj;
lean_object* v_a_1597_ = stack[1].m_obj;
lean_object* v_b_1598_ = stack[2].m_obj;
lean_object* v___y_1599_ = stack[3].m_obj;
lean_object* v___y_1600_ = stack[4].m_obj;
lean_object* v___y_1601_ = stack[5].m_obj;
lean_object* v___y_1602_ = stack[6].m_obj;
lean_object* v___y_1603_ = stack[7].m_obj;
lean_object* v___y_1604_ = stack[8].m_obj;
lean_object* v___y_1605_ = stack[9].m_obj;
lean_object* v___y_1606_ = stack[10].m_obj;
lean_object* v___y_1607_ = stack[11].m_obj;
lean_object* v___y_1608_ = stack[12].m_obj;
lean_object* v_res_1624_;
v_res_1624_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(v_upperBound_1596_, v_a_1597_, v_b_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
stack->m_obj
 = v_res_1624_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___boxed(lean_object* v_upperBound_1625_, lean_object* v_a_1626_, lean_object* v_b_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(v_upperBound_1625_, v_a_1626_, v_b_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec(v_upperBound_1625_);
return v_res_1639_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
uint8_t v_debug_1651_; 
v_debug_1651_ = lean_ctor_get_uint8(v_a_1642_, sizeof(void*)*10 + 2);
if (v_debug_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1640_, v_a_1648_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v_rings_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v_rings_1656_ = lean_ctor_get(v_a_1655_, 0);
lean_inc_ref(v_rings_1656_);
lean_dec(v_a_1655_);
v___x_1657_ = lean_array_get_size(v_rings_1656_);
lean_dec_ref(v_rings_1656_);
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_box(0);
v___x_1660_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(v___x_1657_, v___x_1658_, v___x_1659_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; 
v_unused_1668_ = lean_ctor_get(v___x_1660_, 0);
lean_dec(v_unused_1668_);
v___x_1662_ = v___x_1660_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_dec(v___x_1660_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1659_);
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1659_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
return v___x_1660_;
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1669_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1654_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1654_);
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
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_checkInvariants_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1640_ = stack[0].m_obj;
lean_object* v_a_1641_ = stack[1].m_obj;
lean_object* v_a_1642_ = stack[2].m_obj;
lean_object* v_a_1643_ = stack[3].m_obj;
lean_object* v_a_1644_ = stack[4].m_obj;
lean_object* v_a_1645_ = stack[5].m_obj;
lean_object* v_a_1646_ = stack[6].m_obj;
lean_object* v_a_1647_ = stack[7].m_obj;
lean_object* v_a_1648_ = stack[8].m_obj;
lean_object* v_a_1649_ = stack[9].m_obj;
lean_object* v_res_1677_;
v_res_1677_ = l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
stack->m_obj
 = v_res_1677_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInvariants___boxed(lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec(v_a_1678_);
return v_res_1689_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0(lean_object* v_upperBound_1690_, lean_object* v_inst_1691_, lean_object* v_R_1692_, lean_object* v_a_1693_, lean_object* v_b_1694_, lean_object* v_c_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(v_upperBound_1690_, v_a_1693_, v_b_1694_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1690_ = stack[0].m_obj;
lean_object* v_a_1693_ = stack[3].m_obj;
lean_object* v_b_1694_ = stack[4].m_obj;
lean_object* v___y_1696_ = stack[6].m_obj;
lean_object* v___y_1697_ = stack[7].m_obj;
lean_object* v___y_1698_ = stack[8].m_obj;
lean_object* v___y_1699_ = stack[9].m_obj;
lean_object* v___y_1700_ = stack[10].m_obj;
lean_object* v___y_1701_ = stack[11].m_obj;
lean_object* v___y_1702_ = stack[12].m_obj;
lean_object* v___y_1703_ = stack[13].m_obj;
lean_object* v___y_1704_ = stack[14].m_obj;
lean_object* v___y_1705_ = stack[15].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0(v_upperBound_1690_, lean_box(0), lean_box(0), v_a_1693_, v_b_1694_, lean_box(0), v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1709_ = _args[0];
lean_object* v_inst_1710_ = _args[1];
lean_object* v_R_1711_ = _args[2];
lean_object* v_a_1712_ = _args[3];
lean_object* v_b_1713_ = _args[4];
lean_object* v_c_1714_ = _args[5];
lean_object* v___y_1715_ = _args[6];
lean_object* v___y_1716_ = _args[7];
lean_object* v___y_1717_ = _args[8];
lean_object* v___y_1718_ = _args[9];
lean_object* v___y_1719_ = _args[10];
lean_object* v___y_1720_ = _args[11];
lean_object* v___y_1721_ = _args[12];
lean_object* v___y_1722_ = _args[13];
lean_object* v___y_1723_ = _args[14];
lean_object* v___y_1724_ = _args[15];
lean_object* v___y_1725_ = _args[16];
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0(v_upperBound_1709_, v_inst_1710_, v_R_1711_, v_a_1712_, v_b_1713_, v_c_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec(v_upperBound_1709_);
return v_res_1726_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
