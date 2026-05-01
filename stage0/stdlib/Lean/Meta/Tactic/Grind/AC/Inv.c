// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Inv
// Imports: public import Lean.Meta.Tactic.Grind.AC.Util import Lean.Meta.Tactic.Grind.AC.Seq
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
uint8_t l_Lean_Grind_AC_Seq_compare(lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_isIdempotent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Grind_AC_Seq_noAdjacentDuplicates(lean_object*);
lean_object* l_Lean_Meta_Grind_AC_isCommutative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_hasNeutral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Grind_AC_Seq_contains(lean_object*, lean_object*);
uint8_t l_Lean_Grind_AC_instBEqSeq_beq(lean_object*, lean_object*);
uint8_t l_Lean_Grind_AC_Seq_isSorted(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_get_x27___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Meta.Tactic.Grind.AC.Inv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Meta.Tactic.Grind.AC.Inv.0.Lean.Meta.Grind.AC.checkVars"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "assertion violation: isSameExpr expr expr'\n    "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: s.vars.size == num\n\n"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.Tactic.Grind.AC.Inv.0.Lean.Meta.Grind.AC.checkSeq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "assertion violation: s.noAdjacentDuplicates\n\n"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: !s.contains 0 || s == .var 0\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "assertion violation: s.isSorted\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Tactic.Grind.AC.Inv.0.Lean.Meta.Grind.AC.checkBasis"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: compare c.lhs c.rhs == .gt\n    "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkInvariants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___boxed(lean_object**);
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v___x_15_; lean_object* v___f_16_; lean_object* v___x_5472__overap_17_; lean_object* v___x_18_; 
v___x_15_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0);
v___f_16_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_16_, 0, v___x_15_);
v___x_5472__overap_17_ = lean_panic_fn_borrowed(v___f_16_, v_msg_2_);
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
lean_inc(v___y_3_);
v___x_18_ = lean_apply_12(v___x_5472__overap_17_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, lean_box(0));
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___boxed(lean_object* v_msg_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v_msg_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
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
lean_dec(v___y_20_);
return v_res_32_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1(lean_object* v_msg_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; lean_object* v___f_48_; lean_object* v___x_5490__overap_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0);
v___f_48_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_48_, 0, v___x_47_);
v___x_5490__overap_49_ = lean_panic_fn_borrowed(v___f_48_, v_msg_34_);
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
lean_inc(v___y_35_);
v___x_50_ = lean_apply_12(v___x_5490__overap_49_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___boxed(lean_object* v_msg_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1(v_msg_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
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
lean_dec(v___y_52_);
return v_res_64_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__2));
v___x_69_ = lean_unsigned_to_nat(6u);
v___x_70_ = lean_unsigned_to_nat(21u);
v___x_71_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1));
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_73_ = l_mkPanicMessageWithDecl(v___x_72_, v___x_71_, v___x_70_, v___x_69_, v___x_68_);
return v___x_73_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__4));
v___x_76_ = lean_unsigned_to_nat(6u);
v___x_77_ = lean_unsigned_to_nat(19u);
v___x_78_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1));
v___x_79_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_80_ = l_mkPanicMessageWithDecl(v___x_79_, v___x_78_, v___x_77_, v___x_76_, v___x_75_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0(lean_object* v_vars_81_, lean_object* v_x_82_, lean_object* v_____s_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
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
v___x_105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3);
v___x_106_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_105_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_dec_ref(v___x_106_);
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
v___x_118_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5);
v___x_119_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1(v___x_118_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___boxed(lean_object* v_vars_120_, lean_object* v_x_121_, lean_object* v_____s_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0(v_vars_120_, v_x_121_, v_____s_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
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
lean_dec(v___y_123_);
lean_dec(v_____s_122_);
lean_dec_ref(v_x_121_);
lean_dec_ref(v_vars_120_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0(lean_object* v_f_136_, lean_object* v_s_137_, lean_object* v_a_138_, lean_object* v_b_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v_a_138_);
lean_ctor_set(v___x_152_, 1, v_b_139_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v___y_146_);
lean_inc_ref(v___y_145_);
lean_inc(v___y_144_);
lean_inc_ref(v___y_143_);
lean_inc(v___y_142_);
lean_inc(v___y_141_);
lean_inc(v___y_140_);
v___x_153_ = lean_apply_14(v_f_136_, v___x_152_, v_s_137_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, lean_box(0));
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_180_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_180_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_180_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_180_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
if (lean_obj_tag(v_a_154_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_168_; 
v_a_158_ = lean_ctor_get(v_a_154_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v_a_154_);
if (v_isSharedCheck_168_ == 0)
{
v___x_160_ = v_a_154_;
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v_a_154_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_158_);
v___x_163_ = v_reuseFailAlloc_167_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_165_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_163_);
v___x_165_ = v___x_156_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_179_; 
v_a_169_ = lean_ctor_get(v_a_154_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_a_154_);
if (v_isSharedCheck_179_ == 0)
{
v___x_171_ = v_a_154_;
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v_a_154_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_178_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_174_);
v___x_176_ = v___x_156_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_a_181_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_153_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_153_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0___boxed(lean_object* v_f_189_, lean_object* v_s_190_, lean_object* v_a_191_, lean_object* v_b_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0(v_f_189_, v_s_190_, v_a_191_, v_b_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec(v___y_194_);
lean_dec(v___y_193_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(lean_object* v_f_206_, lean_object* v_keys_207_, lean_object* v_vals_208_, lean_object* v_i_209_, lean_object* v_acc_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = lean_array_get_size(v_keys_207_);
v___x_224_ = lean_nat_dec_lt(v_i_209_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec(v_i_209_);
lean_dec_ref(v_f_206_);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v_acc_210_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
else
{
lean_object* v_k_227_; lean_object* v_v_228_; lean_object* v___x_229_; 
v_k_227_ = lean_array_fget_borrowed(v_keys_207_, v_i_209_);
v_v_228_ = lean_array_fget_borrowed(v_vals_208_, v_i_209_);
lean_inc_ref(v_f_206_);
lean_inc(v___y_221_);
lean_inc_ref(v___y_220_);
lean_inc(v___y_219_);
lean_inc_ref(v___y_218_);
lean_inc(v___y_217_);
lean_inc_ref(v___y_216_);
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
lean_inc(v___y_213_);
lean_inc(v___y_212_);
lean_inc(v___y_211_);
lean_inc(v_v_228_);
lean_inc(v_k_227_);
v___x_229_ = lean_apply_15(v_f_206_, v_acc_210_, v_k_227_, v_v_228_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, lean_box(0));
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
if (lean_obj_tag(v_a_230_) == 0)
{
lean_dec_ref(v_a_230_);
lean_dec(v_i_209_);
lean_dec_ref(v_f_206_);
return v___x_229_;
}
else
{
lean_object* v_a_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec_ref(v___x_229_);
v_a_231_ = lean_ctor_get(v_a_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref(v_a_230_);
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_add(v_i_209_, v___x_232_);
lean_dec(v_i_209_);
v_i_209_ = v___x_233_;
v_acc_210_ = v_a_231_;
goto _start;
}
}
else
{
lean_dec(v_i_209_);
lean_dec_ref(v_f_206_);
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_f_235_ = _args[0];
lean_object* v_keys_236_ = _args[1];
lean_object* v_vals_237_ = _args[2];
lean_object* v_i_238_ = _args[3];
lean_object* v_acc_239_ = _args[4];
lean_object* v___y_240_ = _args[5];
lean_object* v___y_241_ = _args[6];
lean_object* v___y_242_ = _args[7];
lean_object* v___y_243_ = _args[8];
lean_object* v___y_244_ = _args[9];
lean_object* v___y_245_ = _args[10];
lean_object* v___y_246_ = _args[11];
lean_object* v___y_247_ = _args[12];
lean_object* v___y_248_ = _args[13];
lean_object* v___y_249_ = _args[14];
lean_object* v___y_250_ = _args[15];
lean_object* v___y_251_ = _args[16];
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_235_, v_keys_236_, v_vals_237_, v_i_238_, v_acc_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v_vals_237_);
lean_dec_ref(v_keys_236_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(lean_object* v_f_253_, lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_object* v_es_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_290_; 
v_es_268_ = lean_ctor_get(v_x_254_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_290_ == 0)
{
v___x_270_ = v_x_254_;
v_isShared_271_ = v_isSharedCheck_290_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_es_268_);
lean_dec(v_x_254_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_290_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_array_get_size(v_es_268_);
v___x_274_ = lean_nat_dec_lt(v___x_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_276_; 
lean_dec_ref(v_es_268_);
lean_dec_ref(v_f_253_);
if (v_isShared_271_ == 0)
{
lean_ctor_set_tag(v___x_270_, 1);
lean_ctor_set(v___x_270_, 0, v_x_255_);
v___x_276_ = v___x_270_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_x_255_);
v___x_276_ = v_reuseFailAlloc_278_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; 
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
else
{
uint8_t v___x_279_; 
v___x_279_ = lean_nat_dec_le(v___x_273_, v___x_273_);
if (v___x_279_ == 0)
{
if (v___x_274_ == 0)
{
lean_object* v___x_281_; 
lean_dec_ref(v_es_268_);
lean_dec_ref(v_f_253_);
if (v_isShared_271_ == 0)
{
lean_ctor_set_tag(v___x_270_, 1);
lean_ctor_set(v___x_270_, 0, v_x_255_);
v___x_281_ = v___x_270_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_x_255_);
v___x_281_ = v_reuseFailAlloc_283_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; 
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
else
{
size_t v___x_284_; size_t v___x_285_; lean_object* v___x_286_; 
lean_del_object(v___x_270_);
v___x_284_ = ((size_t)0ULL);
v___x_285_ = lean_usize_of_nat(v___x_273_);
v___x_286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_253_, v_es_268_, v___x_284_, v___x_285_, v_x_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec_ref(v_es_268_);
return v___x_286_;
}
}
else
{
size_t v___x_287_; size_t v___x_288_; lean_object* v___x_289_; 
lean_del_object(v___x_270_);
v___x_287_ = ((size_t)0ULL);
v___x_288_ = lean_usize_of_nat(v___x_273_);
v___x_289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_253_, v_es_268_, v___x_287_, v___x_288_, v_x_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec_ref(v_es_268_);
return v___x_289_;
}
}
}
}
else
{
lean_object* v_ks_291_; lean_object* v_vs_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_ks_291_ = lean_ctor_get(v_x_254_, 0);
lean_inc_ref(v_ks_291_);
v_vs_292_ = lean_ctor_get(v_x_254_, 1);
lean_inc_ref(v_vs_292_);
lean_dec_ref(v_x_254_);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_253_, v_ks_291_, v_vs_292_, v___x_293_, v_x_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec_ref(v_vs_292_);
lean_dec_ref(v_ks_291_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_f_295_, lean_object* v_as_296_, size_t v_i_297_, size_t v_stop_298_, lean_object* v_b_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_a_313_; lean_object* v___y_318_; uint8_t v___x_321_; 
v___x_321_ = lean_usize_dec_eq(v_i_297_, v_stop_298_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_array_uget_borrowed(v_as_296_, v_i_297_);
switch(lean_obj_tag(v___x_322_))
{
case 0:
{
lean_object* v_key_323_; lean_object* v_val_324_; lean_object* v___x_325_; 
v_key_323_ = lean_ctor_get(v___x_322_, 0);
v_val_324_ = lean_ctor_get(v___x_322_, 1);
lean_inc_ref(v_f_295_);
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
lean_inc(v___y_300_);
lean_inc(v_val_324_);
lean_inc(v_key_323_);
v___x_325_ = lean_apply_15(v_f_295_, v_b_299_, v_key_323_, v_val_324_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, lean_box(0));
v___y_318_ = v___x_325_;
goto v___jp_317_;
}
case 1:
{
lean_object* v_node_326_; lean_object* v___x_327_; 
v_node_326_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_node_326_);
lean_inc_ref(v_f_295_);
v___x_327_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_295_, v_node_326_, v_b_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
v___y_318_ = v___x_327_;
goto v___jp_317_;
}
default: 
{
v_a_313_ = v_b_299_;
goto v___jp_312_;
}
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v_f_295_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v_b_299_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
v___jp_312_:
{
size_t v___x_314_; size_t v___x_315_; 
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_add(v_i_297_, v___x_314_);
v_i_297_ = v___x_315_;
v_b_299_ = v_a_313_;
goto _start;
}
v___jp_317_:
{
if (lean_obj_tag(v___y_318_) == 0)
{
lean_object* v_a_319_; 
v_a_319_ = lean_ctor_get(v___y_318_, 0);
if (lean_obj_tag(v_a_319_) == 0)
{
lean_dec_ref(v_f_295_);
return v___y_318_;
}
else
{
lean_object* v_a_320_; 
lean_inc_ref(v_a_319_);
lean_dec_ref(v___y_318_);
v_a_320_ = lean_ctor_get(v_a_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref(v_a_319_);
v_a_313_ = v_a_320_;
goto v___jp_312_;
}
}
else
{
lean_dec_ref(v_f_295_);
return v___y_318_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_f_330_ = _args[0];
lean_object* v_as_331_ = _args[1];
lean_object* v_i_332_ = _args[2];
lean_object* v_stop_333_ = _args[3];
lean_object* v_b_334_ = _args[4];
lean_object* v___y_335_ = _args[5];
lean_object* v___y_336_ = _args[6];
lean_object* v___y_337_ = _args[7];
lean_object* v___y_338_ = _args[8];
lean_object* v___y_339_ = _args[9];
lean_object* v___y_340_ = _args[10];
lean_object* v___y_341_ = _args[11];
lean_object* v___y_342_ = _args[12];
lean_object* v___y_343_ = _args[13];
lean_object* v___y_344_ = _args[14];
lean_object* v___y_345_ = _args[15];
lean_object* v___y_346_ = _args[16];
_start:
{
size_t v_i_boxed_347_; size_t v_stop_boxed_348_; lean_object* v_res_349_; 
v_i_boxed_347_ = lean_unbox_usize(v_i_332_);
lean_dec(v_i_332_);
v_stop_boxed_348_ = lean_unbox_usize(v_stop_333_);
lean_dec(v_stop_333_);
v_res_349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_330_, v_as_331_, v_i_boxed_347_, v_stop_boxed_348_, v_b_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v_as_331_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_f_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_350_, v_x_351_, v_x_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
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
lean_dec(v___y_353_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(lean_object* v_map_366_, lean_object* v_init_367_, lean_object* v_f_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___f_381_; lean_object* v___x_382_; 
v___f_381_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0___boxed), 16, 1);
lean_closure_set(v___f_381_, 0, v_f_368_);
lean_inc_ref(v_map_366_);
v___x_382_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v___f_381_, v_map_366_, v_init_367_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___boxed(lean_object* v_map_400_, lean_object* v_init_401_, lean_object* v_f_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_map_400_, v_init_401_, v_f_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
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
lean_dec(v___y_403_);
lean_dec_ref(v_map_400_);
return v_res_415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0));
v___x_418_ = lean_unsigned_to_nat(2u);
v___x_419_ = lean_unsigned_to_nat(23u);
v___x_420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1));
v___x_421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_422_ = l_mkPanicMessageWithDecl(v___x_421_, v___x_420_, v___x_419_, v___x_418_, v___x_417_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v_vars_437_; lean_object* v_varMap_438_; lean_object* v___f_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref(v___x_435_);
v_vars_437_ = lean_ctor_get(v_a_436_, 10);
lean_inc_ref_n(v_vars_437_, 2);
v_varMap_438_ = lean_ctor_get(v_a_436_, 11);
lean_inc_ref(v_varMap_438_);
lean_dec(v_a_436_);
v___f_439_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___boxed), 15, 1);
lean_closure_set(v___f_439_, 0, v_vars_437_);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_varMap_438_, v___x_440_, v___f_439_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
lean_dec_ref(v_varMap_438_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_454_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_454_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_size_446_; uint8_t v___x_447_; 
v_size_446_ = lean_ctor_get(v_vars_437_, 2);
lean_inc(v_size_446_);
lean_dec_ref(v_vars_437_);
v___x_447_ = lean_nat_dec_eq(v_size_446_, v_a_442_);
lean_dec(v_a_442_);
lean_dec(v_size_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_del_object(v___x_444_);
v___x_448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1);
v___x_449_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_448_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = lean_box(0);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_450_);
v___x_452_ = v___x_444_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec_ref(v_vars_437_);
v_a_455_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_441_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_441_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
v_a_463_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_435_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_435_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___boxed(lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec(v_a_472_);
lean_dec(v_a_471_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2(lean_object* v_00_u03c3_484_, lean_object* v_00_u03b2_485_, lean_object* v_map_486_, lean_object* v_init_487_, lean_object* v_f_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_map_486_, v_init_487_, v_f_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_502_ = _args[0];
lean_object* v_00_u03b2_503_ = _args[1];
lean_object* v_map_504_ = _args[2];
lean_object* v_init_505_ = _args[3];
lean_object* v_f_506_ = _args[4];
lean_object* v___y_507_ = _args[5];
lean_object* v___y_508_ = _args[6];
lean_object* v___y_509_ = _args[7];
lean_object* v___y_510_ = _args[8];
lean_object* v___y_511_ = _args[9];
lean_object* v___y_512_ = _args[10];
lean_object* v___y_513_ = _args[11];
lean_object* v___y_514_ = _args[12];
lean_object* v___y_515_ = _args[13];
lean_object* v___y_516_ = _args[14];
lean_object* v___y_517_ = _args[15];
lean_object* v___y_518_ = _args[16];
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2(v_00_u03c3_502_, v_00_u03b2_503_, v_map_504_, v_init_505_, v_f_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v_map_504_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg(lean_object* v_map_520_, lean_object* v_f_521_, lean_object* v_init_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_521_, v_map_520_, v_init_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg___boxed(lean_object* v_map_536_, lean_object* v_f_537_, lean_object* v_init_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg(v_map_536_, v_f_537_, v_init_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec(v___y_540_);
lean_dec(v___y_539_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2(lean_object* v_00_u03c3_552_, lean_object* v_00_u03c3_553_, lean_object* v_00_u03b2_554_, lean_object* v_map_555_, lean_object* v_f_556_, lean_object* v_init_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_556_, v_map_555_, v_init_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_571_ = _args[0];
lean_object* v_00_u03c3_572_ = _args[1];
lean_object* v_00_u03b2_573_ = _args[2];
lean_object* v_map_574_ = _args[3];
lean_object* v_f_575_ = _args[4];
lean_object* v_init_576_ = _args[5];
lean_object* v___y_577_ = _args[6];
lean_object* v___y_578_ = _args[7];
lean_object* v___y_579_ = _args[8];
lean_object* v___y_580_ = _args[9];
lean_object* v___y_581_ = _args[10];
lean_object* v___y_582_ = _args[11];
lean_object* v___y_583_ = _args[12];
lean_object* v___y_584_ = _args[13];
lean_object* v___y_585_ = _args[14];
lean_object* v___y_586_ = _args[15];
lean_object* v___y_587_ = _args[16];
lean_object* v___y_588_ = _args[17];
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2(v_00_u03c3_571_, v_00_u03c3_572_, v_00_u03b2_573_, v_map_574_, v_f_575_, v_init_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec(v___y_578_);
lean_dec(v___y_577_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3(lean_object* v_00_u03c3_590_, lean_object* v_00_u03c3_591_, lean_object* v_00_u03b1_592_, lean_object* v_00_u03b2_593_, lean_object* v_f_594_, lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_594_, v_x_595_, v_x_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03c3_610_ = _args[0];
lean_object* v_00_u03c3_611_ = _args[1];
lean_object* v_00_u03b1_612_ = _args[2];
lean_object* v_00_u03b2_613_ = _args[3];
lean_object* v_f_614_ = _args[4];
lean_object* v_x_615_ = _args[5];
lean_object* v_x_616_ = _args[6];
lean_object* v___y_617_ = _args[7];
lean_object* v___y_618_ = _args[8];
lean_object* v___y_619_ = _args[9];
lean_object* v___y_620_ = _args[10];
lean_object* v___y_621_ = _args[11];
lean_object* v___y_622_ = _args[12];
lean_object* v___y_623_ = _args[13];
lean_object* v___y_624_ = _args[14];
lean_object* v___y_625_ = _args[15];
lean_object* v___y_626_ = _args[16];
lean_object* v___y_627_ = _args[17];
lean_object* v___y_628_ = _args[18];
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3(v_00_u03c3_610_, v_00_u03c3_611_, v_00_u03b1_612_, v_00_u03b2_613_, v_f_614_, v_x_615_, v_x_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec(v___y_618_);
lean_dec(v___y_617_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_630_, lean_object* v_00_u03b2_631_, lean_object* v_00_u03c3_632_, lean_object* v_00_u03c3_633_, lean_object* v_f_634_, lean_object* v_as_635_, size_t v_i_636_, size_t v_stop_637_, lean_object* v_b_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_634_, v_as_635_, v_i_636_, v_stop_637_, v_b_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_00_u03b1_652_ = _args[0];
lean_object* v_00_u03b2_653_ = _args[1];
lean_object* v_00_u03c3_654_ = _args[2];
lean_object* v_00_u03c3_655_ = _args[3];
lean_object* v_f_656_ = _args[4];
lean_object* v_as_657_ = _args[5];
lean_object* v_i_658_ = _args[6];
lean_object* v_stop_659_ = _args[7];
lean_object* v_b_660_ = _args[8];
lean_object* v___y_661_ = _args[9];
lean_object* v___y_662_ = _args[10];
lean_object* v___y_663_ = _args[11];
lean_object* v___y_664_ = _args[12];
lean_object* v___y_665_ = _args[13];
lean_object* v___y_666_ = _args[14];
lean_object* v___y_667_ = _args[15];
lean_object* v___y_668_ = _args[16];
lean_object* v___y_669_ = _args[17];
lean_object* v___y_670_ = _args[18];
lean_object* v___y_671_ = _args[19];
lean_object* v___y_672_ = _args[20];
_start:
{
size_t v_i_boxed_673_; size_t v_stop_boxed_674_; lean_object* v_res_675_; 
v_i_boxed_673_ = lean_unbox_usize(v_i_658_);
lean_dec(v_i_658_);
v_stop_boxed_674_ = lean_unbox_usize(v_stop_659_);
lean_dec(v_stop_659_);
v_res_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4(v_00_u03b1_652_, v_00_u03b2_653_, v_00_u03c3_654_, v_00_u03c3_655_, v_f_656_, v_as_657_, v_i_boxed_673_, v_stop_boxed_674_, v_b_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v_as_657_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_676_, lean_object* v_00_u03c3_677_, lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_f_680_, lean_object* v_keys_681_, lean_object* v_vals_682_, lean_object* v_heq_683_, lean_object* v_i_684_, lean_object* v_acc_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_680_, v_keys_681_, v_vals_682_, v_i_684_, v_acc_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_00_u03c3_699_ = _args[0];
lean_object* v_00_u03c3_700_ = _args[1];
lean_object* v_00_u03b1_701_ = _args[2];
lean_object* v_00_u03b2_702_ = _args[3];
lean_object* v_f_703_ = _args[4];
lean_object* v_keys_704_ = _args[5];
lean_object* v_vals_705_ = _args[6];
lean_object* v_heq_706_ = _args[7];
lean_object* v_i_707_ = _args[8];
lean_object* v_acc_708_ = _args[9];
lean_object* v___y_709_ = _args[10];
lean_object* v___y_710_ = _args[11];
lean_object* v___y_711_ = _args[12];
lean_object* v___y_712_ = _args[13];
lean_object* v___y_713_ = _args[14];
lean_object* v___y_714_ = _args[15];
lean_object* v___y_715_ = _args[16];
lean_object* v___y_716_ = _args[17];
lean_object* v___y_717_ = _args[18];
lean_object* v___y_718_ = _args[19];
lean_object* v___y_719_ = _args[20];
lean_object* v___y_720_ = _args[21];
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5(v_00_u03c3_699_, v_00_u03c3_700_, v_00_u03b1_701_, v_00_u03b2_702_, v_f_703_, v_keys_704_, v_vals_705_, v_heq_706_, v_i_707_, v_acc_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v_vals_705_);
lean_dec_ref(v_keys_704_);
return v_res_721_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1));
v___x_725_ = lean_unsigned_to_nat(4u);
v___x_726_ = lean_unsigned_to_nat(31u);
v___x_727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0));
v___x_728_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_729_ = l_mkPanicMessageWithDecl(v___x_728_, v___x_727_, v___x_726_, v___x_725_, v___x_724_);
return v___x_729_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4));
v___x_734_ = lean_unsigned_to_nat(4u);
v___x_735_ = lean_unsigned_to_nat(29u);
v___x_736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0));
v___x_737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_738_ = l_mkPanicMessageWithDecl(v___x_737_, v___x_736_, v___x_735_, v___x_734_, v___x_733_);
return v___x_738_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6));
v___x_741_ = lean_unsigned_to_nat(4u);
v___x_742_ = lean_unsigned_to_nat(27u);
v___x_743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0));
v___x_744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_745_ = l_mkPanicMessageWithDecl(v___x_744_, v___x_743_, v___x_742_, v___x_741_, v___x_740_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(lean_object* v_s_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___x_797_; 
v___x_797_ = l_Lean_Meta_Grind_AC_isCommutative(v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; uint8_t v___x_828_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___x_797_);
v___x_828_ = lean_unbox(v_a_798_);
lean_dec(v_a_798_);
if (v___x_828_ == 0)
{
v___y_800_ = v_a_747_;
v___y_801_ = v_a_748_;
v___y_802_ = v_a_749_;
v___y_803_ = v_a_750_;
v___y_804_ = v_a_751_;
v___y_805_ = v_a_752_;
v___y_806_ = v_a_753_;
v___y_807_ = v_a_754_;
v___y_808_ = v_a_755_;
v___y_809_ = v_a_756_;
v___y_810_ = v_a_757_;
goto v___jp_799_;
}
else
{
uint8_t v___x_829_; 
v___x_829_ = l_Lean_Grind_AC_Seq_isSorted(v_s_746_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7);
v___x_831_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_830_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
return v___x_831_;
}
else
{
v___y_800_ = v_a_747_;
v___y_801_ = v_a_748_;
v___y_802_ = v_a_749_;
v___y_803_ = v_a_750_;
v___y_804_ = v_a_751_;
v___y_805_ = v_a_752_;
v___y_806_ = v_a_753_;
v___y_807_ = v_a_754_;
v___y_808_ = v_a_755_;
v___y_809_ = v_a_756_;
v___y_810_ = v_a_757_;
goto v___jp_799_;
}
}
v___jp_799_:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Meta_Grind_AC_hasNeutral(v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; uint8_t v___x_813_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref(v___x_811_);
v___x_813_ = lean_unbox(v_a_812_);
lean_dec(v_a_812_);
if (v___x_813_ == 0)
{
v___y_760_ = v___y_800_;
v___y_761_ = v___y_801_;
v___y_762_ = v___y_802_;
v___y_763_ = v___y_803_;
v___y_764_ = v___y_804_;
v___y_765_ = v___y_805_;
v___y_766_ = v___y_806_;
v___y_767_ = v___y_807_;
v___y_768_ = v___y_808_;
v___y_769_ = v___y_809_;
v___y_770_ = v___y_810_;
goto v___jp_759_;
}
else
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = l_Lean_Grind_AC_Seq_contains(v_s_746_, v___x_814_);
if (v___x_815_ == 0)
{
v___y_760_ = v___y_800_;
v___y_761_ = v___y_801_;
v___y_762_ = v___y_802_;
v___y_763_ = v___y_803_;
v___y_764_ = v___y_804_;
v___y_765_ = v___y_805_;
v___y_766_ = v___y_806_;
v___y_767_ = v___y_807_;
v___y_768_ = v___y_808_;
v___y_769_ = v___y_809_;
v___y_770_ = v___y_810_;
goto v___jp_759_;
}
else
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3));
v___x_817_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_746_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5);
v___x_819_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_818_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
return v___x_819_;
}
else
{
v___y_760_ = v___y_800_;
v___y_761_ = v___y_801_;
v___y_762_ = v___y_802_;
v___y_763_ = v___y_803_;
v___y_764_ = v___y_804_;
v___y_765_ = v___y_805_;
v___y_766_ = v___y_806_;
v___y_767_ = v___y_807_;
v___y_768_ = v___y_808_;
v___y_769_ = v___y_809_;
v___y_770_ = v___y_810_;
goto v___jp_759_;
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
v_a_820_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_811_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_811_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_a_832_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_797_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_797_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
v___jp_759_:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Meta_Grind_AC_isIdempotent(v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_788_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_788_ == 0)
{
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_788_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_788_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
uint8_t v___x_776_; 
v___x_776_ = lean_unbox(v_a_772_);
lean_dec(v_a_772_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_box(0);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_777_);
v___x_779_ = v___x_774_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
else
{
uint8_t v___x_781_; 
v___x_781_ = l_Lean_Grind_AC_Seq_noAdjacentDuplicates(v_s_746_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_del_object(v___x_774_);
v___x_782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2);
v___x_783_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_782_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
return v___x_783_;
}
else
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = lean_box(0);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_784_);
v___x_786_ = v___x_774_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_a_789_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_771_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_771_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___boxed(lean_object* v_s_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(v_s_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_s_840_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(lean_object* v_lhs_854_, lean_object* v_rhs_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(v_lhs_854_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v___x_869_; 
lean_dec_ref(v___x_868_);
v___x_869_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(v_rhs_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
return v___x_869_;
}
else
{
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs___boxed(lean_object* v_lhs_870_, lean_object* v_rhs_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_870_, v_rhs_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_rhs_871_);
lean_dec_ref(v_lhs_870_);
return v_res_884_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0(void){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(lean_object* v_msg_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; lean_object* v___f_900_; lean_object* v___x_3741__overap_901_; lean_object* v___x_902_; 
v___x_899_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0);
v___f_900_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_900_, 0, v___x_899_);
v___x_3741__overap_901_ = lean_panic_fn_borrowed(v___f_900_, v_msg_886_);
lean_dec_ref(v___f_900_);
lean_inc(v___y_897_);
lean_inc_ref(v___y_896_);
lean_inc(v___y_895_);
lean_inc_ref(v___y_894_);
lean_inc(v___y_893_);
lean_inc_ref(v___y_892_);
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
lean_inc(v___y_889_);
lean_inc(v___y_888_);
lean_inc(v___y_887_);
v___x_902_ = lean_apply_12(v___x_3741__overap_901_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, lean_box(0));
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___boxed(lean_object* v_msg_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(v_msg_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec(v___y_905_);
lean_dec(v___y_904_);
return v_res_916_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_919_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1));
v___x_920_ = lean_unsigned_to_nat(4u);
v___x_921_ = lean_unsigned_to_nat(38u);
v___x_922_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0));
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_924_ = l_mkPanicMessageWithDecl(v___x_923_, v___x_922_, v___x_921_, v___x_920_, v___x_919_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(lean_object* v_as_x27_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
if (lean_obj_tag(v_as_x27_925_) == 0)
{
lean_object* v___x_939_; 
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v_b_926_);
return v___x_939_;
}
else
{
lean_object* v_head_940_; lean_object* v_tail_941_; lean_object* v_lhs_942_; lean_object* v_rhs_943_; uint8_t v___x_944_; uint8_t v___x_945_; uint8_t v___x_946_; 
v_head_940_ = lean_ctor_get(v_as_x27_925_, 0);
v_tail_941_ = lean_ctor_get(v_as_x27_925_, 1);
v_lhs_942_ = lean_ctor_get(v_head_940_, 0);
v_rhs_943_ = lean_ctor_get(v_head_940_, 1);
v___x_944_ = l_Lean_Grind_AC_Seq_compare(v_lhs_942_, v_rhs_943_);
v___x_945_ = 2;
v___x_946_ = l_instDecidableEqOrdering(v___x_944_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2);
v___x_948_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(v___x_947_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_959_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_959_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_959_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_959_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
if (lean_obj_tag(v_a_949_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; 
v_a_953_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_a_953_);
lean_dec_ref(v_a_949_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v_a_953_);
v___x_955_ = v___x_951_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
else
{
lean_object* v_a_957_; 
lean_del_object(v___x_951_);
v_a_957_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_a_957_);
lean_dec_ref(v_a_949_);
v_as_x27_925_ = v_tail_941_;
v_b_926_ = v_a_957_;
goto _start;
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
v_a_960_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_948_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_948_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v___x_968_; 
v___x_968_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_942_, v_rhs_943_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v___x_969_; 
lean_dec_ref(v___x_968_);
v___x_969_ = lean_box(0);
v_as_x27_925_ = v_tail_941_;
v_b_926_ = v___x_969_;
goto _start;
}
else
{
return v___x_968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___boxed(lean_object* v_as_x27_971_, lean_object* v_b_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_as_x27_971_, v_b_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec(v___y_974_);
lean_dec(v___y_973_);
lean_dec(v_as_x27_971_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v_basis_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref(v___x_998_);
v_basis_1000_ = lean_ctor_get(v_a_999_, 15);
lean_inc(v_basis_1000_);
lean_dec(v_a_999_);
v___x_1001_ = lean_box(0);
v___x_1002_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_basis_1000_, v___x_1001_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
lean_dec(v_basis_1000_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v___x_1002_, 0);
lean_dec(v_unused_1010_);
v___x_1004_ = v___x_1002_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_dec(v___x_1002_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1001_);
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1001_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
return v___x_1002_;
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_998_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_998_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis___boxed(lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec(v_a_1019_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1(lean_object* v_as_1032_, lean_object* v_as_x27_1033_, lean_object* v_b_1034_, lean_object* v_a_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_as_x27_1033_, v_b_1034_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___boxed(lean_object* v_as_1049_, lean_object* v_as_x27_1050_, lean_object* v_b_1051_, lean_object* v_a_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1(v_as_1049_, v_as_x27_1050_, v_b_1051_, v_a_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec(v_as_x27_1050_);
lean_dec(v_as_1049_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(lean_object* v_init_1066_, lean_object* v_x_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
lean_object* v_k_1080_; lean_object* v_l_1081_; lean_object* v_r_1082_; lean_object* v___x_1083_; 
v_k_1080_ = lean_ctor_get(v_x_1067_, 1);
v_l_1081_ = lean_ctor_get(v_x_1067_, 3);
v_r_1082_ = lean_ctor_get(v_x_1067_, 4);
v___x_1083_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v_init_1066_, v_l_1081_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_lhs_1084_; lean_object* v_rhs_1085_; lean_object* v___x_1086_; 
lean_dec_ref(v___x_1083_);
v_lhs_1084_ = lean_ctor_get(v_k_1080_, 0);
v_rhs_1085_ = lean_ctor_get(v_k_1080_, 1);
v___x_1086_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1084_, v_rhs_1085_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v___x_1087_; 
lean_dec_ref(v___x_1086_);
v___x_1087_ = lean_box(0);
v_init_1066_ = v___x_1087_;
v_x_1067_ = v_r_1082_;
goto _start;
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_a_1089_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1086_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1086_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
return v___x_1083_;
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_init_1066_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0___boxed(lean_object* v_init_1099_, lean_object* v_x_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v_init_1099_, v_x_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec(v_x_1100_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v_queue_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref(v___x_1126_);
v_queue_1128_ = lean_ctor_get(v_a_1127_, 14);
lean_inc(v_queue_1128_);
lean_dec(v_a_1127_);
v___x_1129_ = lean_box(0);
v___x_1130_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v___x_1129_, v_queue_1128_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_queue_1128_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v___x_1130_, 0);
lean_dec(v_unused_1138_);
v___x_1132_ = v___x_1130_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_dec(v___x_1130_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1129_);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1129_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v_a_1139_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1130_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1130_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_a_1147_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1126_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1126_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue___boxed(lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec(v_a_1155_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(lean_object* v_as_1171_, size_t v_sz_1172_, size_t v_i_1173_, lean_object* v_b_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_usize_dec_lt(v_i_1173_, v_sz_1172_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v_b_1174_);
return v___x_1188_;
}
else
{
lean_object* v_a_1189_; lean_object* v_lhs_1190_; lean_object* v_rhs_1191_; lean_object* v___x_1192_; 
lean_dec_ref(v_b_1174_);
v_a_1189_ = lean_array_uget_borrowed(v_as_1171_, v_i_1173_);
v_lhs_1190_ = lean_ctor_get(v_a_1189_, 0);
v_rhs_1191_ = lean_ctor_get(v_a_1189_, 1);
v___x_1192_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1190_, v_rhs_1191_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; 
lean_dec_ref(v___x_1192_);
v___x_1193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0));
v___x_1194_ = ((size_t)1ULL);
v___x_1195_ = lean_usize_add(v_i_1173_, v___x_1194_);
v_i_1173_ = v___x_1195_;
v_b_1174_ = v___x_1193_;
goto _start;
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_a_1197_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1192_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1192_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1205_, lean_object* v_sz_1206_, lean_object* v_i_1207_, lean_object* v_b_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
size_t v_sz_boxed_1221_; size_t v_i_boxed_1222_; lean_object* v_res_1223_; 
v_sz_boxed_1221_ = lean_unbox_usize(v_sz_1206_);
lean_dec(v_sz_1206_);
v_i_boxed_1222_ = lean_unbox_usize(v_i_1207_);
lean_dec(v_i_1207_);
v_res_1223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(v_as_1205_, v_sz_boxed_1221_, v_i_boxed_1222_, v_b_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v_as_1205_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(lean_object* v_as_1224_, size_t v_sz_1225_, size_t v_i_1226_, lean_object* v_b_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v___x_1240_; 
v___x_1240_ = lean_usize_dec_lt(v_i_1226_, v_sz_1225_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_b_1227_);
return v___x_1241_;
}
else
{
lean_object* v_a_1242_; lean_object* v_lhs_1243_; lean_object* v_rhs_1244_; lean_object* v___x_1245_; 
lean_dec_ref(v_b_1227_);
v_a_1242_ = lean_array_uget_borrowed(v_as_1224_, v_i_1226_);
v_lhs_1243_ = lean_ctor_get(v_a_1242_, 0);
v_rhs_1244_ = lean_ctor_get(v_a_1242_, 1);
v___x_1245_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1243_, v_rhs_1244_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; lean_object* v___x_1249_; 
lean_dec_ref(v___x_1245_);
v___x_1246_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0));
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = lean_usize_add(v_i_1226_, v___x_1247_);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(v_as_1224_, v_sz_1225_, v___x_1248_, v___x_1246_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1249_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
v_a_1250_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1245_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1245_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1___boxed(lean_object* v_as_1258_, lean_object* v_sz_1259_, lean_object* v_i_1260_, lean_object* v_b_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
size_t v_sz_boxed_1274_; size_t v_i_boxed_1275_; lean_object* v_res_1276_; 
v_sz_boxed_1274_ = lean_unbox_usize(v_sz_1259_);
lean_dec(v_sz_1259_);
v_i_boxed_1275_ = lean_unbox_usize(v_i_1260_);
lean_dec(v_i_1260_);
v_res_1276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(v_as_1258_, v_sz_boxed_1274_, v_i_boxed_1275_, v_b_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v_as_1258_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_1280_, size_t v_sz_1281_, size_t v_i_1282_, lean_object* v_b_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
uint8_t v___x_1296_; 
v___x_1296_ = lean_usize_dec_lt(v_i_1282_, v_sz_1281_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v_b_1283_);
return v___x_1297_;
}
else
{
lean_object* v_a_1298_; lean_object* v_lhs_1299_; lean_object* v_rhs_1300_; lean_object* v___x_1301_; 
lean_dec_ref(v_b_1283_);
v_a_1298_ = lean_array_uget_borrowed(v_as_1280_, v_i_1282_);
v_lhs_1299_ = lean_ctor_get(v_a_1298_, 0);
v_rhs_1300_ = lean_ctor_get(v_a_1298_, 1);
v___x_1301_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1299_, v_rhs_1300_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v___x_1302_; size_t v___x_1303_; size_t v___x_1304_; 
lean_dec_ref(v___x_1301_);
v___x_1302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_1303_ = ((size_t)1ULL);
v___x_1304_ = lean_usize_add(v_i_1282_, v___x_1303_);
v_i_1282_ = v___x_1304_;
v_b_1283_ = v___x_1302_;
goto _start;
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
v_a_1306_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1301_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1301_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_1314_, lean_object* v_sz_1315_, lean_object* v_i_1316_, lean_object* v_b_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
size_t v_sz_boxed_1330_; size_t v_i_boxed_1331_; lean_object* v_res_1332_; 
v_sz_boxed_1330_ = lean_unbox_usize(v_sz_1315_);
lean_dec(v_sz_1315_);
v_i_boxed_1331_ = lean_unbox_usize(v_i_1316_);
lean_dec(v_i_1316_);
v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_1314_, v_sz_boxed_1330_, v_i_boxed_1331_, v_b_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v_as_1314_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(lean_object* v_as_1333_, size_t v_sz_1334_, size_t v_i_1335_, lean_object* v_b_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v___x_1349_; 
v___x_1349_ = lean_usize_dec_lt(v_i_1335_, v_sz_1334_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v_b_1336_);
return v___x_1350_;
}
else
{
lean_object* v_a_1351_; lean_object* v_lhs_1352_; lean_object* v_rhs_1353_; lean_object* v___x_1354_; 
lean_dec_ref(v_b_1336_);
v_a_1351_ = lean_array_uget_borrowed(v_as_1333_, v_i_1335_);
v_lhs_1352_ = lean_ctor_get(v_a_1351_, 0);
v_rhs_1353_ = lean_ctor_get(v_a_1351_, 1);
v___x_1354_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1352_, v_rhs_1353_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
lean_dec_ref(v___x_1354_);
v___x_1355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_add(v_i_1335_, v___x_1356_);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_1333_, v_sz_1334_, v___x_1357_, v___x_1355_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
return v___x_1358_;
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_a_1359_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1354_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1354_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1367_, lean_object* v_sz_1368_, lean_object* v_i_1369_, lean_object* v_b_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
size_t v_sz_boxed_1383_; size_t v_i_boxed_1384_; lean_object* v_res_1385_; 
v_sz_boxed_1383_ = lean_unbox_usize(v_sz_1368_);
lean_dec(v_sz_1368_);
v_i_boxed_1384_ = lean_unbox_usize(v_i_1369_);
lean_dec(v_i_1369_);
v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(v_as_1367_, v_sz_boxed_1383_, v_i_boxed_1384_, v_b_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v_as_1367_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(lean_object* v_init_1386_, lean_object* v_n_1387_, lean_object* v_b_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
if (lean_obj_tag(v_n_1387_) == 0)
{
lean_object* v_cs_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; size_t v_sz_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v_cs_1401_ = lean_ctor_get(v_n_1387_, 0);
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
lean_ctor_set(v___x_1403_, 1, v_b_1388_);
v_sz_1404_ = lean_array_size(v_cs_1401_);
v___x_1405_ = ((size_t)0ULL);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(v_init_1386_, v_cs_1401_, v_sz_1404_, v___x_1405_, v___x_1403_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1421_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1421_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1421_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_fst_1411_; 
v_fst_1411_ = lean_ctor_get(v_a_1407_, 0);
if (lean_obj_tag(v_fst_1411_) == 0)
{
lean_object* v_snd_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v_snd_1412_ = lean_ctor_get(v_a_1407_, 1);
lean_inc(v_snd_1412_);
lean_dec(v_a_1407_);
v___x_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1413_, 0, v_snd_1412_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1413_);
v___x_1415_ = v___x_1409_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
else
{
lean_object* v_val_1417_; lean_object* v___x_1419_; 
lean_inc_ref(v_fst_1411_);
lean_dec(v_a_1407_);
v_val_1417_ = lean_ctor_get(v_fst_1411_, 0);
lean_inc(v_val_1417_);
lean_dec_ref(v_fst_1411_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v_val_1417_);
v___x_1419_ = v___x_1409_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_val_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_a_1422_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1406_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1406_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_vs_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; size_t v_sz_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v_vs_1430_ = lean_ctor_get(v_n_1387_, 0);
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v_b_1388_);
v_sz_1433_ = lean_array_size(v_vs_1430_);
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(v_vs_1430_, v_sz_1433_, v___x_1434_, v___x_1432_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1450_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1450_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1450_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_fst_1440_; 
v_fst_1440_ = lean_ctor_get(v_a_1436_, 0);
if (lean_obj_tag(v_fst_1440_) == 0)
{
lean_object* v_snd_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v_snd_1441_ = lean_ctor_get(v_a_1436_, 1);
lean_inc(v_snd_1441_);
lean_dec(v_a_1436_);
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_snd_1441_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1442_);
v___x_1444_ = v___x_1438_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
else
{
lean_object* v_val_1446_; lean_object* v___x_1448_; 
lean_inc_ref(v_fst_1440_);
lean_dec(v_a_1436_);
v_val_1446_ = lean_ctor_get(v_fst_1440_, 0);
lean_inc(v_val_1446_);
lean_dec_ref(v_fst_1440_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v_val_1446_);
v___x_1448_ = v___x_1438_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_val_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_a_1451_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1435_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1435_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
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
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_1459_, lean_object* v_as_1460_, size_t v_sz_1461_, size_t v_i_1462_, lean_object* v_b_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
uint8_t v___x_1476_; 
v___x_1476_ = lean_usize_dec_lt(v_i_1462_, v_sz_1461_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_b_1463_);
return v___x_1477_;
}
else
{
lean_object* v_snd_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1512_; 
v_snd_1478_ = lean_ctor_get(v_b_1463_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_b_1463_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v_b_1463_, 0);
lean_dec(v_unused_1513_);
v___x_1480_ = v_b_1463_;
v_isShared_1481_ = v_isSharedCheck_1512_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_snd_1478_);
lean_dec(v_b_1463_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1512_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v_a_1482_; lean_object* v___x_1483_; 
v_a_1482_ = lean_array_uget_borrowed(v_as_1460_, v_i_1462_);
lean_inc(v_snd_1478_);
v___x_1483_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_1459_, v_a_1482_, v_snd_1478_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1503_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1503_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1503_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
if (lean_obj_tag(v_a_1484_) == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1488_, 0, v_a_1484_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1488_);
v___x_1490_ = v___x_1480_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_snd_1478_);
v___x_1490_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1492_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1490_);
v___x_1492_ = v___x_1486_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
lean_del_object(v___x_1486_);
lean_dec(v_snd_1478_);
v_a_1495_ = lean_ctor_get(v_a_1484_, 0);
lean_inc(v_a_1495_);
lean_dec_ref(v_a_1484_);
v___x_1496_ = lean_box(0);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v_a_1495_);
lean_ctor_set(v___x_1480_, 0, v___x_1496_);
v___x_1498_ = v___x_1480_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_a_1495_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
size_t v___x_1499_; size_t v___x_1500_; 
v___x_1499_ = ((size_t)1ULL);
v___x_1500_ = lean_usize_add(v_i_1462_, v___x_1499_);
v_i_1462_ = v___x_1500_;
v_b_1463_ = v___x_1498_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_del_object(v___x_1480_);
lean_dec(v_snd_1478_);
v_a_1504_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1483_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1483_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1514_ = _args[0];
lean_object* v_as_1515_ = _args[1];
lean_object* v_sz_1516_ = _args[2];
lean_object* v_i_1517_ = _args[3];
lean_object* v_b_1518_ = _args[4];
lean_object* v___y_1519_ = _args[5];
lean_object* v___y_1520_ = _args[6];
lean_object* v___y_1521_ = _args[7];
lean_object* v___y_1522_ = _args[8];
lean_object* v___y_1523_ = _args[9];
lean_object* v___y_1524_ = _args[10];
lean_object* v___y_1525_ = _args[11];
lean_object* v___y_1526_ = _args[12];
lean_object* v___y_1527_ = _args[13];
lean_object* v___y_1528_ = _args[14];
lean_object* v___y_1529_ = _args[15];
lean_object* v___y_1530_ = _args[16];
_start:
{
size_t v_sz_boxed_1531_; size_t v_i_boxed_1532_; lean_object* v_res_1533_; 
v_sz_boxed_1531_ = lean_unbox_usize(v_sz_1516_);
lean_dec(v_sz_1516_);
v_i_boxed_1532_ = lean_unbox_usize(v_i_1517_);
lean_dec(v_i_1517_);
v_res_1533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(v_init_1514_, v_as_1515_, v_sz_boxed_1531_, v_i_boxed_1532_, v_b_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v_as_1515_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0___boxed(lean_object* v_init_1534_, lean_object* v_n_1535_, lean_object* v_b_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_1534_, v_n_1535_, v_b_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v_n_1535_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(lean_object* v_t_1550_, lean_object* v_init_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_root_1564_; lean_object* v_tail_1565_; lean_object* v___x_1566_; 
v_root_1564_ = lean_ctor_get(v_t_1550_, 0);
v_tail_1565_ = lean_ctor_get(v_t_1550_, 1);
v___x_1566_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_1551_, v_root_1564_, v_init_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1603_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1603_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1603_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
if (lean_obj_tag(v_a_1567_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; 
v_a_1571_ = lean_ctor_get(v_a_1567_, 0);
lean_inc(v_a_1571_);
lean_dec_ref(v_a_1567_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v_a_1571_);
v___x_1573_ = v___x_1569_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; size_t v_sz_1578_; size_t v___x_1579_; lean_object* v___x_1580_; 
lean_del_object(v___x_1569_);
v_a_1575_ = lean_ctor_get(v_a_1567_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v_a_1567_);
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
lean_ctor_set(v___x_1577_, 1, v_a_1575_);
v_sz_1578_ = lean_array_size(v_tail_1565_);
v___x_1579_ = ((size_t)0ULL);
v___x_1580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(v_tail_1565_, v_sz_1578_, v___x_1579_, v___x_1577_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1594_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1594_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1594_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_fst_1585_; 
v_fst_1585_ = lean_ctor_get(v_a_1581_, 0);
if (lean_obj_tag(v_fst_1585_) == 0)
{
lean_object* v_snd_1586_; lean_object* v___x_1588_; 
v_snd_1586_ = lean_ctor_get(v_a_1581_, 1);
lean_inc(v_snd_1586_);
lean_dec(v_a_1581_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v_snd_1586_);
v___x_1588_ = v___x_1583_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_snd_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
else
{
lean_object* v_val_1590_; lean_object* v___x_1592_; 
lean_inc_ref(v_fst_1585_);
lean_dec(v_a_1581_);
v_val_1590_ = lean_ctor_get(v_fst_1585_, 0);
lean_inc(v_val_1590_);
lean_dec_ref(v_fst_1585_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v_val_1590_);
v___x_1592_ = v___x_1583_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_val_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
v_a_1595_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1580_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1580_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_a_1604_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1566_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1566_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0___boxed(lean_object* v_t_1612_, lean_object* v_init_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(v_t_1612_, v_init_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v_t_1612_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v_diseqs_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1639_);
v_diseqs_1641_ = lean_ctor_get(v_a_1640_, 16);
lean_inc_ref(v_diseqs_1641_);
lean_dec(v_a_1640_);
v___x_1642_ = lean_box(0);
v___x_1643_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(v_diseqs_1641_, v___x_1642_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_);
lean_dec_ref(v_diseqs_1641_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v___x_1643_, 0);
lean_dec(v_unused_1651_);
v___x_1645_ = v___x_1643_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_dec(v___x_1643_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1642_);
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1642_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
return v___x_1643_;
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
v_a_1652_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1639_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1639_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs___boxed(lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec(v_a_1660_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v___x_1686_; 
lean_dec_ref(v___x_1685_);
v___x_1686_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v___x_1687_; 
lean_dec_ref(v___x_1686_);
v___x_1687_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v___x_1688_; 
lean_dec_ref(v___x_1687_);
v___x_1688_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1688_;
}
else
{
return v___x_1687_;
}
}
else
{
return v___x_1686_;
}
}
else
{
return v___x_1685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs___boxed(lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
lean_dec(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec(v_a_1689_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(lean_object* v_upperBound_1702_, lean_object* v_a_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_nat_dec_lt(v_a_1703_, v_upperBound_1702_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec(v_a_1703_);
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_b_1704_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; 
v___x_1718_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(v_a_1703_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec_ref(v___x_1718_);
v___x_1719_ = lean_box(0);
v___x_1720_ = lean_unsigned_to_nat(1u);
v___x_1721_ = lean_nat_add(v_a_1703_, v___x_1720_);
lean_dec(v_a_1703_);
v_a_1703_ = v___x_1721_;
v_b_1704_ = v___x_1719_;
goto _start;
}
else
{
lean_dec(v_a_1703_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg___boxed(lean_object* v_upperBound_1723_, lean_object* v_a_1724_, lean_object* v_b_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(v_upperBound_1723_, v_a_1724_, v_b_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec(v_upperBound_1723_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkInvariants(lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
uint8_t v_debug_1749_; 
v_debug_1749_ = lean_ctor_get_uint8(v_a_1740_, sizeof(void*)*7 + 2);
if (v_debug_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_1738_, v_a_1746_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v_structs_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___x_1752_);
v_structs_1754_ = lean_ctor_get(v_a_1753_, 0);
lean_inc_ref(v_structs_1754_);
lean_dec(v_a_1753_);
v___x_1755_ = lean_array_get_size(v_structs_1754_);
lean_dec_ref(v_structs_1754_);
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = lean_box(0);
v___x_1758_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(v___x_1755_, v___x_1756_, v___x_1757_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1758_, 0);
lean_dec(v_unused_1766_);
v___x_1760_ = v___x_1758_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_dec(v___x_1758_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1757_);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1757_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
else
{
return v___x_1758_;
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_a_1767_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1752_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1752_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkInvariants___boxed(lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Meta_Grind_AC_checkInvariants(v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
lean_dec(v_a_1776_);
lean_dec(v_a_1775_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0(lean_object* v_upperBound_1787_, lean_object* v_inst_1788_, lean_object* v_R_1789_, lean_object* v_a_1790_, lean_object* v_b_1791_, lean_object* v_c_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(v_upperBound_1787_, v_a_1790_, v_b_1791_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1805_ = _args[0];
lean_object* v_inst_1806_ = _args[1];
lean_object* v_R_1807_ = _args[2];
lean_object* v_a_1808_ = _args[3];
lean_object* v_b_1809_ = _args[4];
lean_object* v_c_1810_ = _args[5];
lean_object* v___y_1811_ = _args[6];
lean_object* v___y_1812_ = _args[7];
lean_object* v___y_1813_ = _args[8];
lean_object* v___y_1814_ = _args[9];
lean_object* v___y_1815_ = _args[10];
lean_object* v___y_1816_ = _args[11];
lean_object* v___y_1817_ = _args[12];
lean_object* v___y_1818_ = _args[13];
lean_object* v___y_1819_ = _args[14];
lean_object* v___y_1820_ = _args[15];
lean_object* v___y_1821_ = _args[16];
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0(v_upperBound_1805_, v_inst_1806_, v_R_1807_, v_a_1808_, v_b_1809_, v_c_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec(v_upperBound_1805_);
return v_res_1822_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Inv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_AC_Inv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Inv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_AC_Inv(builtin);
}
#ifdef __cplusplus
}
#endif
