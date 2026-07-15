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
size_t lean_ptr_addr(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 184, .m_capacity = 184, .m_length = 183, .m_data = "assertion violation: s.vars.size == num\n\n/-\n**Note**: Elements in the todo queue are not fully simplified.\nRecall that we only (fully) simplify them when adding them to the basis.\n-/\n"};
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "assertion violation: !s.contains 0 || s == .var 0\n    "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "assertion violation: s.isSorted\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_15_; lean_object* v___f_16_; lean_object* v___x_5544__overap_17_; lean_object* v___x_18_; 
v___x_15_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0);
v___f_16_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_16_, 0, v___x_15_);
v___x_5544__overap_17_ = lean_panic_fn_borrowed(v___f_16_, v_msg_2_);
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
v___x_18_ = lean_apply_12(v___x_5544__overap_17_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, lean_box(0));
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
lean_object* v___x_47_; lean_object* v___f_48_; lean_object* v___x_5562__overap_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0);
v___f_48_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_48_, 0, v___x_47_);
v___x_5562__overap_49_ = lean_panic_fn_borrowed(v___f_48_, v_msg_34_);
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
v___x_50_ = lean_apply_12(v___x_5562__overap_49_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
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
lean_object* v___x_115_; lean_object* v___x_116_; size_t v___x_117_; size_t v___x_118_; uint8_t v___x_119_; 
v___x_115_ = l_Lean_instInhabitedExpr;
v___x_116_ = l_Lean_PersistentArray_get_x21___redArg(v___x_115_, v_vars_81_, v_snd_102_);
v___x_117_ = lean_ptr_addr(v_fst_101_);
v___x_118_ = lean_ptr_addr(v___x_116_);
lean_dec(v___x_116_);
v___x_119_ = lean_usize_dec_eq(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5);
v___x_121_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1(v___x_120_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
return v___x_121_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___boxed(lean_object* v_vars_122_, lean_object* v_x_123_, lean_object* v_____s_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0(v_vars_122_, v_x_123_, v_____s_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec(v___y_126_);
lean_dec(v___y_125_);
lean_dec(v_____s_124_);
lean_dec_ref(v_x_123_);
lean_dec_ref(v_vars_122_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0(lean_object* v_f_138_, lean_object* v_s_139_, lean_object* v_a_140_, lean_object* v_b_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v_a_140_);
lean_ctor_set(v___x_154_, 1, v_b_141_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v___y_146_);
lean_inc_ref(v___y_145_);
lean_inc(v___y_144_);
lean_inc(v___y_143_);
lean_inc(v___y_142_);
v___x_155_ = lean_apply_14(v_f_138_, v___x_154_, v_s_139_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, lean_box(0));
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_182_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_182_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_182_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_182_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
if (lean_obj_tag(v_a_156_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_170_; 
v_a_160_ = lean_ctor_get(v_a_156_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v_a_156_);
if (v_isSharedCheck_170_ == 0)
{
v___x_162_ = v_a_156_;
v_isShared_163_ = v_isSharedCheck_170_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v_a_156_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_170_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_169_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_165_);
v___x_167_ = v___x_158_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_181_; 
v_a_171_ = lean_ctor_get(v_a_156_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_a_156_);
if (v_isSharedCheck_181_ == 0)
{
v___x_173_ = v_a_156_;
v_isShared_174_ = v_isSharedCheck_181_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v_a_156_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_181_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_180_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_178_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_176_);
v___x_178_ = v___x_158_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_a_183_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_155_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_155_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0___boxed(lean_object* v_f_191_, lean_object* v_s_192_, lean_object* v_a_193_, lean_object* v_b_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0(v_f_191_, v_s_192_, v_a_193_, v_b_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec(v___y_196_);
lean_dec(v___y_195_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(lean_object* v_f_208_, lean_object* v_keys_209_, lean_object* v_vals_210_, lean_object* v_i_211_, lean_object* v_acc_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = lean_array_get_size(v_keys_209_);
v___x_226_ = lean_nat_dec_lt(v_i_211_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec(v_i_211_);
lean_dec_ref(v_f_208_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v_acc_212_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
else
{
lean_object* v_k_229_; lean_object* v_v_230_; lean_object* v___x_231_; 
v_k_229_ = lean_array_fget_borrowed(v_keys_209_, v_i_211_);
v_v_230_ = lean_array_fget_borrowed(v_vals_210_, v_i_211_);
lean_inc_ref(v_f_208_);
lean_inc(v___y_223_);
lean_inc_ref(v___y_222_);
lean_inc(v___y_221_);
lean_inc_ref(v___y_220_);
lean_inc(v___y_219_);
lean_inc_ref(v___y_218_);
lean_inc(v___y_217_);
lean_inc_ref(v___y_216_);
lean_inc(v___y_215_);
lean_inc(v___y_214_);
lean_inc(v___y_213_);
lean_inc(v_v_230_);
lean_inc(v_k_229_);
v___x_231_ = lean_apply_15(v_f_208_, v_acc_212_, v_k_229_, v_v_230_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, lean_box(0));
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
if (lean_obj_tag(v_a_232_) == 0)
{
lean_dec_ref_known(v_a_232_, 1);
lean_dec(v_i_211_);
lean_dec_ref(v_f_208_);
return v___x_231_;
}
else
{
lean_object* v_a_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec_ref_known(v___x_231_, 1);
v_a_233_ = lean_ctor_get(v_a_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref_known(v_a_232_, 1);
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = lean_nat_add(v_i_211_, v___x_234_);
lean_dec(v_i_211_);
v_i_211_ = v___x_235_;
v_acc_212_ = v_a_233_;
goto _start;
}
}
else
{
lean_dec(v_i_211_);
lean_dec_ref(v_f_208_);
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_f_237_ = _args[0];
lean_object* v_keys_238_ = _args[1];
lean_object* v_vals_239_ = _args[2];
lean_object* v_i_240_ = _args[3];
lean_object* v_acc_241_ = _args[4];
lean_object* v___y_242_ = _args[5];
lean_object* v___y_243_ = _args[6];
lean_object* v___y_244_ = _args[7];
lean_object* v___y_245_ = _args[8];
lean_object* v___y_246_ = _args[9];
lean_object* v___y_247_ = _args[10];
lean_object* v___y_248_ = _args[11];
lean_object* v___y_249_ = _args[12];
lean_object* v___y_250_ = _args[13];
lean_object* v___y_251_ = _args[14];
lean_object* v___y_252_ = _args[15];
lean_object* v___y_253_ = _args[16];
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_237_, v_keys_238_, v_vals_239_, v_i_240_, v_acc_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v_vals_239_);
lean_dec_ref(v_keys_238_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(lean_object* v_f_255_, lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
lean_object* v_es_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_292_; 
v_es_270_ = lean_ctor_get(v_x_256_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v_x_256_);
if (v_isSharedCheck_292_ == 0)
{
v___x_272_ = v_x_256_;
v_isShared_273_ = v_isSharedCheck_292_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_es_270_);
lean_dec(v_x_256_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_292_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_array_get_size(v_es_270_);
v___x_276_ = lean_nat_dec_lt(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_278_; 
lean_dec_ref(v_es_270_);
lean_dec_ref(v_f_255_);
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 1);
lean_ctor_set(v___x_272_, 0, v_x_257_);
v___x_278_ = v___x_272_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_x_257_);
v___x_278_ = v_reuseFailAlloc_280_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; 
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
else
{
uint8_t v___x_281_; 
v___x_281_ = lean_nat_dec_le(v___x_275_, v___x_275_);
if (v___x_281_ == 0)
{
if (v___x_276_ == 0)
{
lean_object* v___x_283_; 
lean_dec_ref(v_es_270_);
lean_dec_ref(v_f_255_);
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 1);
lean_ctor_set(v___x_272_, 0, v_x_257_);
v___x_283_ = v___x_272_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_x_257_);
v___x_283_ = v_reuseFailAlloc_285_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; 
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
else
{
size_t v___x_286_; size_t v___x_287_; lean_object* v___x_288_; 
lean_del_object(v___x_272_);
v___x_286_ = ((size_t)0ULL);
v___x_287_ = lean_usize_of_nat(v___x_275_);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_255_, v_es_270_, v___x_286_, v___x_287_, v_x_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec_ref(v_es_270_);
return v___x_288_;
}
}
else
{
size_t v___x_289_; size_t v___x_290_; lean_object* v___x_291_; 
lean_del_object(v___x_272_);
v___x_289_ = ((size_t)0ULL);
v___x_290_ = lean_usize_of_nat(v___x_275_);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_255_, v_es_270_, v___x_289_, v___x_290_, v_x_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec_ref(v_es_270_);
return v___x_291_;
}
}
}
}
else
{
lean_object* v_ks_293_; lean_object* v_vs_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_ks_293_ = lean_ctor_get(v_x_256_, 0);
lean_inc_ref(v_ks_293_);
v_vs_294_ = lean_ctor_get(v_x_256_, 1);
lean_inc_ref(v_vs_294_);
lean_dec_ref_known(v_x_256_, 2);
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_255_, v_ks_293_, v_vs_294_, v___x_295_, v_x_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec_ref(v_vs_294_);
lean_dec_ref(v_ks_293_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_f_297_, lean_object* v_as_298_, size_t v_i_299_, size_t v_stop_300_, lean_object* v_b_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_a_315_; lean_object* v___y_320_; uint8_t v___x_323_; 
v___x_323_ = lean_usize_dec_eq(v_i_299_, v_stop_300_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
v___x_324_ = lean_array_uget_borrowed(v_as_298_, v_i_299_);
switch(lean_obj_tag(v___x_324_))
{
case 0:
{
lean_object* v_key_325_; lean_object* v_val_326_; lean_object* v___x_327_; 
v_key_325_ = lean_ctor_get(v___x_324_, 0);
v_val_326_ = lean_ctor_get(v___x_324_, 1);
lean_inc_ref(v_f_297_);
lean_inc(v___y_312_);
lean_inc_ref(v___y_311_);
lean_inc(v___y_310_);
lean_inc_ref(v___y_309_);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
lean_inc(v___y_304_);
lean_inc(v___y_303_);
lean_inc(v___y_302_);
lean_inc(v_val_326_);
lean_inc(v_key_325_);
v___x_327_ = lean_apply_15(v_f_297_, v_b_301_, v_key_325_, v_val_326_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, lean_box(0));
v___y_320_ = v___x_327_;
goto v___jp_319_;
}
case 1:
{
lean_object* v_node_328_; lean_object* v___x_329_; 
v_node_328_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_node_328_);
lean_inc_ref(v_f_297_);
v___x_329_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_297_, v_node_328_, v_b_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
v___y_320_ = v___x_329_;
goto v___jp_319_;
}
default: 
{
v_a_315_ = v_b_301_;
goto v___jp_314_;
}
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec_ref(v_f_297_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v_b_301_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
v___jp_314_:
{
size_t v___x_316_; size_t v___x_317_; 
v___x_316_ = ((size_t)1ULL);
v___x_317_ = lean_usize_add(v_i_299_, v___x_316_);
v_i_299_ = v___x_317_;
v_b_301_ = v_a_315_;
goto _start;
}
v___jp_319_:
{
if (lean_obj_tag(v___y_320_) == 0)
{
lean_object* v_a_321_; 
v_a_321_ = lean_ctor_get(v___y_320_, 0);
if (lean_obj_tag(v_a_321_) == 0)
{
lean_dec_ref(v_f_297_);
return v___y_320_;
}
else
{
lean_object* v_a_322_; 
lean_inc_ref(v_a_321_);
lean_dec_ref_known(v___y_320_, 1);
v_a_322_ = lean_ctor_get(v_a_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v_a_321_, 1);
v_a_315_ = v_a_322_;
goto v___jp_314_;
}
}
else
{
lean_dec_ref(v_f_297_);
return v___y_320_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_f_332_ = _args[0];
lean_object* v_as_333_ = _args[1];
lean_object* v_i_334_ = _args[2];
lean_object* v_stop_335_ = _args[3];
lean_object* v_b_336_ = _args[4];
lean_object* v___y_337_ = _args[5];
lean_object* v___y_338_ = _args[6];
lean_object* v___y_339_ = _args[7];
lean_object* v___y_340_ = _args[8];
lean_object* v___y_341_ = _args[9];
lean_object* v___y_342_ = _args[10];
lean_object* v___y_343_ = _args[11];
lean_object* v___y_344_ = _args[12];
lean_object* v___y_345_ = _args[13];
lean_object* v___y_346_ = _args[14];
lean_object* v___y_347_ = _args[15];
lean_object* v___y_348_ = _args[16];
_start:
{
size_t v_i_boxed_349_; size_t v_stop_boxed_350_; lean_object* v_res_351_; 
v_i_boxed_349_ = lean_unbox_usize(v_i_334_);
lean_dec(v_i_334_);
v_stop_boxed_350_ = lean_unbox_usize(v_stop_335_);
lean_dec(v_stop_335_);
v_res_351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_332_, v_as_333_, v_i_boxed_349_, v_stop_boxed_350_, v_b_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v_as_333_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_f_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_352_, v_x_353_, v_x_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec(v___y_356_);
lean_dec(v___y_355_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(lean_object* v_map_368_, lean_object* v_init_369_, lean_object* v_f_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___f_383_; lean_object* v___x_384_; 
v___f_383_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0___boxed), 16, 1);
lean_closure_set(v___f_383_, 0, v_f_370_);
lean_inc_ref(v_map_368_);
v___x_384_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v___f_383_, v_map_368_, v_init_369_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_393_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_393_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_a_389_; lean_object* v___x_391_; 
v_a_389_ = lean_ctor_get(v_a_385_, 0);
lean_inc(v_a_389_);
lean_dec(v_a_385_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v_a_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
v_a_394_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_384_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_384_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___boxed(lean_object* v_map_402_, lean_object* v_init_403_, lean_object* v_f_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_map_402_, v_init_403_, v_f_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
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
lean_dec(v___y_405_);
lean_dec_ref(v_map_402_);
return v_res_417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0));
v___x_420_ = lean_unsigned_to_nat(2u);
v___x_421_ = lean_unsigned_to_nat(23u);
v___x_422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1));
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_424_ = l_mkPanicMessageWithDecl(v___x_423_, v___x_422_, v___x_421_, v___x_420_, v___x_419_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v_vars_439_; lean_object* v_varMap_440_; lean_object* v___f_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v_vars_439_ = lean_ctor_get(v_a_438_, 10);
lean_inc_ref_n(v_vars_439_, 2);
v_varMap_440_ = lean_ctor_get(v_a_438_, 11);
lean_inc_ref(v_varMap_440_);
lean_dec(v_a_438_);
v___f_441_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___boxed), 15, 1);
lean_closure_set(v___f_441_, 0, v_vars_439_);
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_varMap_440_, v___x_442_, v___f_441_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec_ref(v_varMap_440_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_456_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_456_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_456_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_456_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_size_448_; uint8_t v___x_449_; 
v_size_448_ = lean_ctor_get(v_vars_439_, 2);
lean_inc(v_size_448_);
lean_dec_ref(v_vars_439_);
v___x_449_ = lean_nat_dec_eq(v_size_448_, v_a_444_);
lean_dec(v_a_444_);
lean_dec(v_size_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_del_object(v___x_446_);
v___x_450_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1);
v___x_451_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_450_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
return v___x_451_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = lean_box(0);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_452_);
v___x_454_ = v___x_446_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec_ref(v_vars_439_);
v_a_457_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_443_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_443_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_a_465_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_437_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_437_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___boxed(lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec(v_a_474_);
lean_dec(v_a_473_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2(lean_object* v_00_u03c3_486_, lean_object* v_00_u03b2_487_, lean_object* v_map_488_, lean_object* v_init_489_, lean_object* v_f_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_map_488_, v_init_489_, v_f_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_504_ = _args[0];
lean_object* v_00_u03b2_505_ = _args[1];
lean_object* v_map_506_ = _args[2];
lean_object* v_init_507_ = _args[3];
lean_object* v_f_508_ = _args[4];
lean_object* v___y_509_ = _args[5];
lean_object* v___y_510_ = _args[6];
lean_object* v___y_511_ = _args[7];
lean_object* v___y_512_ = _args[8];
lean_object* v___y_513_ = _args[9];
lean_object* v___y_514_ = _args[10];
lean_object* v___y_515_ = _args[11];
lean_object* v___y_516_ = _args[12];
lean_object* v___y_517_ = _args[13];
lean_object* v___y_518_ = _args[14];
lean_object* v___y_519_ = _args[15];
lean_object* v___y_520_ = _args[16];
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2(v_00_u03c3_504_, v_00_u03b2_505_, v_map_506_, v_init_507_, v_f_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v_map_506_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg(lean_object* v_map_522_, lean_object* v_f_523_, lean_object* v_init_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_523_, v_map_522_, v_init_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg___boxed(lean_object* v_map_538_, lean_object* v_f_539_, lean_object* v_init_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg(v_map_538_, v_f_539_, v_init_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec(v___y_542_);
lean_dec(v___y_541_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2(lean_object* v_00_u03c3_554_, lean_object* v_00_u03c3_555_, lean_object* v_00_u03b2_556_, lean_object* v_map_557_, lean_object* v_f_558_, lean_object* v_init_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_558_, v_map_557_, v_init_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_573_ = _args[0];
lean_object* v_00_u03c3_574_ = _args[1];
lean_object* v_00_u03b2_575_ = _args[2];
lean_object* v_map_576_ = _args[3];
lean_object* v_f_577_ = _args[4];
lean_object* v_init_578_ = _args[5];
lean_object* v___y_579_ = _args[6];
lean_object* v___y_580_ = _args[7];
lean_object* v___y_581_ = _args[8];
lean_object* v___y_582_ = _args[9];
lean_object* v___y_583_ = _args[10];
lean_object* v___y_584_ = _args[11];
lean_object* v___y_585_ = _args[12];
lean_object* v___y_586_ = _args[13];
lean_object* v___y_587_ = _args[14];
lean_object* v___y_588_ = _args[15];
lean_object* v___y_589_ = _args[16];
lean_object* v___y_590_ = _args[17];
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2(v_00_u03c3_573_, v_00_u03c3_574_, v_00_u03b2_575_, v_map_576_, v_f_577_, v_init_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec(v___y_580_);
lean_dec(v___y_579_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3(lean_object* v_00_u03c3_592_, lean_object* v_00_u03c3_593_, lean_object* v_00_u03b1_594_, lean_object* v_00_u03b2_595_, lean_object* v_f_596_, lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_596_, v_x_597_, v_x_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03c3_612_ = _args[0];
lean_object* v_00_u03c3_613_ = _args[1];
lean_object* v_00_u03b1_614_ = _args[2];
lean_object* v_00_u03b2_615_ = _args[3];
lean_object* v_f_616_ = _args[4];
lean_object* v_x_617_ = _args[5];
lean_object* v_x_618_ = _args[6];
lean_object* v___y_619_ = _args[7];
lean_object* v___y_620_ = _args[8];
lean_object* v___y_621_ = _args[9];
lean_object* v___y_622_ = _args[10];
lean_object* v___y_623_ = _args[11];
lean_object* v___y_624_ = _args[12];
lean_object* v___y_625_ = _args[13];
lean_object* v___y_626_ = _args[14];
lean_object* v___y_627_ = _args[15];
lean_object* v___y_628_ = _args[16];
lean_object* v___y_629_ = _args[17];
lean_object* v___y_630_ = _args[18];
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3(v_00_u03c3_612_, v_00_u03c3_613_, v_00_u03b1_614_, v_00_u03b2_615_, v_f_616_, v_x_617_, v_x_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec(v___y_620_);
lean_dec(v___y_619_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_632_, lean_object* v_00_u03b2_633_, lean_object* v_00_u03c3_634_, lean_object* v_00_u03c3_635_, lean_object* v_f_636_, lean_object* v_as_637_, size_t v_i_638_, size_t v_stop_639_, lean_object* v_b_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_636_, v_as_637_, v_i_638_, v_stop_639_, v_b_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_00_u03b1_654_ = _args[0];
lean_object* v_00_u03b2_655_ = _args[1];
lean_object* v_00_u03c3_656_ = _args[2];
lean_object* v_00_u03c3_657_ = _args[3];
lean_object* v_f_658_ = _args[4];
lean_object* v_as_659_ = _args[5];
lean_object* v_i_660_ = _args[6];
lean_object* v_stop_661_ = _args[7];
lean_object* v_b_662_ = _args[8];
lean_object* v___y_663_ = _args[9];
lean_object* v___y_664_ = _args[10];
lean_object* v___y_665_ = _args[11];
lean_object* v___y_666_ = _args[12];
lean_object* v___y_667_ = _args[13];
lean_object* v___y_668_ = _args[14];
lean_object* v___y_669_ = _args[15];
lean_object* v___y_670_ = _args[16];
lean_object* v___y_671_ = _args[17];
lean_object* v___y_672_ = _args[18];
lean_object* v___y_673_ = _args[19];
lean_object* v___y_674_ = _args[20];
_start:
{
size_t v_i_boxed_675_; size_t v_stop_boxed_676_; lean_object* v_res_677_; 
v_i_boxed_675_ = lean_unbox_usize(v_i_660_);
lean_dec(v_i_660_);
v_stop_boxed_676_ = lean_unbox_usize(v_stop_661_);
lean_dec(v_stop_661_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4(v_00_u03b1_654_, v_00_u03b2_655_, v_00_u03c3_656_, v_00_u03c3_657_, v_f_658_, v_as_659_, v_i_boxed_675_, v_stop_boxed_676_, v_b_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v_as_659_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_678_, lean_object* v_00_u03c3_679_, lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_f_682_, lean_object* v_keys_683_, lean_object* v_vals_684_, lean_object* v_heq_685_, lean_object* v_i_686_, lean_object* v_acc_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_682_, v_keys_683_, v_vals_684_, v_i_686_, v_acc_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_00_u03c3_701_ = _args[0];
lean_object* v_00_u03c3_702_ = _args[1];
lean_object* v_00_u03b1_703_ = _args[2];
lean_object* v_00_u03b2_704_ = _args[3];
lean_object* v_f_705_ = _args[4];
lean_object* v_keys_706_ = _args[5];
lean_object* v_vals_707_ = _args[6];
lean_object* v_heq_708_ = _args[7];
lean_object* v_i_709_ = _args[8];
lean_object* v_acc_710_ = _args[9];
lean_object* v___y_711_ = _args[10];
lean_object* v___y_712_ = _args[11];
lean_object* v___y_713_ = _args[12];
lean_object* v___y_714_ = _args[13];
lean_object* v___y_715_ = _args[14];
lean_object* v___y_716_ = _args[15];
lean_object* v___y_717_ = _args[16];
lean_object* v___y_718_ = _args[17];
lean_object* v___y_719_ = _args[18];
lean_object* v___y_720_ = _args[19];
lean_object* v___y_721_ = _args[20];
lean_object* v___y_722_ = _args[21];
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5(v_00_u03c3_701_, v_00_u03c3_702_, v_00_u03b1_703_, v_00_u03b2_704_, v_f_705_, v_keys_706_, v_vals_707_, v_heq_708_, v_i_709_, v_acc_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v_vals_707_);
lean_dec_ref(v_keys_706_);
return v_res_723_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1));
v___x_727_ = lean_unsigned_to_nat(6u);
v___x_728_ = lean_unsigned_to_nat(36u);
v___x_729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0));
v___x_730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_731_ = l_mkPanicMessageWithDecl(v___x_730_, v___x_729_, v___x_728_, v___x_727_, v___x_726_);
return v___x_731_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4));
v___x_736_ = lean_unsigned_to_nat(6u);
v___x_737_ = lean_unsigned_to_nat(34u);
v___x_738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0));
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_740_ = l_mkPanicMessageWithDecl(v___x_739_, v___x_738_, v___x_737_, v___x_736_, v___x_735_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6));
v___x_743_ = lean_unsigned_to_nat(4u);
v___x_744_ = lean_unsigned_to_nat(31u);
v___x_745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0));
v___x_746_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_747_ = l_mkPanicMessageWithDecl(v___x_746_, v___x_745_, v___x_744_, v___x_743_, v___x_742_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(lean_object* v_s_748_, uint8_t v_simplified_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___x_800_; 
v___x_800_ = l_Lean_Meta_Grind_AC_isCommutative(v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_842_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_842_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_842_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_842_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; uint8_t v___x_838_; 
v___x_838_ = lean_unbox(v_a_801_);
lean_dec(v_a_801_);
if (v___x_838_ == 0)
{
v___y_806_ = v_a_750_;
v___y_807_ = v_a_751_;
v___y_808_ = v_a_752_;
v___y_809_ = v_a_753_;
v___y_810_ = v_a_754_;
v___y_811_ = v_a_755_;
v___y_812_ = v_a_756_;
v___y_813_ = v_a_757_;
v___y_814_ = v_a_758_;
v___y_815_ = v_a_759_;
v___y_816_ = v_a_760_;
goto v___jp_805_;
}
else
{
uint8_t v___x_839_; 
v___x_839_ = l_Lean_Grind_AC_Seq_isSorted(v_s_748_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_del_object(v___x_803_);
v___x_840_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7);
v___x_841_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_840_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
return v___x_841_;
}
else
{
v___y_806_ = v_a_750_;
v___y_807_ = v_a_751_;
v___y_808_ = v_a_752_;
v___y_809_ = v_a_753_;
v___y_810_ = v_a_754_;
v___y_811_ = v_a_755_;
v___y_812_ = v_a_756_;
v___y_813_ = v_a_757_;
v___y_814_ = v_a_758_;
v___y_815_ = v_a_759_;
v___y_816_ = v_a_760_;
goto v___jp_805_;
}
}
v___jp_805_:
{
if (v_simplified_749_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = lean_box(0);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_817_);
v___x_819_ = v___x_803_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
lean_object* v___x_821_; 
lean_del_object(v___x_803_);
v___x_821_ = l_Lean_Meta_Grind_AC_hasNeutral(v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; uint8_t v___x_823_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
v___x_823_ = lean_unbox(v_a_822_);
lean_dec(v_a_822_);
if (v___x_823_ == 0)
{
v___y_763_ = v___y_806_;
v___y_764_ = v___y_807_;
v___y_765_ = v___y_808_;
v___y_766_ = v___y_809_;
v___y_767_ = v___y_810_;
v___y_768_ = v___y_811_;
v___y_769_ = v___y_812_;
v___y_770_ = v___y_813_;
v___y_771_ = v___y_814_;
v___y_772_ = v___y_815_;
v___y_773_ = v___y_816_;
goto v___jp_762_;
}
else
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = l_Lean_Grind_AC_Seq_contains(v_s_748_, v___x_824_);
if (v___x_825_ == 0)
{
v___y_763_ = v___y_806_;
v___y_764_ = v___y_807_;
v___y_765_ = v___y_808_;
v___y_766_ = v___y_809_;
v___y_767_ = v___y_810_;
v___y_768_ = v___y_811_;
v___y_769_ = v___y_812_;
v___y_770_ = v___y_813_;
v___y_771_ = v___y_814_;
v___y_772_ = v___y_815_;
v___y_773_ = v___y_816_;
goto v___jp_762_;
}
else
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3));
v___x_827_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_748_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5);
v___x_829_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_828_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
return v___x_829_;
}
else
{
v___y_763_ = v___y_806_;
v___y_764_ = v___y_807_;
v___y_765_ = v___y_808_;
v___y_766_ = v___y_809_;
v___y_767_ = v___y_810_;
v___y_768_ = v___y_811_;
v___y_769_ = v___y_812_;
v___y_770_ = v___y_813_;
v___y_771_ = v___y_814_;
v___y_772_ = v___y_815_;
v___y_773_ = v___y_816_;
goto v___jp_762_;
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_a_830_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_821_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_821_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v_a_843_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_800_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_800_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
v___jp_762_:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Meta_Grind_AC_isIdempotent(v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_791_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_791_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_791_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_791_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
uint8_t v___x_779_; 
v___x_779_ = lean_unbox(v_a_775_);
lean_dec(v_a_775_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_box(0);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_780_);
v___x_782_ = v___x_777_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
else
{
uint8_t v___x_784_; 
v___x_784_ = l_Lean_Grind_AC_Seq_noAdjacentDuplicates(v_s_748_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; 
lean_del_object(v___x_777_);
v___x_785_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2);
v___x_786_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_785_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
return v___x_786_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_box(0);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_787_);
v___x_789_ = v___x_777_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
v_a_792_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_774_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_774_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___boxed(lean_object* v_s_851_, lean_object* v_simplified_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
uint8_t v_simplified_boxed_865_; lean_object* v_res_866_; 
v_simplified_boxed_865_ = lean_unbox(v_simplified_852_);
v_res_866_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(v_s_851_, v_simplified_boxed_865_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_s_851_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(lean_object* v_lhs_867_, lean_object* v_rhs_868_, uint8_t v_simplified_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(v_lhs_867_, v_simplified_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_883_; 
lean_dec_ref_known(v___x_882_, 1);
v___x_883_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(v_rhs_868_, v_simplified_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
return v___x_883_;
}
else
{
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs___boxed(lean_object* v_lhs_884_, lean_object* v_rhs_885_, lean_object* v_simplified_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
uint8_t v_simplified_boxed_899_; lean_object* v_res_900_; 
v_simplified_boxed_899_ = lean_unbox(v_simplified_886_);
v_res_900_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_884_, v_rhs_885_, v_simplified_boxed_899_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_rhs_885_);
lean_dec_ref(v_lhs_884_);
return v_res_900_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0(void){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(lean_object* v_msg_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; lean_object* v___f_916_; lean_object* v___x_3765__overap_917_; lean_object* v___x_918_; 
v___x_915_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0);
v___f_916_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_916_, 0, v___x_915_);
v___x_3765__overap_917_ = lean_panic_fn_borrowed(v___f_916_, v_msg_902_);
lean_dec_ref(v___f_916_);
lean_inc(v___y_913_);
lean_inc_ref(v___y_912_);
lean_inc(v___y_911_);
lean_inc_ref(v___y_910_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc(v___y_904_);
lean_inc(v___y_903_);
v___x_918_ = lean_apply_12(v___x_3765__overap_917_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, lean_box(0));
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___boxed(lean_object* v_msg_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(v_msg_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec(v___y_921_);
lean_dec(v___y_920_);
return v_res_932_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_935_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1));
v___x_936_ = lean_unsigned_to_nat(4u);
v___x_937_ = lean_unsigned_to_nat(43u);
v___x_938_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0));
v___x_939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_940_ = l_mkPanicMessageWithDecl(v___x_939_, v___x_938_, v___x_937_, v___x_936_, v___x_935_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(lean_object* v_as_x27_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
if (lean_obj_tag(v_as_x27_941_) == 0)
{
lean_object* v___x_955_; 
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v_b_942_);
return v___x_955_;
}
else
{
lean_object* v_head_956_; lean_object* v_tail_957_; lean_object* v_lhs_958_; lean_object* v_rhs_959_; uint8_t v___x_960_; uint8_t v___x_961_; uint8_t v___x_962_; 
v_head_956_ = lean_ctor_get(v_as_x27_941_, 0);
v_tail_957_ = lean_ctor_get(v_as_x27_941_, 1);
v_lhs_958_ = lean_ctor_get(v_head_956_, 0);
v_rhs_959_ = lean_ctor_get(v_head_956_, 1);
v___x_960_ = l_Lean_Grind_AC_Seq_compare(v_lhs_958_, v_rhs_959_);
v___x_961_ = 2;
v___x_962_ = l_instDecidableEqOrdering(v___x_960_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2);
v___x_964_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(v___x_963_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_975_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_975_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_975_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_975_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
if (lean_obj_tag(v_a_965_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; 
v_a_969_ = lean_ctor_get(v_a_965_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v_a_965_, 1);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v_a_969_);
v___x_971_ = v___x_967_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
else
{
lean_object* v_a_973_; 
lean_del_object(v___x_967_);
v_a_973_ = lean_ctor_get(v_a_965_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v_a_965_, 1);
v_as_x27_941_ = v_tail_957_;
v_b_942_ = v_a_973_;
goto _start;
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
v_a_976_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_964_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_964_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v___x_984_; 
v___x_984_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_958_, v_rhs_959_, v___x_962_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v___x_985_; 
lean_dec_ref_known(v___x_984_, 1);
v___x_985_ = lean_box(0);
v_as_x27_941_ = v_tail_957_;
v_b_942_ = v___x_985_;
goto _start;
}
else
{
return v___x_984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___boxed(lean_object* v_as_x27_987_, lean_object* v_b_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_as_x27_987_, v_b_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec(v___y_990_);
lean_dec(v___y_989_);
lean_dec(v_as_x27_987_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v_basis_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v_basis_1016_ = lean_ctor_get(v_a_1015_, 15);
lean_inc(v_basis_1016_);
lean_dec(v_a_1015_);
v___x_1017_ = lean_box(0);
v___x_1018_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_basis_1016_, v___x_1017_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_basis_1016_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v___x_1018_, 0);
lean_dec(v_unused_1026_);
v___x_1020_ = v___x_1018_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_dec(v___x_1018_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1017_);
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1017_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
else
{
return v___x_1018_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v_a_1027_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1014_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1014_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis___boxed(lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec(v_a_1035_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1(lean_object* v_as_1048_, lean_object* v_as_x27_1049_, lean_object* v_b_1050_, lean_object* v_a_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_as_x27_1049_, v_b_1050_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___boxed(lean_object* v_as_1065_, lean_object* v_as_x27_1066_, lean_object* v_b_1067_, lean_object* v_a_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1(v_as_1065_, v_as_x27_1066_, v_b_1067_, v_a_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec(v_as_x27_1066_);
lean_dec(v_as_1065_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(lean_object* v_init_1082_, lean_object* v_x_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
if (lean_obj_tag(v_x_1083_) == 0)
{
lean_object* v_k_1096_; lean_object* v_l_1097_; lean_object* v_r_1098_; lean_object* v___x_1099_; 
v_k_1096_ = lean_ctor_get(v_x_1083_, 1);
v_l_1097_ = lean_ctor_get(v_x_1083_, 3);
v_r_1098_ = lean_ctor_get(v_x_1083_, 4);
v___x_1099_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v_init_1082_, v_l_1097_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_lhs_1100_; lean_object* v_rhs_1101_; uint8_t v___x_1102_; lean_object* v___x_1103_; 
lean_dec_ref_known(v___x_1099_, 1);
v_lhs_1100_ = lean_ctor_get(v_k_1096_, 0);
v_rhs_1101_ = lean_ctor_get(v_k_1096_, 1);
v___x_1102_ = 0;
v___x_1103_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1100_, v_rhs_1101_, v___x_1102_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v___x_1104_; 
lean_dec_ref_known(v___x_1103_, 1);
v___x_1104_ = lean_box(0);
v_init_1082_ = v___x_1104_;
v_x_1083_ = v_r_1098_;
goto _start;
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_a_1106_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1103_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1103_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
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
else
{
return v___x_1099_;
}
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_init_1082_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0___boxed(lean_object* v_init_1116_, lean_object* v_x_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v_init_1116_, v_x_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec(v_x_1117_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v_queue_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v_queue_1145_ = lean_ctor_get(v_a_1144_, 14);
lean_inc(v_queue_1145_);
lean_dec(v_a_1144_);
v___x_1146_ = lean_box(0);
v___x_1147_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v___x_1146_, v_queue_1145_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
lean_dec(v_queue_1145_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v___x_1147_, 0);
lean_dec(v_unused_1155_);
v___x_1149_ = v___x_1147_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_dec(v___x_1147_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1146_);
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1146_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
v_a_1156_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1147_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1147_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
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
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
v_a_1164_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1143_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1143_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue___boxed(lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec(v_a_1172_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(lean_object* v_as_1188_, size_t v_sz_1189_, size_t v_i_1190_, lean_object* v_b_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_usize_dec_lt(v_i_1190_, v_sz_1189_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_b_1191_);
return v___x_1205_;
}
else
{
lean_object* v_a_1206_; lean_object* v_lhs_1207_; lean_object* v_rhs_1208_; lean_object* v___x_1209_; 
lean_dec_ref(v_b_1191_);
v_a_1206_ = lean_array_uget_borrowed(v_as_1188_, v_i_1190_);
v_lhs_1207_ = lean_ctor_get(v_a_1206_, 0);
v_rhs_1208_ = lean_ctor_get(v_a_1206_, 1);
v___x_1209_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1207_, v_rhs_1208_, v___x_1204_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; 
lean_dec_ref_known(v___x_1209_, 1);
v___x_1210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0));
v___x_1211_ = ((size_t)1ULL);
v___x_1212_ = lean_usize_add(v_i_1190_, v___x_1211_);
v_i_1190_ = v___x_1212_;
v_b_1191_ = v___x_1210_;
goto _start;
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v_a_1214_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1209_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1209_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1222_, lean_object* v_sz_1223_, lean_object* v_i_1224_, lean_object* v_b_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
size_t v_sz_boxed_1238_; size_t v_i_boxed_1239_; lean_object* v_res_1240_; 
v_sz_boxed_1238_ = lean_unbox_usize(v_sz_1223_);
lean_dec(v_sz_1223_);
v_i_boxed_1239_ = lean_unbox_usize(v_i_1224_);
lean_dec(v_i_1224_);
v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(v_as_1222_, v_sz_boxed_1238_, v_i_boxed_1239_, v_b_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v_as_1222_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(lean_object* v_as_1241_, size_t v_sz_1242_, size_t v_i_1243_, lean_object* v_b_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
uint8_t v___x_1257_; 
v___x_1257_ = lean_usize_dec_lt(v_i_1243_, v_sz_1242_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_b_1244_);
return v___x_1258_;
}
else
{
lean_object* v_a_1259_; lean_object* v_lhs_1260_; lean_object* v_rhs_1261_; lean_object* v___x_1262_; 
lean_dec_ref(v_b_1244_);
v_a_1259_ = lean_array_uget_borrowed(v_as_1241_, v_i_1243_);
v_lhs_1260_ = lean_ctor_get(v_a_1259_, 0);
v_rhs_1261_ = lean_ctor_get(v_a_1259_, 1);
v___x_1262_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1260_, v_rhs_1261_, v___x_1257_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
lean_dec_ref_known(v___x_1262_, 1);
v___x_1263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0));
v___x_1264_ = ((size_t)1ULL);
v___x_1265_ = lean_usize_add(v_i_1243_, v___x_1264_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(v_as_1241_, v_sz_1242_, v___x_1265_, v___x_1263_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
return v___x_1266_;
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_a_1267_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1262_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1262_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1___boxed(lean_object* v_as_1275_, lean_object* v_sz_1276_, lean_object* v_i_1277_, lean_object* v_b_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
size_t v_sz_boxed_1291_; size_t v_i_boxed_1292_; lean_object* v_res_1293_; 
v_sz_boxed_1291_ = lean_unbox_usize(v_sz_1276_);
lean_dec(v_sz_1276_);
v_i_boxed_1292_ = lean_unbox_usize(v_i_1277_);
lean_dec(v_i_1277_);
v_res_1293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(v_as_1275_, v_sz_boxed_1291_, v_i_boxed_1292_, v_b_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v_as_1275_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_1297_, size_t v_sz_1298_, size_t v_i_1299_, lean_object* v_b_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
uint8_t v___x_1313_; 
v___x_1313_ = lean_usize_dec_lt(v_i_1299_, v_sz_1298_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_b_1300_);
return v___x_1314_;
}
else
{
lean_object* v_a_1315_; lean_object* v_lhs_1316_; lean_object* v_rhs_1317_; lean_object* v___x_1318_; 
lean_dec_ref(v_b_1300_);
v_a_1315_ = lean_array_uget_borrowed(v_as_1297_, v_i_1299_);
v_lhs_1316_ = lean_ctor_get(v_a_1315_, 0);
v_rhs_1317_ = lean_ctor_get(v_a_1315_, 1);
v___x_1318_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1316_, v_rhs_1317_, v___x_1313_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; 
lean_dec_ref_known(v___x_1318_, 1);
v___x_1319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = lean_usize_add(v_i_1299_, v___x_1320_);
v_i_1299_ = v___x_1321_;
v_b_1300_ = v___x_1319_;
goto _start;
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
v_a_1323_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1318_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1318_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_1331_, lean_object* v_sz_1332_, lean_object* v_i_1333_, lean_object* v_b_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
size_t v_sz_boxed_1347_; size_t v_i_boxed_1348_; lean_object* v_res_1349_; 
v_sz_boxed_1347_ = lean_unbox_usize(v_sz_1332_);
lean_dec(v_sz_1332_);
v_i_boxed_1348_ = lean_unbox_usize(v_i_1333_);
lean_dec(v_i_1333_);
v_res_1349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_1331_, v_sz_boxed_1347_, v_i_boxed_1348_, v_b_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v_as_1331_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(lean_object* v_as_1350_, size_t v_sz_1351_, size_t v_i_1352_, lean_object* v_b_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_usize_dec_lt(v_i_1352_, v_sz_1351_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_b_1353_);
return v___x_1367_;
}
else
{
lean_object* v_a_1368_; lean_object* v_lhs_1369_; lean_object* v_rhs_1370_; lean_object* v___x_1371_; 
lean_dec_ref(v_b_1353_);
v_a_1368_ = lean_array_uget_borrowed(v_as_1350_, v_i_1352_);
v_lhs_1369_ = lean_ctor_get(v_a_1368_, 0);
v_rhs_1370_ = lean_ctor_get(v_a_1368_, 1);
v___x_1371_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1369_, v_rhs_1370_, v___x_1366_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; lean_object* v___x_1375_; 
lean_dec_ref_known(v___x_1371_, 1);
v___x_1372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_1373_ = ((size_t)1ULL);
v___x_1374_ = lean_usize_add(v_i_1352_, v___x_1373_);
v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_1350_, v_sz_1351_, v___x_1374_, v___x_1372_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
return v___x_1375_;
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
v_a_1376_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1371_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1371_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1384_, lean_object* v_sz_1385_, lean_object* v_i_1386_, lean_object* v_b_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
size_t v_sz_boxed_1400_; size_t v_i_boxed_1401_; lean_object* v_res_1402_; 
v_sz_boxed_1400_ = lean_unbox_usize(v_sz_1385_);
lean_dec(v_sz_1385_);
v_i_boxed_1401_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(v_as_1384_, v_sz_boxed_1400_, v_i_boxed_1401_, v_b_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v_as_1384_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(lean_object* v_init_1403_, lean_object* v_n_1404_, lean_object* v_b_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
if (lean_obj_tag(v_n_1404_) == 0)
{
lean_object* v_cs_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; size_t v_sz_1421_; size_t v___x_1422_; lean_object* v___x_1423_; 
v_cs_1418_ = lean_ctor_get(v_n_1404_, 0);
v___x_1419_ = lean_box(0);
v___x_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
lean_ctor_set(v___x_1420_, 1, v_b_1405_);
v_sz_1421_ = lean_array_size(v_cs_1418_);
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(v_init_1403_, v_cs_1418_, v_sz_1421_, v___x_1422_, v___x_1420_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1438_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1438_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1438_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v_fst_1428_; 
v_fst_1428_ = lean_ctor_get(v_a_1424_, 0);
if (lean_obj_tag(v_fst_1428_) == 0)
{
lean_object* v_snd_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v_snd_1429_ = lean_ctor_get(v_a_1424_, 1);
lean_inc(v_snd_1429_);
lean_dec(v_a_1424_);
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_snd_1429_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1430_);
v___x_1432_ = v___x_1426_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
else
{
lean_object* v_val_1434_; lean_object* v___x_1436_; 
lean_inc_ref(v_fst_1428_);
lean_dec(v_a_1424_);
v_val_1434_ = lean_ctor_get(v_fst_1428_, 0);
lean_inc(v_val_1434_);
lean_dec_ref_known(v_fst_1428_, 1);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v_val_1434_);
v___x_1436_ = v___x_1426_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_val_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1423_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1423_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
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
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_vs_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; size_t v_sz_1450_; size_t v___x_1451_; lean_object* v___x_1452_; 
v_vs_1447_ = lean_ctor_get(v_n_1404_, 0);
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
lean_ctor_set(v___x_1449_, 1, v_b_1405_);
v_sz_1450_ = lean_array_size(v_vs_1447_);
v___x_1451_ = ((size_t)0ULL);
v___x_1452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(v_vs_1447_, v_sz_1450_, v___x_1451_, v___x_1449_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1467_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1467_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1467_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v_fst_1457_; 
v_fst_1457_ = lean_ctor_get(v_a_1453_, 0);
if (lean_obj_tag(v_fst_1457_) == 0)
{
lean_object* v_snd_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v_snd_1458_ = lean_ctor_get(v_a_1453_, 1);
lean_inc(v_snd_1458_);
lean_dec(v_a_1453_);
v___x_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1459_, 0, v_snd_1458_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1459_);
v___x_1461_ = v___x_1455_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
else
{
lean_object* v_val_1463_; lean_object* v___x_1465_; 
lean_inc_ref(v_fst_1457_);
lean_dec(v_a_1453_);
v_val_1463_ = lean_ctor_get(v_fst_1457_, 0);
lean_inc(v_val_1463_);
lean_dec_ref_known(v_fst_1457_, 1);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v_val_1463_);
v___x_1465_ = v___x_1455_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_val_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
v_a_1468_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1452_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1452_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_1476_, lean_object* v_as_1477_, size_t v_sz_1478_, size_t v_i_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
uint8_t v___x_1493_; 
v___x_1493_ = lean_usize_dec_lt(v_i_1479_, v_sz_1478_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_b_1480_);
return v___x_1494_;
}
else
{
lean_object* v_snd_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1529_; 
v_snd_1495_ = lean_ctor_get(v_b_1480_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_b_1480_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v_b_1480_, 0);
lean_dec(v_unused_1530_);
v___x_1497_ = v_b_1480_;
v_isShared_1498_ = v_isSharedCheck_1529_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_snd_1495_);
lean_dec(v_b_1480_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1529_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_a_1499_; lean_object* v___x_1500_; 
v_a_1499_ = lean_array_uget_borrowed(v_as_1477_, v_i_1479_);
lean_inc(v_snd_1495_);
v___x_1500_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_1476_, v_a_1499_, v_snd_1495_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1520_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1520_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1520_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
if (lean_obj_tag(v_a_1501_) == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_a_1501_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1505_);
v___x_1507_ = v___x_1497_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_snd_1495_);
v___x_1507_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v___x_1507_);
v___x_1509_ = v___x_1503_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
lean_del_object(v___x_1503_);
lean_dec(v_snd_1495_);
v_a_1512_ = lean_ctor_get(v_a_1501_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v_a_1501_, 1);
v___x_1513_ = lean_box(0);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 1, v_a_1512_);
lean_ctor_set(v___x_1497_, 0, v___x_1513_);
v___x_1515_ = v___x_1497_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_a_1512_);
v___x_1515_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
size_t v___x_1516_; size_t v___x_1517_; 
v___x_1516_ = ((size_t)1ULL);
v___x_1517_ = lean_usize_add(v_i_1479_, v___x_1516_);
v_i_1479_ = v___x_1517_;
v_b_1480_ = v___x_1515_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_del_object(v___x_1497_);
lean_dec(v_snd_1495_);
v_a_1521_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1500_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1500_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1531_ = _args[0];
lean_object* v_as_1532_ = _args[1];
lean_object* v_sz_1533_ = _args[2];
lean_object* v_i_1534_ = _args[3];
lean_object* v_b_1535_ = _args[4];
lean_object* v___y_1536_ = _args[5];
lean_object* v___y_1537_ = _args[6];
lean_object* v___y_1538_ = _args[7];
lean_object* v___y_1539_ = _args[8];
lean_object* v___y_1540_ = _args[9];
lean_object* v___y_1541_ = _args[10];
lean_object* v___y_1542_ = _args[11];
lean_object* v___y_1543_ = _args[12];
lean_object* v___y_1544_ = _args[13];
lean_object* v___y_1545_ = _args[14];
lean_object* v___y_1546_ = _args[15];
lean_object* v___y_1547_ = _args[16];
_start:
{
size_t v_sz_boxed_1548_; size_t v_i_boxed_1549_; lean_object* v_res_1550_; 
v_sz_boxed_1548_ = lean_unbox_usize(v_sz_1533_);
lean_dec(v_sz_1533_);
v_i_boxed_1549_ = lean_unbox_usize(v_i_1534_);
lean_dec(v_i_1534_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(v_init_1531_, v_as_1532_, v_sz_boxed_1548_, v_i_boxed_1549_, v_b_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v_as_1532_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0___boxed(lean_object* v_init_1551_, lean_object* v_n_1552_, lean_object* v_b_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_1551_, v_n_1552_, v_b_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v_n_1552_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(lean_object* v_t_1567_, lean_object* v_init_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_root_1581_; lean_object* v_tail_1582_; lean_object* v___x_1583_; 
v_root_1581_ = lean_ctor_get(v_t_1567_, 0);
v_tail_1582_ = lean_ctor_get(v_t_1567_, 1);
v___x_1583_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_1568_, v_root_1581_, v_init_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1620_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1620_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1620_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
if (lean_obj_tag(v_a_1584_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; 
v_a_1588_ = lean_ctor_get(v_a_1584_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v_a_1584_, 1);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v_a_1588_);
v___x_1590_ = v___x_1586_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; size_t v_sz_1595_; size_t v___x_1596_; lean_object* v___x_1597_; 
lean_del_object(v___x_1586_);
v_a_1592_ = lean_ctor_get(v_a_1584_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v_a_1584_, 1);
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v_a_1592_);
v_sz_1595_ = lean_array_size(v_tail_1582_);
v___x_1596_ = ((size_t)0ULL);
v___x_1597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(v_tail_1582_, v_sz_1595_, v___x_1596_, v___x_1594_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1611_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1611_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1611_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v_fst_1602_; 
v_fst_1602_ = lean_ctor_get(v_a_1598_, 0);
if (lean_obj_tag(v_fst_1602_) == 0)
{
lean_object* v_snd_1603_; lean_object* v___x_1605_; 
v_snd_1603_ = lean_ctor_get(v_a_1598_, 1);
lean_inc(v_snd_1603_);
lean_dec(v_a_1598_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_snd_1603_);
v___x_1605_ = v___x_1600_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_snd_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
else
{
lean_object* v_val_1607_; lean_object* v___x_1609_; 
lean_inc_ref(v_fst_1602_);
lean_dec(v_a_1598_);
v_val_1607_ = lean_ctor_get(v_fst_1602_, 0);
lean_inc(v_val_1607_);
lean_dec_ref_known(v_fst_1602_, 1);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_val_1607_);
v___x_1609_ = v___x_1600_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_val_1607_);
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
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1597_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1597_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
v_a_1621_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1583_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1583_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0___boxed(lean_object* v_t_1629_, lean_object* v_init_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(v_t_1629_, v_init_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v_t_1629_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v_diseqs_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v_diseqs_1658_ = lean_ctor_get(v_a_1657_, 16);
lean_inc_ref(v_diseqs_1658_);
lean_dec(v_a_1657_);
v___x_1659_ = lean_box(0);
v___x_1660_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(v_diseqs_1658_, v___x_1659_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
lean_dec_ref(v_diseqs_1658_);
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
v_a_1669_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1656_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1656_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs___boxed(lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
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
lean_dec(v_a_1677_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v___x_1703_; 
lean_dec_ref_known(v___x_1702_, 1);
v___x_1703_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v___x_1704_; 
lean_dec_ref_known(v___x_1703_, 1);
v___x_1704_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v___x_1705_; 
lean_dec_ref_known(v___x_1704_, 1);
v___x_1705_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_1705_;
}
else
{
return v___x_1704_;
}
}
else
{
return v___x_1703_;
}
}
else
{
return v___x_1702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs___boxed(lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec(v_a_1706_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(lean_object* v_upperBound_1719_, lean_object* v_a_1720_, lean_object* v_b_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_nat_dec_lt(v_a_1720_, v_upperBound_1719_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_dec(v_a_1720_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_b_1721_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(v_a_1720_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec_ref_known(v___x_1735_, 1);
v___x_1736_ = lean_box(0);
v___x_1737_ = lean_unsigned_to_nat(1u);
v___x_1738_ = lean_nat_add(v_a_1720_, v___x_1737_);
lean_dec(v_a_1720_);
v_a_1720_ = v___x_1738_;
v_b_1721_ = v___x_1736_;
goto _start;
}
else
{
lean_dec(v_a_1720_);
return v___x_1735_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg___boxed(lean_object* v_upperBound_1740_, lean_object* v_a_1741_, lean_object* v_b_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(v_upperBound_1740_, v_a_1741_, v_b_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec(v_upperBound_1740_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkInvariants(lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
uint8_t v_debug_1766_; 
v_debug_1766_ = lean_ctor_get_uint8(v_a_1757_, sizeof(void*)*8 + 2);
if (v_debug_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_box(0);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
else
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_1755_, v_a_1763_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v_structs_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v_structs_1771_ = lean_ctor_get(v_a_1770_, 0);
lean_inc_ref(v_structs_1771_);
lean_dec(v_a_1770_);
v___x_1772_ = lean_array_get_size(v_structs_1771_);
lean_dec_ref(v_structs_1771_);
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = lean_box(0);
v___x_1775_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(v___x_1772_, v___x_1773_, v___x_1774_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1782_ == 0)
{
lean_object* v_unused_1783_; 
v_unused_1783_ = lean_ctor_get(v___x_1775_, 0);
lean_dec(v_unused_1783_);
v___x_1777_ = v___x_1775_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_dec(v___x_1775_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1774_);
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1774_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
else
{
return v___x_1775_;
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1769_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1769_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkInvariants___boxed(lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_Meta_Grind_AC_checkInvariants(v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec(v_a_1792_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0(lean_object* v_upperBound_1804_, lean_object* v_inst_1805_, lean_object* v_R_1806_, lean_object* v_a_1807_, lean_object* v_b_1808_, lean_object* v_c_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(v_upperBound_1804_, v_a_1807_, v_b_1808_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1822_ = _args[0];
lean_object* v_inst_1823_ = _args[1];
lean_object* v_R_1824_ = _args[2];
lean_object* v_a_1825_ = _args[3];
lean_object* v_b_1826_ = _args[4];
lean_object* v_c_1827_ = _args[5];
lean_object* v___y_1828_ = _args[6];
lean_object* v___y_1829_ = _args[7];
lean_object* v___y_1830_ = _args[8];
lean_object* v___y_1831_ = _args[9];
lean_object* v___y_1832_ = _args[10];
lean_object* v___y_1833_ = _args[11];
lean_object* v___y_1834_ = _args[12];
lean_object* v___y_1835_ = _args[13];
lean_object* v___y_1836_ = _args[14];
lean_object* v___y_1837_ = _args[15];
lean_object* v___y_1838_ = _args[16];
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0(v_upperBound_1822_, v_inst_1823_, v_R_1824_, v_a_1825_, v_b_1826_, v_c_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec(v_upperBound_1822_);
return v_res_1839_;
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
