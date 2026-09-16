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
lean_object* l_Ordering_ctorIdx(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object**);
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
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Tactic.Grind.AC.Inv.0.Lean.Meta.Grind.AC.checkBasis"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: compare c.lhs c.rhs == .gt\n    "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__3;
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
lean_object* v___x_15_; lean_object* v___f_16_; lean_object* v___x_4704__overap_17_; lean_object* v___x_18_; 
v___x_15_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0___closed__0);
v___f_16_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_16_, 0, v___x_15_);
v___x_4704__overap_17_ = lean_panic_fn_borrowed(v___f_16_, v_msg_2_);
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
v___x_18_ = lean_apply_12(v___x_4704__overap_17_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, lean_box(0));
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
lean_object* v___x_47_; lean_object* v___f_48_; lean_object* v___x_4722__overap_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1___closed__0);
v___f_48_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_48_, 0, v___x_47_);
v___x_4722__overap_49_ = lean_panic_fn_borrowed(v___f_48_, v_msg_34_);
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
v___x_50_ = lean_apply_12(v___x_4722__overap_49_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0(lean_object* v_vars_81_, lean_object* v___x_82_, lean_object* v_x_83_, lean_object* v_____s_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_fst_102_; lean_object* v_snd_103_; lean_object* v_size_104_; uint8_t v___x_105_; 
v_fst_102_ = lean_ctor_get(v_x_83_, 0);
v_snd_103_ = lean_ctor_get(v_x_83_, 1);
v_size_104_ = lean_ctor_get(v_vars_81_, 2);
v___x_105_ = lean_nat_dec_lt(v_snd_103_, v_size_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__3);
v___x_107_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_106_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_dec_ref_known(v___x_107_, 1);
goto v___jp_97_;
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
else
{
lean_object* v___x_116_; size_t v___x_117_; size_t v___x_118_; uint8_t v___x_119_; 
v___x_116_ = l_Lean_PersistentArray_get_x21___redArg(v___x_82_, v_vars_81_, v_snd_103_);
v___x_117_ = lean_ptr_addr(v_fst_102_);
v___x_118_ = lean_ptr_addr(v___x_116_);
lean_dec(v___x_116_);
v___x_119_ = lean_usize_dec_eq(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__5);
v___x_121_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__1(v___x_120_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
return v___x_121_;
}
else
{
goto v___jp_97_;
}
}
v___jp_97_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = lean_nat_add(v_____s_84_, v___x_98_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___boxed(lean_object* v_vars_122_, lean_object* v___x_123_, lean_object* v_x_124_, lean_object* v_____s_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0(v_vars_122_, v___x_123_, v_x_124_, v_____s_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec(v___y_127_);
lean_dec(v___y_126_);
lean_dec(v_____s_125_);
lean_dec_ref(v_x_124_);
lean_dec_ref(v___x_123_);
lean_dec_ref(v_vars_122_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0(lean_object* v_f_139_, lean_object* v_s_140_, lean_object* v_a_141_, lean_object* v_b_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_a_141_);
lean_ctor_set(v___x_155_, 1, v_b_142_);
lean_inc(v___y_153_);
lean_inc_ref(v___y_152_);
lean_inc(v___y_151_);
lean_inc_ref(v___y_150_);
lean_inc(v___y_149_);
lean_inc_ref(v___y_148_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc(v___y_144_);
lean_inc(v___y_143_);
v___x_156_ = lean_apply_14(v_f_139_, v___x_155_, v_s_140_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, lean_box(0));
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_183_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_183_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_183_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_183_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
if (lean_obj_tag(v_a_157_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_171_; 
v_a_161_ = lean_ctor_get(v_a_157_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v_a_157_);
if (v_isSharedCheck_171_ == 0)
{
v___x_163_ = v_a_157_;
v_isShared_164_ = v_isSharedCheck_171_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v_a_157_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_171_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_170_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_166_);
v___x_168_ = v___x_159_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_182_; 
v_a_172_ = lean_ctor_get(v_a_157_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v_a_157_);
if (v_isSharedCheck_182_ == 0)
{
v___x_174_ = v_a_157_;
v_isShared_175_ = v_isSharedCheck_182_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v_a_157_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_182_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_181_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_179_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_177_);
v___x_179_ = v___x_159_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
v_a_184_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_156_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_156_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0___boxed(lean_object* v_f_192_, lean_object* v_s_193_, lean_object* v_a_194_, lean_object* v_b_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0(v_f_192_, v_s_193_, v_a_194_, v_b_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec(v___y_197_);
lean_dec(v___y_196_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(lean_object* v_f_209_, lean_object* v_keys_210_, lean_object* v_vals_211_, lean_object* v_i_212_, lean_object* v_acc_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = lean_array_get_size(v_keys_210_);
v___x_227_ = lean_nat_dec_lt(v_i_212_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v_i_212_);
lean_dec_ref(v_f_209_);
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v_acc_213_);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
else
{
lean_object* v_k_230_; lean_object* v_v_231_; lean_object* v___x_232_; 
v_k_230_ = lean_array_fget_borrowed(v_keys_210_, v_i_212_);
v_v_231_ = lean_array_fget_borrowed(v_vals_211_, v_i_212_);
lean_inc_ref(v_f_209_);
lean_inc(v___y_224_);
lean_inc_ref(v___y_223_);
lean_inc(v___y_222_);
lean_inc_ref(v___y_221_);
lean_inc(v___y_220_);
lean_inc_ref(v___y_219_);
lean_inc(v___y_218_);
lean_inc_ref(v___y_217_);
lean_inc(v___y_216_);
lean_inc(v___y_215_);
lean_inc(v___y_214_);
lean_inc(v_v_231_);
lean_inc(v_k_230_);
v___x_232_ = lean_apply_15(v_f_209_, v_acc_213_, v_k_230_, v_v_231_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, lean_box(0));
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
if (lean_obj_tag(v_a_233_) == 0)
{
lean_dec_ref_known(v_a_233_, 1);
lean_dec(v_i_212_);
lean_dec_ref(v_f_209_);
return v___x_232_;
}
else
{
lean_object* v_a_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec_ref_known(v___x_232_, 1);
v_a_234_ = lean_ctor_get(v_a_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v_a_233_, 1);
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_nat_add(v_i_212_, v___x_235_);
lean_dec(v_i_212_);
v_i_212_ = v___x_236_;
v_acc_213_ = v_a_234_;
goto _start;
}
}
else
{
lean_dec(v_i_212_);
lean_dec_ref(v_f_209_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_f_238_ = _args[0];
lean_object* v_keys_239_ = _args[1];
lean_object* v_vals_240_ = _args[2];
lean_object* v_i_241_ = _args[3];
lean_object* v_acc_242_ = _args[4];
lean_object* v___y_243_ = _args[5];
lean_object* v___y_244_ = _args[6];
lean_object* v___y_245_ = _args[7];
lean_object* v___y_246_ = _args[8];
lean_object* v___y_247_ = _args[9];
lean_object* v___y_248_ = _args[10];
lean_object* v___y_249_ = _args[11];
lean_object* v___y_250_ = _args[12];
lean_object* v___y_251_ = _args[13];
lean_object* v___y_252_ = _args[14];
lean_object* v___y_253_ = _args[15];
lean_object* v___y_254_ = _args[16];
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_238_, v_keys_239_, v_vals_240_, v_i_241_, v_acc_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v_vals_240_);
lean_dec_ref(v_keys_239_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_f_256_, lean_object* v_as_257_, size_t v_i_258_, size_t v_stop_259_, lean_object* v_b_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_a_274_; lean_object* v___y_279_; uint8_t v___x_282_; 
v___x_282_ = lean_usize_dec_eq(v_i_258_, v_stop_259_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_array_uget_borrowed(v_as_257_, v_i_258_);
switch(lean_obj_tag(v___x_283_))
{
case 0:
{
lean_object* v_key_284_; lean_object* v_val_285_; lean_object* v___x_286_; 
v_key_284_ = lean_ctor_get(v___x_283_, 0);
v_val_285_ = lean_ctor_get(v___x_283_, 1);
lean_inc_ref(v_f_256_);
lean_inc(v___y_271_);
lean_inc_ref(v___y_270_);
lean_inc(v___y_269_);
lean_inc_ref(v___y_268_);
lean_inc(v___y_267_);
lean_inc_ref(v___y_266_);
lean_inc(v___y_265_);
lean_inc_ref(v___y_264_);
lean_inc(v___y_263_);
lean_inc(v___y_262_);
lean_inc(v___y_261_);
lean_inc(v_val_285_);
lean_inc(v_key_284_);
v___x_286_ = lean_apply_15(v_f_256_, v_b_260_, v_key_284_, v_val_285_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, lean_box(0));
v___y_279_ = v___x_286_;
goto v___jp_278_;
}
case 1:
{
lean_object* v_node_287_; lean_object* v___x_288_; 
v_node_287_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_node_287_);
lean_inc_ref(v_f_256_);
v___x_288_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_256_, v_node_287_, v_b_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
v___y_279_ = v___x_288_;
goto v___jp_278_;
}
default: 
{
v_a_274_ = v_b_260_;
goto v___jp_273_;
}
}
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec_ref(v_f_256_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_b_260_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
v___jp_273_:
{
size_t v___x_275_; size_t v___x_276_; 
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_add(v_i_258_, v___x_275_);
v_i_258_ = v___x_276_;
v_b_260_ = v_a_274_;
goto _start;
}
v___jp_278_:
{
if (lean_obj_tag(v___y_279_) == 0)
{
lean_object* v_a_280_; 
v_a_280_ = lean_ctor_get(v___y_279_, 0);
if (lean_obj_tag(v_a_280_) == 0)
{
lean_dec_ref(v_f_256_);
return v___y_279_;
}
else
{
lean_object* v_a_281_; 
lean_inc_ref(v_a_280_);
lean_dec_ref_known(v___y_279_, 1);
v_a_281_ = lean_ctor_get(v_a_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref_known(v_a_280_, 1);
v_a_274_ = v_a_281_;
goto v___jp_273_;
}
}
else
{
lean_dec_ref(v_f_256_);
return v___y_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(lean_object* v_f_291_, lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
if (lean_obj_tag(v_x_292_) == 0)
{
lean_object* v_es_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_320_; 
v_es_306_ = lean_ctor_get(v_x_292_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_x_292_);
if (v_isSharedCheck_320_ == 0)
{
v___x_308_ = v_x_292_;
v_isShared_309_ = v_isSharedCheck_320_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_es_306_);
lean_dec(v_x_292_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_320_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_array_get_size(v_es_306_);
v___x_312_ = lean_nat_dec_lt(v___x_310_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_314_; 
lean_dec_ref(v_es_306_);
lean_dec_ref(v_f_291_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 1);
lean_ctor_set(v___x_308_, 0, v_x_293_);
v___x_314_ = v___x_308_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_x_293_);
v___x_314_ = v_reuseFailAlloc_316_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
else
{
size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
lean_del_object(v___x_308_);
v___x_317_ = ((size_t)0ULL);
v___x_318_ = lean_usize_of_nat(v___x_311_);
v___x_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_291_, v_es_306_, v___x_317_, v___x_318_, v_x_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec_ref(v_es_306_);
return v___x_319_;
}
}
}
else
{
lean_object* v_ks_321_; lean_object* v_vs_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_ks_321_ = lean_ctor_get(v_x_292_, 0);
lean_inc_ref(v_ks_321_);
v_vs_322_ = lean_ctor_get(v_x_292_, 1);
lean_inc_ref(v_vs_322_);
lean_dec_ref_known(v_x_292_, 2);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_291_, v_ks_321_, v_vs_322_, v___x_323_, v_x_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec_ref(v_vs_322_);
lean_dec_ref(v_ks_321_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_f_325_, lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_325_, v_x_326_, v_x_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec(v___y_329_);
lean_dec(v___y_328_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_f_341_ = _args[0];
lean_object* v_as_342_ = _args[1];
lean_object* v_i_343_ = _args[2];
lean_object* v_stop_344_ = _args[3];
lean_object* v_b_345_ = _args[4];
lean_object* v___y_346_ = _args[5];
lean_object* v___y_347_ = _args[6];
lean_object* v___y_348_ = _args[7];
lean_object* v___y_349_ = _args[8];
lean_object* v___y_350_ = _args[9];
lean_object* v___y_351_ = _args[10];
lean_object* v___y_352_ = _args[11];
lean_object* v___y_353_ = _args[12];
lean_object* v___y_354_ = _args[13];
lean_object* v___y_355_ = _args[14];
lean_object* v___y_356_ = _args[15];
lean_object* v___y_357_ = _args[16];
_start:
{
size_t v_i_boxed_358_; size_t v_stop_boxed_359_; lean_object* v_res_360_; 
v_i_boxed_358_ = lean_unbox_usize(v_i_343_);
lean_dec(v_i_343_);
v_stop_boxed_359_ = lean_unbox_usize(v_stop_344_);
lean_dec(v_stop_344_);
v_res_360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_341_, v_as_342_, v_i_boxed_358_, v_stop_boxed_359_, v_b_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v_as_342_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(lean_object* v_map_361_, lean_object* v_init_362_, lean_object* v_f_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___f_376_; lean_object* v___x_377_; 
v___f_376_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___lam__0___boxed), 16, 1);
lean_closure_set(v___f_376_, 0, v_f_363_);
lean_inc_ref(v_map_361_);
v___x_377_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v___f_376_, v_map_361_, v_init_362_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_386_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_386_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_a_382_; lean_object* v___x_384_; 
v_a_382_ = lean_ctor_get(v_a_378_, 0);
lean_inc(v_a_382_);
lean_dec(v_a_378_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v_a_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
v_a_387_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_377_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_377_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg___boxed(lean_object* v_map_395_, lean_object* v_init_396_, lean_object* v_f_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_map_395_, v_init_396_, v_f_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v_map_395_);
return v_res_410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__0));
v___x_413_ = lean_unsigned_to_nat(2u);
v___x_414_ = lean_unsigned_to_nat(23u);
v___x_415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__1));
v___x_416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_417_ = l_mkPanicMessageWithDecl(v___x_416_, v___x_415_, v___x_414_, v___x_413_, v___x_412_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v_vars_432_; lean_object* v_varMap_433_; lean_object* v___x_434_; lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_430_, 1);
v_vars_432_ = lean_ctor_get(v_a_431_, 10);
lean_inc_ref_n(v_vars_432_, 2);
v_varMap_433_ = lean_ctor_get(v_a_431_, 11);
lean_inc_ref(v_varMap_433_);
lean_dec(v_a_431_);
v___x_434_ = l_Lean_instInhabitedExpr;
v___f_435_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___boxed), 16, 2);
lean_closure_set(v___f_435_, 0, v_vars_432_);
lean_closure_set(v___f_435_, 1, v___x_434_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_varMap_433_, v___x_436_, v___f_435_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
lean_dec_ref(v_varMap_433_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_450_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_450_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_450_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_450_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_size_442_; uint8_t v___x_443_; 
v_size_442_ = lean_ctor_get(v_vars_432_, 2);
lean_inc(v_size_442_);
lean_dec_ref(v_vars_432_);
v___x_443_ = lean_nat_dec_eq(v_size_442_, v_a_438_);
lean_dec(v_a_438_);
lean_dec(v_size_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; 
lean_del_object(v___x_440_);
v___x_444_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___closed__1);
v___x_445_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_444_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
return v___x_445_;
}
else
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = lean_box(0);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_446_);
v___x_448_ = v___x_440_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v_vars_432_);
v_a_451_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_437_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_437_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
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
v_a_459_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_430_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_430_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___boxed(lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec(v_a_468_);
lean_dec(v_a_467_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2(lean_object* v_00_u03c3_480_, lean_object* v_00_u03b2_481_, lean_object* v_map_482_, lean_object* v_init_483_, lean_object* v_f_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___redArg(v_map_482_, v_init_483_, v_f_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_498_ = _args[0];
lean_object* v_00_u03b2_499_ = _args[1];
lean_object* v_map_500_ = _args[2];
lean_object* v_init_501_ = _args[3];
lean_object* v_f_502_ = _args[4];
lean_object* v___y_503_ = _args[5];
lean_object* v___y_504_ = _args[6];
lean_object* v___y_505_ = _args[7];
lean_object* v___y_506_ = _args[8];
lean_object* v___y_507_ = _args[9];
lean_object* v___y_508_ = _args[10];
lean_object* v___y_509_ = _args[11];
lean_object* v___y_510_ = _args[12];
lean_object* v___y_511_ = _args[13];
lean_object* v___y_512_ = _args[14];
lean_object* v___y_513_ = _args[15];
lean_object* v___y_514_ = _args[16];
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2(v_00_u03c3_498_, v_00_u03b2_499_, v_map_500_, v_init_501_, v_f_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v_map_500_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg(lean_object* v_map_516_, lean_object* v_f_517_, lean_object* v_init_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_517_, v_map_516_, v_init_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg___boxed(lean_object* v_map_532_, lean_object* v_f_533_, lean_object* v_init_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___redArg(v_map_532_, v_f_533_, v_init_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec(v___y_536_);
lean_dec(v___y_535_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2(lean_object* v_00_u03c3_548_, lean_object* v_00_u03c3_549_, lean_object* v_00_u03b2_550_, lean_object* v_map_551_, lean_object* v_f_552_, lean_object* v_init_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_552_, v_map_551_, v_init_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_567_ = _args[0];
lean_object* v_00_u03c3_568_ = _args[1];
lean_object* v_00_u03b2_569_ = _args[2];
lean_object* v_map_570_ = _args[3];
lean_object* v_f_571_ = _args[4];
lean_object* v_init_572_ = _args[5];
lean_object* v___y_573_ = _args[6];
lean_object* v___y_574_ = _args[7];
lean_object* v___y_575_ = _args[8];
lean_object* v___y_576_ = _args[9];
lean_object* v___y_577_ = _args[10];
lean_object* v___y_578_ = _args[11];
lean_object* v___y_579_ = _args[12];
lean_object* v___y_580_ = _args[13];
lean_object* v___y_581_ = _args[14];
lean_object* v___y_582_ = _args[15];
lean_object* v___y_583_ = _args[16];
lean_object* v___y_584_ = _args[17];
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2(v_00_u03c3_567_, v_00_u03c3_568_, v_00_u03b2_569_, v_map_570_, v_f_571_, v_init_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec(v___y_574_);
lean_dec(v___y_573_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3(lean_object* v_00_u03c3_586_, lean_object* v_00_u03c3_587_, lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_f_590_, lean_object* v_x_591_, lean_object* v_x_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___redArg(v_f_590_, v_x_591_, v_x_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03c3_606_ = _args[0];
lean_object* v_00_u03c3_607_ = _args[1];
lean_object* v_00_u03b1_608_ = _args[2];
lean_object* v_00_u03b2_609_ = _args[3];
lean_object* v_f_610_ = _args[4];
lean_object* v_x_611_ = _args[5];
lean_object* v_x_612_ = _args[6];
lean_object* v___y_613_ = _args[7];
lean_object* v___y_614_ = _args[8];
lean_object* v___y_615_ = _args[9];
lean_object* v___y_616_ = _args[10];
lean_object* v___y_617_ = _args[11];
lean_object* v___y_618_ = _args[12];
lean_object* v___y_619_ = _args[13];
lean_object* v___y_620_ = _args[14];
lean_object* v___y_621_ = _args[15];
lean_object* v___y_622_ = _args[16];
lean_object* v___y_623_ = _args[17];
lean_object* v___y_624_ = _args[18];
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3(v_00_u03c3_606_, v_00_u03c3_607_, v_00_u03b1_608_, v_00_u03b2_609_, v_f_610_, v_x_611_, v_x_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec(v___y_614_);
lean_dec(v___y_613_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_626_, lean_object* v_00_u03b2_627_, lean_object* v_00_u03c3_628_, lean_object* v_00_u03c3_629_, lean_object* v_f_630_, lean_object* v_as_631_, size_t v_i_632_, size_t v_stop_633_, lean_object* v_b_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_630_, v_as_631_, v_i_632_, v_stop_633_, v_b_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_00_u03b1_648_ = _args[0];
lean_object* v_00_u03b2_649_ = _args[1];
lean_object* v_00_u03c3_650_ = _args[2];
lean_object* v_00_u03c3_651_ = _args[3];
lean_object* v_f_652_ = _args[4];
lean_object* v_as_653_ = _args[5];
lean_object* v_i_654_ = _args[6];
lean_object* v_stop_655_ = _args[7];
lean_object* v_b_656_ = _args[8];
lean_object* v___y_657_ = _args[9];
lean_object* v___y_658_ = _args[10];
lean_object* v___y_659_ = _args[11];
lean_object* v___y_660_ = _args[12];
lean_object* v___y_661_ = _args[13];
lean_object* v___y_662_ = _args[14];
lean_object* v___y_663_ = _args[15];
lean_object* v___y_664_ = _args[16];
lean_object* v___y_665_ = _args[17];
lean_object* v___y_666_ = _args[18];
lean_object* v___y_667_ = _args[19];
lean_object* v___y_668_ = _args[20];
_start:
{
size_t v_i_boxed_669_; size_t v_stop_boxed_670_; lean_object* v_res_671_; 
v_i_boxed_669_ = lean_unbox_usize(v_i_654_);
lean_dec(v_i_654_);
v_stop_boxed_670_ = lean_unbox_usize(v_stop_655_);
lean_dec(v_stop_655_);
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__4(v_00_u03b1_648_, v_00_u03b2_649_, v_00_u03c3_650_, v_00_u03c3_651_, v_f_652_, v_as_653_, v_i_boxed_669_, v_stop_boxed_670_, v_b_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v_as_653_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_672_, lean_object* v_00_u03c3_673_, lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_f_676_, lean_object* v_keys_677_, lean_object* v_vals_678_, lean_object* v_heq_679_, lean_object* v_i_680_, lean_object* v_acc_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_676_, v_keys_677_, v_vals_678_, v_i_680_, v_acc_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_00_u03c3_695_ = _args[0];
lean_object* v_00_u03c3_696_ = _args[1];
lean_object* v_00_u03b1_697_ = _args[2];
lean_object* v_00_u03b2_698_ = _args[3];
lean_object* v_f_699_ = _args[4];
lean_object* v_keys_700_ = _args[5];
lean_object* v_vals_701_ = _args[6];
lean_object* v_heq_702_ = _args[7];
lean_object* v_i_703_ = _args[8];
lean_object* v_acc_704_ = _args[9];
lean_object* v___y_705_ = _args[10];
lean_object* v___y_706_ = _args[11];
lean_object* v___y_707_ = _args[12];
lean_object* v___y_708_ = _args[13];
lean_object* v___y_709_ = _args[14];
lean_object* v___y_710_ = _args[15];
lean_object* v___y_711_ = _args[16];
lean_object* v___y_712_ = _args[17];
lean_object* v___y_713_ = _args[18];
lean_object* v___y_714_ = _args[19];
lean_object* v___y_715_ = _args[20];
lean_object* v___y_716_ = _args[21];
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__2_spec__2_spec__3_spec__5(v_00_u03c3_695_, v_00_u03c3_696_, v_00_u03b1_697_, v_00_u03b2_698_, v_f_699_, v_keys_700_, v_vals_701_, v_heq_702_, v_i_703_, v_acc_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v_vals_701_);
lean_dec_ref(v_keys_700_);
return v_res_717_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__1));
v___x_721_ = lean_unsigned_to_nat(6u);
v___x_722_ = lean_unsigned_to_nat(36u);
v___x_723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0));
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_725_ = l_mkPanicMessageWithDecl(v___x_724_, v___x_723_, v___x_722_, v___x_721_, v___x_720_);
return v___x_725_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__4));
v___x_730_ = lean_unsigned_to_nat(6u);
v___x_731_ = lean_unsigned_to_nat(34u);
v___x_732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0));
v___x_733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_734_ = l_mkPanicMessageWithDecl(v___x_733_, v___x_732_, v___x_731_, v___x_730_, v___x_729_);
return v___x_734_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__6));
v___x_737_ = lean_unsigned_to_nat(4u);
v___x_738_ = lean_unsigned_to_nat(31u);
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__0));
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_741_ = l_mkPanicMessageWithDecl(v___x_740_, v___x_739_, v___x_738_, v___x_737_, v___x_736_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(lean_object* v_s_742_, uint8_t v_simplified_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___x_794_; 
v___x_794_ = l_Lean_Meta_Grind_AC_isCommutative(v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_836_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_836_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_836_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_836_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; uint8_t v___x_832_; 
v___x_832_ = lean_unbox(v_a_795_);
lean_dec(v_a_795_);
if (v___x_832_ == 0)
{
v___y_800_ = v_a_744_;
v___y_801_ = v_a_745_;
v___y_802_ = v_a_746_;
v___y_803_ = v_a_747_;
v___y_804_ = v_a_748_;
v___y_805_ = v_a_749_;
v___y_806_ = v_a_750_;
v___y_807_ = v_a_751_;
v___y_808_ = v_a_752_;
v___y_809_ = v_a_753_;
v___y_810_ = v_a_754_;
goto v___jp_799_;
}
else
{
uint8_t v___x_833_; 
v___x_833_ = l_Lean_Grind_AC_Seq_isSorted(v_s_742_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_del_object(v___x_797_);
v___x_834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__7);
v___x_835_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_834_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
return v___x_835_;
}
else
{
v___y_800_ = v_a_744_;
v___y_801_ = v_a_745_;
v___y_802_ = v_a_746_;
v___y_803_ = v_a_747_;
v___y_804_ = v_a_748_;
v___y_805_ = v_a_749_;
v___y_806_ = v_a_750_;
v___y_807_ = v_a_751_;
v___y_808_ = v_a_752_;
v___y_809_ = v_a_753_;
v___y_810_ = v_a_754_;
goto v___jp_799_;
}
}
v___jp_799_:
{
if (v_simplified_743_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = lean_box(0);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_811_);
v___x_813_ = v___x_797_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
else
{
lean_object* v___x_815_; 
lean_del_object(v___x_797_);
v___x_815_ = l_Lean_Meta_Grind_AC_hasNeutral(v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; uint8_t v___x_817_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v___x_815_, 1);
v___x_817_ = lean_unbox(v_a_816_);
lean_dec(v_a_816_);
if (v___x_817_ == 0)
{
v___y_757_ = v___y_800_;
v___y_758_ = v___y_801_;
v___y_759_ = v___y_802_;
v___y_760_ = v___y_803_;
v___y_761_ = v___y_804_;
v___y_762_ = v___y_805_;
v___y_763_ = v___y_806_;
v___y_764_ = v___y_807_;
v___y_765_ = v___y_808_;
v___y_766_ = v___y_809_;
v___y_767_ = v___y_810_;
goto v___jp_756_;
}
else
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = l_Lean_Grind_AC_Seq_contains(v_s_742_, v___x_818_);
if (v___x_819_ == 0)
{
v___y_757_ = v___y_800_;
v___y_758_ = v___y_801_;
v___y_759_ = v___y_802_;
v___y_760_ = v___y_803_;
v___y_761_ = v___y_804_;
v___y_762_ = v___y_805_;
v___y_763_ = v___y_806_;
v___y_764_ = v___y_807_;
v___y_765_ = v___y_808_;
v___y_766_ = v___y_809_;
v___y_767_ = v___y_810_;
goto v___jp_756_;
}
else
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__3));
v___x_821_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_742_, v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__5);
v___x_823_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_822_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
return v___x_823_;
}
else
{
v___y_757_ = v___y_800_;
v___y_758_ = v___y_801_;
v___y_759_ = v___y_802_;
v___y_760_ = v___y_803_;
v___y_761_ = v___y_804_;
v___y_762_ = v___y_805_;
v___y_763_ = v___y_806_;
v___y_764_ = v___y_807_;
v___y_765_ = v___y_808_;
v___y_766_ = v___y_809_;
v___y_767_ = v___y_810_;
goto v___jp_756_;
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_a_824_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_815_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_815_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v_a_837_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_794_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_794_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
v___jp_756_:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Meta_Grind_AC_isIdempotent(v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_785_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_785_ == 0)
{
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_785_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_785_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
uint8_t v___x_773_; 
v___x_773_ = lean_unbox(v_a_769_);
lean_dec(v_a_769_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_box(0);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_774_);
v___x_776_ = v___x_771_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
uint8_t v___x_778_; 
v___x_778_ = l_Lean_Grind_AC_Seq_noAdjacentDuplicates(v_s_742_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_del_object(v___x_771_);
v___x_779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___closed__2);
v___x_780_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars_spec__0(v___x_779_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
return v___x_780_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = lean_box(0);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_781_);
v___x_783_ = v___x_771_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_786_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_768_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_768_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq___boxed(lean_object* v_s_845_, lean_object* v_simplified_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
uint8_t v_simplified_boxed_859_; lean_object* v_res_860_; 
v_simplified_boxed_859_ = lean_unbox(v_simplified_846_);
v_res_860_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(v_s_845_, v_simplified_boxed_859_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_s_845_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(lean_object* v_lhs_861_, lean_object* v_rhs_862_, uint8_t v_simplified_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(v_lhs_861_, v_simplified_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_877_; 
lean_dec_ref_known(v___x_876_, 1);
v___x_877_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkSeq(v_rhs_862_, v_simplified_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
return v___x_877_;
}
else
{
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs___boxed(lean_object* v_lhs_878_, lean_object* v_rhs_879_, lean_object* v_simplified_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
uint8_t v_simplified_boxed_893_; lean_object* v_res_894_; 
v_simplified_boxed_893_ = lean_unbox(v_simplified_880_);
v_res_894_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_878_, v_rhs_879_, v_simplified_boxed_893_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_rhs_879_);
lean_dec_ref(v_lhs_878_);
return v_res_894_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0(void){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(lean_object* v_msg_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; lean_object* v___f_910_; lean_object* v___x_3465__overap_911_; lean_object* v___x_912_; 
v___x_909_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___closed__0);
v___f_910_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_910_, 0, v___x_909_);
v___x_3465__overap_911_ = lean_panic_fn_borrowed(v___f_910_, v_msg_896_);
lean_dec_ref(v___f_910_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
lean_inc(v___y_901_);
lean_inc_ref(v___y_900_);
lean_inc(v___y_899_);
lean_inc(v___y_898_);
lean_inc(v___y_897_);
v___x_912_ = lean_apply_12(v___x_3465__overap_911_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, lean_box(0));
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0___boxed(lean_object* v_msg_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(v_msg_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec(v___y_915_);
lean_dec(v___y_914_);
return v_res_926_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0(void){
_start:
{
uint8_t v___x_927_; lean_object* v___x_928_; 
v___x_927_ = 2;
v___x_928_ = l_Ordering_ctorIdx(v___x_927_);
return v___x_928_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_931_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__2));
v___x_932_ = lean_unsigned_to_nat(4u);
v___x_933_ = lean_unsigned_to_nat(43u);
v___x_934_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__1));
v___x_935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars___lam__0___closed__0));
v___x_936_ = l_mkPanicMessageWithDecl(v___x_935_, v___x_934_, v___x_933_, v___x_932_, v___x_931_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(lean_object* v_as_x27_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
if (lean_obj_tag(v_as_x27_937_) == 0)
{
lean_object* v___x_951_; 
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v_b_938_);
return v___x_951_;
}
else
{
lean_object* v_head_952_; lean_object* v_tail_953_; lean_object* v_lhs_954_; lean_object* v_rhs_955_; uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_head_952_ = lean_ctor_get(v_as_x27_937_, 0);
v_tail_953_ = lean_ctor_get(v_as_x27_937_, 1);
v_lhs_954_ = lean_ctor_get(v_head_952_, 0);
v_rhs_955_ = lean_ctor_get(v_head_952_, 1);
v___x_956_ = l_Lean_Grind_AC_Seq_compare(v_lhs_954_, v_rhs_955_);
v___x_957_ = l_Ordering_ctorIdx(v___x_956_);
v___x_958_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__0);
v___x_959_ = lean_nat_dec_eq(v___x_957_, v___x_958_);
lean_dec(v___x_957_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___closed__3);
v___x_961_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__0(v___x_960_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_972_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_972_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_972_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_972_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
if (lean_obj_tag(v_a_962_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_968_; 
v_a_966_ = lean_ctor_get(v_a_962_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v_a_962_, 1);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v_a_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
else
{
lean_object* v_a_970_; 
lean_del_object(v___x_964_);
v_a_970_ = lean_ctor_get(v_a_962_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v_a_962_, 1);
v_as_x27_937_ = v_tail_953_;
v_b_938_ = v_a_970_;
goto _start;
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_a_973_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_961_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_961_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v___x_981_; 
v___x_981_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_954_, v_rhs_955_, v___x_959_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v___x_982_; 
lean_dec_ref_known(v___x_981_, 1);
v___x_982_ = lean_box(0);
v_as_x27_937_ = v_tail_953_;
v_b_938_ = v___x_982_;
goto _start;
}
else
{
return v___x_981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg___boxed(lean_object* v_as_x27_984_, lean_object* v_b_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_as_x27_984_, v_b_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec(v___y_987_);
lean_dec(v___y_986_);
lean_dec(v_as_x27_984_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v_basis_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v_basis_1013_ = lean_ctor_get(v_a_1012_, 15);
lean_inc(v_basis_1013_);
lean_dec(v_a_1012_);
v___x_1014_ = lean_box(0);
v___x_1015_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_basis_1013_, v___x_1014_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_basis_1013_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v___x_1015_, 0);
lean_dec(v_unused_1023_);
v___x_1017_ = v___x_1015_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v___x_1015_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1014_);
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1014_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
return v___x_1015_;
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1011_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1011_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis___boxed(lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
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
lean_dec(v_a_1032_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1(lean_object* v_as_1045_, lean_object* v_as_x27_1046_, lean_object* v_b_1047_, lean_object* v_a_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___redArg(v_as_x27_1046_, v_b_1047_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1___boxed(lean_object* v_as_1062_, lean_object* v_as_x27_1063_, lean_object* v_b_1064_, lean_object* v_a_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis_spec__1(v_as_1062_, v_as_x27_1063_, v_b_1064_, v_a_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec(v_as_x27_1063_);
lean_dec(v_as_1062_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(lean_object* v_init_1079_, lean_object* v_x_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
lean_object* v_k_1093_; lean_object* v_l_1094_; lean_object* v_r_1095_; lean_object* v___x_1096_; 
v_k_1093_ = lean_ctor_get(v_x_1080_, 1);
v_l_1094_ = lean_ctor_get(v_x_1080_, 3);
v_r_1095_ = lean_ctor_get(v_x_1080_, 4);
v___x_1096_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v_init_1079_, v_l_1094_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_lhs_1097_; lean_object* v_rhs_1098_; uint8_t v___x_1099_; lean_object* v___x_1100_; 
lean_dec_ref_known(v___x_1096_, 1);
v_lhs_1097_ = lean_ctor_get(v_k_1093_, 0);
v_rhs_1098_ = lean_ctor_get(v_k_1093_, 1);
v___x_1099_ = 0;
v___x_1100_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1097_, v_rhs_1098_, v___x_1099_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v___x_1101_; 
lean_dec_ref_known(v___x_1100_, 1);
v___x_1101_ = lean_box(0);
v_init_1079_ = v___x_1101_;
v_x_1080_ = v_r_1095_;
goto _start;
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1100_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1100_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
return v___x_1096_;
}
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_init_1079_);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0___boxed(lean_object* v_init_1113_, lean_object* v_x_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v_init_1113_, v_x_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec(v_x_1114_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v_queue_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v_queue_1142_ = lean_ctor_get(v_a_1141_, 14);
lean_inc(v_queue_1142_);
lean_dec(v_a_1141_);
v___x_1143_ = lean_box(0);
v___x_1144_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue_spec__0(v___x_1143_, v_queue_1142_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_queue_1142_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v___x_1144_, 0);
lean_dec(v_unused_1152_);
v___x_1146_ = v___x_1144_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_dec(v___x_1144_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1143_);
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1143_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
v_a_1153_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1144_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1144_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
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
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v_a_1161_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1140_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1140_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue___boxed(lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec(v_a_1169_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(lean_object* v_as_1185_, size_t v_sz_1186_, size_t v_i_1187_, lean_object* v_b_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v___x_1201_; 
v___x_1201_ = lean_usize_dec_lt(v_i_1187_, v_sz_1186_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v_b_1188_);
return v___x_1202_;
}
else
{
lean_object* v_a_1203_; lean_object* v_lhs_1204_; lean_object* v_rhs_1205_; lean_object* v___x_1206_; 
lean_dec_ref(v_b_1188_);
v_a_1203_ = lean_array_uget_borrowed(v_as_1185_, v_i_1187_);
v_lhs_1204_ = lean_ctor_get(v_a_1203_, 0);
v_rhs_1205_ = lean_ctor_get(v_a_1203_, 1);
v___x_1206_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1204_, v_rhs_1205_, v___x_1201_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v___x_1207_; size_t v___x_1208_; size_t v___x_1209_; 
lean_dec_ref_known(v___x_1206_, 1);
v___x_1207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0));
v___x_1208_ = ((size_t)1ULL);
v___x_1209_ = lean_usize_add(v_i_1187_, v___x_1208_);
v_i_1187_ = v___x_1209_;
v_b_1188_ = v___x_1207_;
goto _start;
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
v_a_1211_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1206_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1206_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1219_, lean_object* v_sz_1220_, lean_object* v_i_1221_, lean_object* v_b_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
size_t v_sz_boxed_1235_; size_t v_i_boxed_1236_; lean_object* v_res_1237_; 
v_sz_boxed_1235_ = lean_unbox_usize(v_sz_1220_);
lean_dec(v_sz_1220_);
v_i_boxed_1236_ = lean_unbox_usize(v_i_1221_);
lean_dec(v_i_1221_);
v_res_1237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(v_as_1219_, v_sz_boxed_1235_, v_i_boxed_1236_, v_b_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v_as_1219_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(lean_object* v_as_1238_, size_t v_sz_1239_, size_t v_i_1240_, lean_object* v_b_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_usize_dec_lt(v_i_1240_, v_sz_1239_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_b_1241_);
return v___x_1255_;
}
else
{
lean_object* v_a_1256_; lean_object* v_lhs_1257_; lean_object* v_rhs_1258_; lean_object* v___x_1259_; 
lean_dec_ref(v_b_1241_);
v_a_1256_ = lean_array_uget_borrowed(v_as_1238_, v_i_1240_);
v_lhs_1257_ = lean_ctor_get(v_a_1256_, 0);
v_rhs_1258_ = lean_ctor_get(v_a_1256_, 1);
v___x_1259_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1257_, v_rhs_1258_, v___x_1254_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
lean_dec_ref_known(v___x_1259_, 1);
v___x_1260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4___closed__0));
v___x_1261_ = ((size_t)1ULL);
v___x_1262_ = lean_usize_add(v_i_1240_, v___x_1261_);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1_spec__4(v_as_1238_, v_sz_1239_, v___x_1262_, v___x_1260_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1263_;
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
v_a_1264_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1259_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1259_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1___boxed(lean_object* v_as_1272_, lean_object* v_sz_1273_, lean_object* v_i_1274_, lean_object* v_b_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
size_t v_sz_boxed_1288_; size_t v_i_boxed_1289_; lean_object* v_res_1290_; 
v_sz_boxed_1288_ = lean_unbox_usize(v_sz_1273_);
lean_dec(v_sz_1273_);
v_i_boxed_1289_ = lean_unbox_usize(v_i_1274_);
lean_dec(v_i_1274_);
v_res_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(v_as_1272_, v_sz_boxed_1288_, v_i_boxed_1289_, v_b_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v_as_1272_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_1294_, size_t v_sz_1295_, size_t v_i_1296_, lean_object* v_b_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_usize_dec_lt(v_i_1296_, v_sz_1295_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v_b_1297_);
return v___x_1311_;
}
else
{
lean_object* v_a_1312_; lean_object* v_lhs_1313_; lean_object* v_rhs_1314_; lean_object* v___x_1315_; 
lean_dec_ref(v_b_1297_);
v_a_1312_ = lean_array_uget_borrowed(v_as_1294_, v_i_1296_);
v_lhs_1313_ = lean_ctor_get(v_a_1312_, 0);
v_rhs_1314_ = lean_ctor_get(v_a_1312_, 1);
v___x_1315_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1313_, v_rhs_1314_, v___x_1310_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; 
lean_dec_ref_known(v___x_1315_, 1);
v___x_1316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_1317_ = ((size_t)1ULL);
v___x_1318_ = lean_usize_add(v_i_1296_, v___x_1317_);
v_i_1296_ = v___x_1318_;
v_b_1297_ = v___x_1316_;
goto _start;
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
v_a_1320_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1315_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1315_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_1328_, lean_object* v_sz_1329_, lean_object* v_i_1330_, lean_object* v_b_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
size_t v_sz_boxed_1344_; size_t v_i_boxed_1345_; lean_object* v_res_1346_; 
v_sz_boxed_1344_ = lean_unbox_usize(v_sz_1329_);
lean_dec(v_sz_1329_);
v_i_boxed_1345_ = lean_unbox_usize(v_i_1330_);
lean_dec(v_i_1330_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_1328_, v_sz_boxed_1344_, v_i_boxed_1345_, v_b_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v_as_1328_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(lean_object* v_as_1347_, size_t v_sz_1348_, size_t v_i_1349_, lean_object* v_b_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_usize_dec_lt(v_i_1349_, v_sz_1348_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_b_1350_);
return v___x_1364_;
}
else
{
lean_object* v_a_1365_; lean_object* v_lhs_1366_; lean_object* v_rhs_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v_b_1350_);
v_a_1365_ = lean_array_uget_borrowed(v_as_1347_, v_i_1349_);
v_lhs_1366_ = lean_ctor_get(v_a_1365_, 0);
v_rhs_1367_ = lean_ctor_get(v_a_1365_, 1);
v___x_1368_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkLhsRhs(v_lhs_1366_, v_rhs_1367_, v___x_1363_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; size_t v___x_1370_; size_t v___x_1371_; lean_object* v___x_1372_; 
lean_dec_ref_known(v___x_1368_, 1);
v___x_1369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_1370_ = ((size_t)1ULL);
v___x_1371_ = lean_usize_add(v_i_1349_, v___x_1370_);
v___x_1372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_1347_, v_sz_1348_, v___x_1371_, v___x_1369_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
return v___x_1372_;
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_a_1373_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1368_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1368_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1381_, lean_object* v_sz_1382_, lean_object* v_i_1383_, lean_object* v_b_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
size_t v_sz_boxed_1397_; size_t v_i_boxed_1398_; lean_object* v_res_1399_; 
v_sz_boxed_1397_ = lean_unbox_usize(v_sz_1382_);
lean_dec(v_sz_1382_);
v_i_boxed_1398_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_res_1399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(v_as_1381_, v_sz_boxed_1397_, v_i_boxed_1398_, v_b_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v_as_1381_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(lean_object* v_init_1400_, lean_object* v_n_1401_, lean_object* v_b_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
if (lean_obj_tag(v_n_1401_) == 0)
{
lean_object* v_cs_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; size_t v_sz_1418_; size_t v___x_1419_; lean_object* v___x_1420_; 
v_cs_1415_ = lean_ctor_get(v_n_1401_, 0);
v___x_1416_ = lean_box(0);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
lean_ctor_set(v___x_1417_, 1, v_b_1402_);
v_sz_1418_ = lean_array_size(v_cs_1415_);
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(v_init_1400_, v_cs_1415_, v_sz_1418_, v___x_1419_, v___x_1417_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1435_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1435_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1435_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_fst_1425_; 
v_fst_1425_ = lean_ctor_get(v_a_1421_, 0);
if (lean_obj_tag(v_fst_1425_) == 0)
{
lean_object* v_snd_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v_snd_1426_ = lean_ctor_get(v_a_1421_, 1);
lean_inc(v_snd_1426_);
lean_dec(v_a_1421_);
v___x_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_snd_1426_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1427_);
v___x_1429_ = v___x_1423_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
else
{
lean_object* v_val_1431_; lean_object* v___x_1433_; 
lean_inc_ref(v_fst_1425_);
lean_dec(v_a_1421_);
v_val_1431_ = lean_ctor_get(v_fst_1425_, 0);
lean_inc(v_val_1431_);
lean_dec_ref_known(v_fst_1425_, 1);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_val_1431_);
v___x_1433_ = v___x_1423_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_val_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1420_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1420_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_object* v_vs_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; size_t v_sz_1447_; size_t v___x_1448_; lean_object* v___x_1449_; 
v_vs_1444_ = lean_ctor_get(v_n_1401_, 0);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v_b_1402_);
v_sz_1447_ = lean_array_size(v_vs_1444_);
v___x_1448_ = ((size_t)0ULL);
v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__2(v_vs_1444_, v_sz_1447_, v___x_1448_, v___x_1446_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1464_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1464_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1464_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v_fst_1454_; 
v_fst_1454_ = lean_ctor_get(v_a_1450_, 0);
if (lean_obj_tag(v_fst_1454_) == 0)
{
lean_object* v_snd_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v_snd_1455_ = lean_ctor_get(v_a_1450_, 1);
lean_inc(v_snd_1455_);
lean_dec(v_a_1450_);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_snd_1455_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1456_);
v___x_1458_ = v___x_1452_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
else
{
lean_object* v_val_1460_; lean_object* v___x_1462_; 
lean_inc_ref(v_fst_1454_);
lean_dec(v_a_1450_);
v_val_1460_ = lean_ctor_get(v_fst_1454_, 0);
lean_inc(v_val_1460_);
lean_dec_ref_known(v_fst_1454_, 1);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v_val_1460_);
v___x_1462_ = v___x_1452_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_val_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
v_a_1465_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1449_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1449_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(lean_object* v_init_1473_, lean_object* v_as_1474_, size_t v_sz_1475_, size_t v_i_1476_, lean_object* v_b_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_usize_dec_lt(v_i_1476_, v_sz_1475_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_b_1477_);
return v___x_1491_;
}
else
{
lean_object* v_snd_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1526_; 
v_snd_1492_ = lean_ctor_get(v_b_1477_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_b_1477_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v_b_1477_, 0);
lean_dec(v_unused_1527_);
v___x_1494_ = v_b_1477_;
v_isShared_1495_ = v_isSharedCheck_1526_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_snd_1492_);
lean_dec(v_b_1477_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1526_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_a_1496_; lean_object* v___x_1497_; 
v_a_1496_ = lean_array_uget_borrowed(v_as_1474_, v_i_1476_);
lean_inc(v_snd_1492_);
v___x_1497_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_1473_, v_a_1496_, v_snd_1492_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1517_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1517_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1517_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
if (lean_obj_tag(v_a_1498_) == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_a_1498_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1502_);
v___x_1504_ = v___x_1494_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_snd_1492_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1504_);
v___x_1506_ = v___x_1500_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_del_object(v___x_1500_);
lean_dec(v_snd_1492_);
v_a_1509_ = lean_ctor_get(v_a_1498_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v_a_1498_, 1);
v___x_1510_ = lean_box(0);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v_a_1509_);
lean_ctor_set(v___x_1494_, 0, v___x_1510_);
v___x_1512_ = v___x_1494_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_a_1509_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
size_t v___x_1513_; size_t v___x_1514_; 
v___x_1513_ = ((size_t)1ULL);
v___x_1514_ = lean_usize_add(v_i_1476_, v___x_1513_);
v_i_1476_ = v___x_1514_;
v_b_1477_ = v___x_1512_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
v_a_1518_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1497_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1497_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1528_ = _args[0];
lean_object* v_as_1529_ = _args[1];
lean_object* v_sz_1530_ = _args[2];
lean_object* v_i_1531_ = _args[3];
lean_object* v_b_1532_ = _args[4];
lean_object* v___y_1533_ = _args[5];
lean_object* v___y_1534_ = _args[6];
lean_object* v___y_1535_ = _args[7];
lean_object* v___y_1536_ = _args[8];
lean_object* v___y_1537_ = _args[9];
lean_object* v___y_1538_ = _args[10];
lean_object* v___y_1539_ = _args[11];
lean_object* v___y_1540_ = _args[12];
lean_object* v___y_1541_ = _args[13];
lean_object* v___y_1542_ = _args[14];
lean_object* v___y_1543_ = _args[15];
lean_object* v___y_1544_ = _args[16];
_start:
{
size_t v_sz_boxed_1545_; size_t v_i_boxed_1546_; lean_object* v_res_1547_; 
v_sz_boxed_1545_ = lean_unbox_usize(v_sz_1530_);
lean_dec(v_sz_1530_);
v_i_boxed_1546_ = lean_unbox_usize(v_i_1531_);
lean_dec(v_i_1531_);
v_res_1547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0_spec__1(v_init_1528_, v_as_1529_, v_sz_boxed_1545_, v_i_boxed_1546_, v_b_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v_as_1529_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0___boxed(lean_object* v_init_1548_, lean_object* v_n_1549_, lean_object* v_b_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_1548_, v_n_1549_, v_b_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v_n_1549_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(lean_object* v_t_1564_, lean_object* v_init_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_root_1578_; lean_object* v_tail_1579_; lean_object* v___x_1580_; 
v_root_1578_ = lean_ctor_get(v_t_1564_, 0);
v_tail_1579_ = lean_ctor_get(v_t_1564_, 1);
v___x_1580_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__0(v_init_1565_, v_root_1578_, v_init_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1617_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1617_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1617_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
if (lean_obj_tag(v_a_1581_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; 
v_a_1585_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v_a_1581_, 1);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v_a_1585_);
v___x_1587_ = v___x_1583_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; size_t v_sz_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
lean_del_object(v___x_1583_);
v_a_1589_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v_a_1581_, 1);
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set(v___x_1591_, 1, v_a_1589_);
v_sz_1592_ = lean_array_size(v_tail_1579_);
v___x_1593_ = ((size_t)0ULL);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0_spec__1(v_tail_1579_, v_sz_1592_, v___x_1593_, v___x_1591_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1608_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1608_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1608_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_fst_1599_; 
v_fst_1599_ = lean_ctor_get(v_a_1595_, 0);
if (lean_obj_tag(v_fst_1599_) == 0)
{
lean_object* v_snd_1600_; lean_object* v___x_1602_; 
v_snd_1600_ = lean_ctor_get(v_a_1595_, 1);
lean_inc(v_snd_1600_);
lean_dec(v_a_1595_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v_snd_1600_);
v___x_1602_ = v___x_1597_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_snd_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
else
{
lean_object* v_val_1604_; lean_object* v___x_1606_; 
lean_inc_ref(v_fst_1599_);
lean_dec(v_a_1595_);
v_val_1604_ = lean_ctor_get(v_fst_1599_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v_fst_1599_, 1);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v_val_1604_);
v___x_1606_ = v___x_1597_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_val_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
v_a_1609_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1594_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1594_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
v_a_1618_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1580_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1580_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0___boxed(lean_object* v_t_1626_, lean_object* v_init_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(v_t_1626_, v_init_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v_t_1626_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v_diseqs_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
v_diseqs_1655_ = lean_ctor_get(v_a_1654_, 16);
lean_inc_ref(v_diseqs_1655_);
lean_dec(v_a_1654_);
v___x_1656_ = lean_box(0);
v___x_1657_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs_spec__0(v_diseqs_1655_, v___x_1656_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
lean_dec_ref(v_diseqs_1655_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v___x_1657_, 0);
lean_dec(v_unused_1665_);
v___x_1659_ = v___x_1657_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_dec(v___x_1657_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1656_);
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1656_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
else
{
return v___x_1657_;
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_a_1666_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1653_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1653_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs___boxed(lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec(v_a_1674_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkVars(v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v___x_1700_; 
lean_dec_ref_known(v___x_1699_, 1);
v___x_1700_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkBasis(v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v___x_1701_; 
lean_dec_ref_known(v___x_1700_, 1);
v___x_1701_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkQueue(v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v___x_1702_; 
lean_dec_ref_known(v___x_1701_, 1);
v___x_1702_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkDiseqs(v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1702_;
}
else
{
return v___x_1701_;
}
}
else
{
return v___x_1700_;
}
}
else
{
return v___x_1699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs___boxed(lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec(v_a_1703_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(lean_object* v_upperBound_1716_, lean_object* v_a_1717_, lean_object* v_b_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
uint8_t v___x_1730_; 
v___x_1730_ = lean_nat_dec_lt(v_a_1717_, v_upperBound_1716_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; 
lean_dec(v_a_1717_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_b_1718_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; 
v___x_1732_ = l___private_Lean_Meta_Tactic_Grind_AC_Inv_0__Lean_Meta_Grind_AC_checkStructInvs(v_a_1717_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec_ref_known(v___x_1732_, 1);
v___x_1733_ = lean_box(0);
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_add(v_a_1717_, v___x_1734_);
lean_dec(v_a_1717_);
v_a_1717_ = v___x_1735_;
v_b_1718_ = v___x_1733_;
goto _start;
}
else
{
lean_dec(v_a_1717_);
return v___x_1732_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg___boxed(lean_object* v_upperBound_1737_, lean_object* v_a_1738_, lean_object* v_b_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(v_upperBound_1737_, v_a_1738_, v_b_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec(v_upperBound_1737_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkInvariants(lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
uint8_t v_debug_1763_; 
v_debug_1763_ = lean_ctor_get_uint8(v_a_1754_, sizeof(void*)*8 + 2);
if (v_debug_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
else
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_1752_, v_a_1760_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v_structs_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v_structs_1768_ = lean_ctor_get(v_a_1767_, 0);
lean_inc_ref(v_structs_1768_);
lean_dec(v_a_1767_);
v___x_1769_ = lean_array_get_size(v_structs_1768_);
lean_dec_ref(v_structs_1768_);
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = lean_box(0);
v___x_1772_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(v___x_1769_, v___x_1770_, v___x_1771_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v___x_1772_, 0);
lean_dec(v_unused_1780_);
v___x_1774_ = v___x_1772_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_dec(v___x_1772_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1771_);
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1771_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
else
{
return v___x_1772_;
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1766_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1766_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkInvariants___boxed(lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Meta_Grind_AC_checkInvariants(v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec(v_a_1789_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0(lean_object* v_upperBound_1801_, lean_object* v_inst_1802_, lean_object* v_R_1803_, lean_object* v_a_1804_, lean_object* v_b_1805_, lean_object* v_c_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___redArg(v_upperBound_1801_, v_a_1804_, v_b_1805_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1819_ = _args[0];
lean_object* v_inst_1820_ = _args[1];
lean_object* v_R_1821_ = _args[2];
lean_object* v_a_1822_ = _args[3];
lean_object* v_b_1823_ = _args[4];
lean_object* v_c_1824_ = _args[5];
lean_object* v___y_1825_ = _args[6];
lean_object* v___y_1826_ = _args[7];
lean_object* v___y_1827_ = _args[8];
lean_object* v___y_1828_ = _args[9];
lean_object* v___y_1829_ = _args[10];
lean_object* v___y_1830_ = _args[11];
lean_object* v___y_1831_ = _args[12];
lean_object* v___y_1832_ = _args[13];
lean_object* v___y_1833_ = _args[14];
lean_object* v___y_1834_ = _args[15];
lean_object* v___y_1835_ = _args[16];
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_AC_checkInvariants_spec__0(v_upperBound_1819_, v_inst_1820_, v_R_1821_, v_a_1822_, v_b_1823_, v_c_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec(v_upperBound_1819_);
return v_res_1836_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Inv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
