// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM import Lean.Meta.Tactic.Grind.Arith.Insts import Lean.OrderLevel
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "PowIdentity available: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "NoNatZeroDivisors available: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(17, 56, 209, 254, 185, 203, 153, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toCommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(134, 95, 181, 253, 18, 104, 213, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "new ring: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23_value),LEAN_SCALAR_PTR_LITERAL(134, 3, 13, 60, 96, 160, 201, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "OfCommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ofCommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(219, 56, 247, 159, 186, 83, 86, 251)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(36, 61, 219, 203, 190, 113, 236, 200)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 171, 186, 15, 174, 251, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "toNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(156, 107, 255, 119, 73, 35, 26, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__23_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__29_value),LEAN_SCALAR_PTR_LITERAL(8, 241, 181, 204, 215, 46, 40, 252)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__31_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__33_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__35_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__36_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__38_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__38_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__40_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__40_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__41_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__42 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__42_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__42_value),LEAN_SCALAR_PTR_LITERAL(84, 97, 73, 37, 143, 22, 233, 204)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__44_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__44_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__45_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__46_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__46_value),LEAN_SCALAR_PTR_LITERAL(1, 189, 244, 99, 68, 50, 19, 202)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "PowIdentity available: false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__51 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__51_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "instNoNatZeroDivisorsQOfAddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__51_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value),LEAN_SCALAR_PTR_LITERAL(221, 130, 167, 21, 145, 237, 132, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__54_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__54_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__55_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "instIsCharPQOfAddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__59_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__59_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__59_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__59_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__59_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__51_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__59_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value),LEAN_SCALAR_PTR_LITERAL(194, 21, 126, 159, 192, 171, 59, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__59 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__59_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__51_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 238, 182, 216, 107, 45, 243, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "`grind` unexpected failure, failure to initialize ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0(lean_object* v_00_u03b2_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__1);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0(lean_object* v___x_6_, lean_object* v_s_7_){
_start:
{
lean_object* v_rings_8_; lean_object* v_typeIdOf_9_; lean_object* v_exprToRingId_10_; lean_object* v_semirings_11_; lean_object* v_stypeIdOf_12_; lean_object* v_exprToSemiringId_13_; lean_object* v_ncRings_14_; lean_object* v_exprToNCRingId_15_; lean_object* v_nctypeIdOf_16_; lean_object* v_ncSemirings_17_; lean_object* v_exprToNCSemiringId_18_; lean_object* v_ncstypeIdOf_19_; lean_object* v_steps_20_; uint8_t v_reportedMaxDegreeIssue_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_29_; 
v_rings_8_ = lean_ctor_get(v_s_7_, 0);
v_typeIdOf_9_ = lean_ctor_get(v_s_7_, 1);
v_exprToRingId_10_ = lean_ctor_get(v_s_7_, 2);
v_semirings_11_ = lean_ctor_get(v_s_7_, 3);
v_stypeIdOf_12_ = lean_ctor_get(v_s_7_, 4);
v_exprToSemiringId_13_ = lean_ctor_get(v_s_7_, 5);
v_ncRings_14_ = lean_ctor_get(v_s_7_, 6);
v_exprToNCRingId_15_ = lean_ctor_get(v_s_7_, 7);
v_nctypeIdOf_16_ = lean_ctor_get(v_s_7_, 8);
v_ncSemirings_17_ = lean_ctor_get(v_s_7_, 9);
v_exprToNCSemiringId_18_ = lean_ctor_get(v_s_7_, 10);
v_ncstypeIdOf_19_ = lean_ctor_get(v_s_7_, 11);
v_steps_20_ = lean_ctor_get(v_s_7_, 12);
v_reportedMaxDegreeIssue_21_ = lean_ctor_get_uint8(v_s_7_, sizeof(void*)*13);
v_isSharedCheck_29_ = !lean_is_exclusive(v_s_7_);
if (v_isSharedCheck_29_ == 0)
{
v___x_23_ = v_s_7_;
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_steps_20_);
lean_inc(v_ncstypeIdOf_19_);
lean_inc(v_exprToNCSemiringId_18_);
lean_inc(v_ncSemirings_17_);
lean_inc(v_nctypeIdOf_16_);
lean_inc(v_exprToNCRingId_15_);
lean_inc(v_ncRings_14_);
lean_inc(v_exprToSemiringId_13_);
lean_inc(v_stypeIdOf_12_);
lean_inc(v_semirings_11_);
lean_inc(v_exprToRingId_10_);
lean_inc(v_typeIdOf_9_);
lean_inc(v_rings_8_);
lean_dec(v_s_7_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_25_; lean_object* v___x_27_; 
v___x_25_ = lean_array_push(v_rings_8_, v___x_6_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 0, v___x_25_);
v___x_27_ = v___x_23_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_25_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_typeIdOf_9_);
lean_ctor_set(v_reuseFailAlloc_28_, 2, v_exprToRingId_10_);
lean_ctor_set(v_reuseFailAlloc_28_, 3, v_semirings_11_);
lean_ctor_set(v_reuseFailAlloc_28_, 4, v_stypeIdOf_12_);
lean_ctor_set(v_reuseFailAlloc_28_, 5, v_exprToSemiringId_13_);
lean_ctor_set(v_reuseFailAlloc_28_, 6, v_ncRings_14_);
lean_ctor_set(v_reuseFailAlloc_28_, 7, v_exprToNCRingId_15_);
lean_ctor_set(v_reuseFailAlloc_28_, 8, v_nctypeIdOf_16_);
lean_ctor_set(v_reuseFailAlloc_28_, 9, v_ncSemirings_17_);
lean_ctor_set(v_reuseFailAlloc_28_, 10, v_exprToNCSemiringId_18_);
lean_ctor_set(v_reuseFailAlloc_28_, 11, v_ncstypeIdOf_19_);
lean_ctor_set(v_reuseFailAlloc_28_, 12, v_steps_20_);
lean_ctor_set_uint8(v_reuseFailAlloc_28_, sizeof(void*)*13, v_reportedMaxDegreeIssue_21_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(lean_object* v___x_33_, lean_object* v_____do__lift_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_options_46_; uint8_t v_hasTrace_47_; 
v_options_46_ = lean_ctor_get(v___y_43_, 2);
v_hasTrace_47_ = lean_ctor_get_uint8(v_options_46_, sizeof(void*)*1);
if (v_hasTrace_47_ == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v___x_33_);
v___x_48_ = lean_box(v_hasTrace_47_);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
else
{
lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_50_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___closed__1));
v___x_51_ = l_Lean_Name_append(v___x_50_, v___x_33_);
v___x_52_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_34_, v_options_46_, v___x_51_);
lean_dec(v___x_51_);
v___x_53_ = lean_box(v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___boxed(lean_object* v___x_55_, lean_object* v_____do__lift_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(v___x_55_, v_____do__lift_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec(v___y_57_);
lean_dec_ref(v_____do__lift_56_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(lean_object* v_msgData_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v_env_76_; lean_object* v___x_77_; lean_object* v_mctx_78_; lean_object* v_lctx_79_; lean_object* v_options_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_75_ = lean_st_ref_get(v___y_73_);
v_env_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_ref(v_env_76_);
lean_dec(v___x_75_);
v___x_77_ = lean_st_ref_get(v___y_71_);
v_mctx_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc_ref(v_mctx_78_);
lean_dec(v___x_77_);
v_lctx_79_ = lean_ctor_get(v___y_70_, 2);
v_options_80_ = lean_ctor_get(v___y_72_, 2);
lean_inc_ref(v_options_80_);
lean_inc_ref(v_lctx_79_);
v___x_81_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_81_, 0, v_env_76_);
lean_ctor_set(v___x_81_, 1, v_mctx_78_);
lean_ctor_set(v___x_81_, 2, v_lctx_79_);
lean_ctor_set(v___x_81_, 3, v_options_80_);
v___x_82_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v_msgData_69_);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1___boxed(lean_object* v_msgData_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(v_msgData_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
return v_res_90_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_91_; double v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_float_of_nat(v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(lean_object* v_cls_96_, lean_object* v_msg_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_ref_103_; lean_object* v___x_104_; lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_149_; 
v_ref_103_ = lean_ctor_get(v___y_100_, 5);
v___x_104_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(v_msg_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_149_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_149_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_149_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v_traceState_110_; lean_object* v_env_111_; lean_object* v_nextMacroScope_112_; lean_object* v_ngen_113_; lean_object* v_auxDeclNGen_114_; lean_object* v_cache_115_; lean_object* v_messages_116_; lean_object* v_infoState_117_; lean_object* v_snapshotTasks_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_148_; 
v___x_109_ = lean_st_ref_take(v___y_101_);
v_traceState_110_ = lean_ctor_get(v___x_109_, 4);
v_env_111_ = lean_ctor_get(v___x_109_, 0);
v_nextMacroScope_112_ = lean_ctor_get(v___x_109_, 1);
v_ngen_113_ = lean_ctor_get(v___x_109_, 2);
v_auxDeclNGen_114_ = lean_ctor_get(v___x_109_, 3);
v_cache_115_ = lean_ctor_get(v___x_109_, 5);
v_messages_116_ = lean_ctor_get(v___x_109_, 6);
v_infoState_117_ = lean_ctor_get(v___x_109_, 7);
v_snapshotTasks_118_ = lean_ctor_get(v___x_109_, 8);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_148_ == 0)
{
v___x_120_ = v___x_109_;
v_isShared_121_ = v_isSharedCheck_148_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_snapshotTasks_118_);
lean_inc(v_infoState_117_);
lean_inc(v_messages_116_);
lean_inc(v_cache_115_);
lean_inc(v_traceState_110_);
lean_inc(v_auxDeclNGen_114_);
lean_inc(v_ngen_113_);
lean_inc(v_nextMacroScope_112_);
lean_inc(v_env_111_);
lean_dec(v___x_109_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_148_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
uint64_t v_tid_122_; lean_object* v_traces_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_147_; 
v_tid_122_ = lean_ctor_get_uint64(v_traceState_110_, sizeof(void*)*1);
v_traces_123_ = lean_ctor_get(v_traceState_110_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_traceState_110_);
if (v_isSharedCheck_147_ == 0)
{
v___x_125_ = v_traceState_110_;
v_isShared_126_ = v_isSharedCheck_147_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_traces_123_);
lean_dec(v_traceState_110_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_147_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; double v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_127_ = lean_box(0);
v___x_128_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0);
v___x_129_ = 0;
v___x_130_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__1));
v___x_131_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_131_, 0, v_cls_96_);
lean_ctor_set(v___x_131_, 1, v___x_127_);
lean_ctor_set(v___x_131_, 2, v___x_130_);
lean_ctor_set_float(v___x_131_, sizeof(void*)*3, v___x_128_);
lean_ctor_set_float(v___x_131_, sizeof(void*)*3 + 8, v___x_128_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*3 + 16, v___x_129_);
v___x_132_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__2));
v___x_133_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v_a_105_);
lean_ctor_set(v___x_133_, 2, v___x_132_);
lean_inc(v_ref_103_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_ref_103_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = l_Lean_PersistentArray_push___redArg(v_traces_123_, v___x_134_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_135_);
v___x_137_ = v___x_125_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_135_);
lean_ctor_set_uint64(v_reuseFailAlloc_146_, sizeof(void*)*1, v_tid_122_);
v___x_137_ = v_reuseFailAlloc_146_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_139_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 4, v___x_137_);
v___x_139_ = v___x_120_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_env_111_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_nextMacroScope_112_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v_ngen_113_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v_auxDeclNGen_114_);
lean_ctor_set(v_reuseFailAlloc_145_, 4, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_145_, 5, v_cache_115_);
lean_ctor_set(v_reuseFailAlloc_145_, 6, v_messages_116_);
lean_ctor_set(v_reuseFailAlloc_145_, 7, v_infoState_117_);
lean_ctor_set(v_reuseFailAlloc_145_, 8, v_snapshotTasks_118_);
v___x_139_ = v_reuseFailAlloc_145_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_140_ = lean_st_ref_set(v___y_101_, v___x_139_);
v___x_141_ = lean_box(0);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_141_);
v___x_143_ = v___x_107_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___boxed(lean_object* v_cls_150_, lean_object* v_msg_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v_cls_150_, v_msg_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_unsigned_to_nat(32u);
v___x_159_ = lean_mk_empty_array_with_capacity(v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1(void){
_start:
{
size_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_161_ = ((size_t)5ULL);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_unsigned_to_nat(32u);
v___x_164_ = lean_mk_empty_array_with_capacity(v___x_163_);
v___x_165_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0);
v___x_166_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
lean_ctor_set(v___x_166_, 2, v___x_162_);
lean_ctor_set(v___x_166_, 3, v___x_162_);
lean_ctor_set_usize(v___x_166_, 4, v___x_161_);
return v___x_166_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4(void){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0(lean_box(0));
return v___x_170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6));
v___x_174_ = l_Lean_stringToMessageData(v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10));
v___x_179_ = l_Lean_stringToMessageData(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27));
v___x_215_ = l_Lean_stringToMessageData(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(lean_object* v_type_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v_val_484_; lean_object* v___x_547_; 
v___x_547_ = l_Lean_leCarrierIsSort(v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; uint8_t v___x_549_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_547_, 1);
v___x_549_ = lean_unbox(v_a_548_);
lean_dec(v_a_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
lean_inc_ref(v_type_216_);
v___x_550_ = l_Lean_Meta_getDecLevel(v_type_216_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v_val_484_ = v_a_551_;
goto v___jp_483_;
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec_ref(v_type_216_);
v_a_552_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_550_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_object* v___x_560_; 
lean_inc_ref(v_type_216_);
v___x_560_ = l_Lean_Meta_getDecLevel_x3f(v_type_216_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_570_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_570_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
if (lean_obj_tag(v_a_561_) == 1)
{
lean_object* v_val_565_; 
lean_del_object(v___x_563_);
v_val_565_ = lean_ctor_get(v_a_561_, 0);
lean_inc(v_val_565_);
lean_dec_ref_known(v_a_561_, 1);
v_val_484_ = v_val_565_;
goto v___jp_483_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_568_; 
lean_dec(v_a_561_);
lean_dec_ref(v_type_216_);
v___x_566_ = lean_box(0);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_566_);
v___x_568_ = v___x_563_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v_type_216_);
v_a_571_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_560_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_560_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v_type_216_);
v_a_579_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_547_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_547_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
v___jp_228_:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v_rings_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___f_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v_rings_242_ = lean_ctor_get(v_a_241_, 0);
lean_inc_ref(v_rings_242_);
lean_dec(v_a_241_);
v___x_243_ = lean_box(0);
v___x_244_ = lean_array_get_size(v_rings_242_);
lean_dec_ref(v_rings_242_);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1);
v___x_247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3);
v___x_248_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_248_, 0, v___x_244_);
lean_ctor_set(v___x_248_, 1, v_type_216_);
lean_ctor_set(v___x_248_, 2, v___y_233_);
lean_ctor_set(v___x_248_, 3, v___y_235_);
lean_ctor_set(v___x_248_, 4, v___y_237_);
lean_ctor_set(v___x_248_, 5, v___y_234_);
lean_ctor_set(v___x_248_, 6, v___x_243_);
lean_ctor_set(v___x_248_, 7, v___x_243_);
lean_ctor_set(v___x_248_, 8, v___x_243_);
lean_ctor_set(v___x_248_, 9, v___x_243_);
lean_ctor_set(v___x_248_, 10, v___x_243_);
lean_ctor_set(v___x_248_, 11, v___x_243_);
lean_ctor_set(v___x_248_, 12, v___x_243_);
lean_ctor_set(v___x_248_, 13, v___x_243_);
lean_ctor_set(v___x_248_, 14, v___x_246_);
lean_ctor_set(v___x_248_, 15, v___x_247_);
lean_ctor_set(v___x_248_, 16, v___x_247_);
v___x_249_ = lean_box(1);
v___x_250_ = lean_box(0);
v___x_251_ = 0;
v___x_252_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4);
v___x_253_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v___x_253_, 0, v___x_248_);
lean_ctor_set(v___x_253_, 1, v___x_243_);
lean_ctor_set(v___x_253_, 2, v___x_243_);
lean_ctor_set(v___x_253_, 3, v___y_231_);
lean_ctor_set(v___x_253_, 4, v___y_229_);
lean_ctor_set(v___x_253_, 5, v___y_236_);
lean_ctor_set(v___x_253_, 6, v___y_232_);
lean_ctor_set(v___x_253_, 7, v___y_230_);
lean_ctor_set(v___x_253_, 8, v___x_246_);
lean_ctor_set(v___x_253_, 9, v___x_245_);
lean_ctor_set(v___x_253_, 10, v___x_245_);
lean_ctor_set(v___x_253_, 11, v___x_249_);
lean_ctor_set(v___x_253_, 12, v___x_250_);
lean_ctor_set(v___x_253_, 13, v___x_246_);
lean_ctor_set(v___x_253_, 14, v___x_252_);
lean_ctor_set(v___x_253_, 15, v___x_245_);
lean_ctor_set(v___x_253_, 16, v___x_243_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*17, v___x_251_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*17 + 1, v___x_251_);
v___f_254_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0), 2, 1);
lean_closure_set(v___f_254_, 0, v___x_253_);
v___x_255_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_256_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_255_, v___f_254_, v___y_238_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_264_; 
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; 
v_unused_265_ = lean_ctor_get(v___x_256_, 0);
lean_dec(v_unused_265_);
v___x_258_ = v___x_256_;
v_isShared_259_ = v_isSharedCheck_264_;
goto v_resetjp_257_;
}
else
{
lean_dec(v___x_256_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_264_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_244_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_260_);
v___x_262_ = v___x_258_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_a_266_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_256_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_256_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec_ref(v_type_216_);
v_a_274_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_240_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_240_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
v___jp_282_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
lean_inc_ref(v___y_304_);
v___x_305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_305_, 0, v___y_304_);
v___x_306_ = l_Lean_MessageData_ofFormat(v___x_305_);
lean_inc_ref(v___y_290_);
v___x_307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_307_, 0, v___y_290_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___y_288_, v___x_307_, v___y_299_, v___y_284_, v___y_297_, v___y_303_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_dec_ref_known(v___x_308_, 1);
v___y_229_ = v___y_283_;
v___y_230_ = v___y_296_;
v___y_231_ = v___y_295_;
v___y_232_ = v___y_286_;
v___y_233_ = v___y_298_;
v___y_234_ = v___y_302_;
v___y_235_ = v___y_301_;
v___y_236_ = v___y_293_;
v___y_237_ = v___y_294_;
v___y_238_ = v___y_285_;
v___y_239_ = v___y_297_;
goto v___jp_228_;
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_298_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_283_);
lean_dec_ref(v_type_216_);
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
v___jp_317_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5));
lean_inc_ref(v___y_323_);
lean_inc_ref(v___y_326_);
v___x_340_ = l_Lean_Name_mkStr3(v___y_326_, v___y_323_, v___x_339_);
v___x_341_ = l_Lean_mkConst(v___x_340_, v___y_321_);
lean_inc_ref(v_type_216_);
v___x_342_ = l_Lean_Expr_app___override(v___x_341_, v_type_216_);
v___x_343_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_342_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_345_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
lean_inc_ref(v_type_216_);
lean_inc(v___y_320_);
v___x_345_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(v___y_320_, v_type_216_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_options_346_; uint8_t v_hasTrace_347_; 
v_options_346_ = lean_ctor_get(v___y_337_, 2);
v_hasTrace_347_ = lean_ctor_get_uint8(v_options_346_, sizeof(void*)*1);
if (v_hasTrace_347_ == 0)
{
lean_object* v_a_348_; 
lean_dec(v___y_322_);
v_a_348_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_345_, 1);
v___y_229_ = v___y_318_;
v___y_230_ = v_a_348_;
v___y_231_ = v___y_319_;
v___y_232_ = v_a_344_;
v___y_233_ = v___y_320_;
v___y_234_ = v___y_325_;
v___y_235_ = v___y_324_;
v___y_236_ = v___y_327_;
v___y_237_ = v___y_328_;
v___y_238_ = v___y_329_;
v___y_239_ = v___y_337_;
goto v___jp_228_;
}
else
{
lean_object* v_a_349_; lean_object* v_inheritedTraceOptions_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v_a_349_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_345_, 1);
v_inheritedTraceOptions_350_ = lean_ctor_get(v___y_337_, 13);
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___closed__1));
lean_inc(v___y_322_);
v___x_352_ = l_Lean_Name_append(v___x_351_, v___y_322_);
v___x_353_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_350_, v_options_346_, v___x_352_);
lean_dec(v___x_352_);
if (v___x_353_ == 0)
{
lean_dec(v___y_322_);
v___y_229_ = v___y_318_;
v___y_230_ = v_a_349_;
v___y_231_ = v___y_319_;
v___y_232_ = v_a_344_;
v___y_233_ = v___y_320_;
v___y_234_ = v___y_325_;
v___y_235_ = v___y_324_;
v___y_236_ = v___y_327_;
v___y_237_ = v___y_328_;
v___y_238_ = v___y_329_;
v___y_239_ = v___y_337_;
goto v___jp_228_;
}
else
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_Meta_Grind_updateLastTag(v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v___x_355_; 
lean_dec_ref_known(v___x_354_, 1);
v___x_355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7);
if (lean_obj_tag(v_a_349_) == 0)
{
lean_object* v___x_356_; 
v___x_356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8));
v___y_283_ = v___y_318_;
v___y_284_ = v___y_336_;
v___y_285_ = v___y_329_;
v___y_286_ = v_a_344_;
v___y_287_ = v___y_334_;
v___y_288_ = v___y_322_;
v___y_289_ = v___y_331_;
v___y_290_ = v___x_355_;
v___y_291_ = v___y_333_;
v___y_292_ = v___y_332_;
v___y_293_ = v___y_327_;
v___y_294_ = v___y_328_;
v___y_295_ = v___y_319_;
v___y_296_ = v_a_349_;
v___y_297_ = v___y_337_;
v___y_298_ = v___y_320_;
v___y_299_ = v___y_335_;
v___y_300_ = v___y_330_;
v___y_301_ = v___y_324_;
v___y_302_ = v___y_325_;
v___y_303_ = v___y_338_;
v___y_304_ = v___x_356_;
goto v___jp_282_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9));
v___y_283_ = v___y_318_;
v___y_284_ = v___y_336_;
v___y_285_ = v___y_329_;
v___y_286_ = v_a_344_;
v___y_287_ = v___y_334_;
v___y_288_ = v___y_322_;
v___y_289_ = v___y_331_;
v___y_290_ = v___x_355_;
v___y_291_ = v___y_333_;
v___y_292_ = v___y_332_;
v___y_293_ = v___y_327_;
v___y_294_ = v___y_328_;
v___y_295_ = v___y_319_;
v___y_296_ = v_a_349_;
v___y_297_ = v___y_337_;
v___y_298_ = v___y_320_;
v___y_299_ = v___y_335_;
v___y_300_ = v___y_330_;
v___y_301_ = v___y_324_;
v___y_302_ = v___y_325_;
v___y_303_ = v___y_338_;
v___y_304_ = v___x_357_;
goto v___jp_282_;
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_a_349_);
lean_dec(v_a_344_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_322_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec_ref(v_type_216_);
v_a_358_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_354_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_354_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec(v_a_344_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_322_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec_ref(v_type_216_);
v_a_366_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_345_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_345_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_322_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec_ref(v_type_216_);
v_a_374_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_343_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_343_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
v___jp_382_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_inc_ref(v___y_405_);
v___x_406_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_406_, 0, v___y_405_);
v___x_407_ = l_Lean_MessageData_ofFormat(v___x_406_);
lean_inc_ref(v___y_393_);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___y_393_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
lean_inc(v___y_387_);
v___x_409_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___y_387_, v___x_408_, v___y_388_, v___y_398_, v___y_392_, v___y_404_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_dec_ref_known(v___x_409_, 1);
v___y_318_ = v___y_383_;
v___y_319_ = v___y_394_;
v___y_320_ = v___y_396_;
v___y_321_ = v___y_395_;
v___y_322_ = v___y_387_;
v___y_323_ = v___y_397_;
v___y_324_ = v___y_401_;
v___y_325_ = v___y_400_;
v___y_326_ = v___y_399_;
v___y_327_ = v___y_389_;
v___y_328_ = v___y_390_;
v___y_329_ = v___y_386_;
v___y_330_ = v___y_402_;
v___y_331_ = v___y_385_;
v___y_332_ = v___y_403_;
v___y_333_ = v___y_391_;
v___y_334_ = v___y_384_;
v___y_335_ = v___y_388_;
v___y_336_ = v___y_398_;
v___y_337_ = v___y_392_;
v___y_338_ = v___y_404_;
goto v___jp_317_;
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_383_);
lean_dec_ref(v_type_216_);
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
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
v___jp_418_:
{
lean_object* v___x_439_; 
lean_inc_ref(v___y_428_);
lean_inc_ref(v_type_216_);
lean_inc(v___y_422_);
v___x_439_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v___y_422_, v_type_216_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
lean_inc_ref(v_type_216_);
lean_inc(v___y_422_);
v___x_441_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v___y_422_, v_type_216_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v_inheritedTraceOptions_443_; lean_object* v___x_444_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v_inheritedTraceOptions_443_ = lean_ctor_get(v___y_437_, 13);
lean_inc_ref(v___y_424_);
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc(v___y_429_);
lean_inc_ref(v_inheritedTraceOptions_443_);
v___x_444_ = lean_apply_12(v___y_424_, v_inheritedTraceOptions_443_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, lean_box(0));
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; uint8_t v___x_446_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
v___x_446_ = lean_unbox(v_a_445_);
lean_dec(v_a_445_);
if (v___x_446_ == 0)
{
v___y_318_ = v___y_419_;
v___y_319_ = v___y_420_;
v___y_320_ = v___y_422_;
v___y_321_ = v___y_421_;
v___y_322_ = v___y_423_;
v___y_323_ = v___y_425_;
v___y_324_ = v___y_427_;
v___y_325_ = v_a_440_;
v___y_326_ = v___y_426_;
v___y_327_ = v_a_442_;
v___y_328_ = v___y_428_;
v___y_329_ = v___y_429_;
v___y_330_ = v___y_430_;
v___y_331_ = v___y_431_;
v___y_332_ = v___y_432_;
v___y_333_ = v___y_433_;
v___y_334_ = v___y_434_;
v___y_335_ = v___y_435_;
v___y_336_ = v___y_436_;
v___y_337_ = v___y_437_;
v___y_338_ = v___y_438_;
goto v___jp_317_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_Grind_updateLastTag(v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; 
lean_dec_ref_known(v___x_447_, 1);
v___x_448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11);
if (lean_obj_tag(v_a_442_) == 0)
{
lean_object* v___x_449_; 
v___x_449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8));
v___y_383_ = v___y_419_;
v___y_384_ = v___y_434_;
v___y_385_ = v___y_431_;
v___y_386_ = v___y_429_;
v___y_387_ = v___y_423_;
v___y_388_ = v___y_435_;
v___y_389_ = v_a_442_;
v___y_390_ = v___y_428_;
v___y_391_ = v___y_433_;
v___y_392_ = v___y_437_;
v___y_393_ = v___x_448_;
v___y_394_ = v___y_420_;
v___y_395_ = v___y_421_;
v___y_396_ = v___y_422_;
v___y_397_ = v___y_425_;
v___y_398_ = v___y_436_;
v___y_399_ = v___y_426_;
v___y_400_ = v_a_440_;
v___y_401_ = v___y_427_;
v___y_402_ = v___y_430_;
v___y_403_ = v___y_432_;
v___y_404_ = v___y_438_;
v___y_405_ = v___x_449_;
goto v___jp_382_;
}
else
{
lean_object* v___x_450_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9));
v___y_383_ = v___y_419_;
v___y_384_ = v___y_434_;
v___y_385_ = v___y_431_;
v___y_386_ = v___y_429_;
v___y_387_ = v___y_423_;
v___y_388_ = v___y_435_;
v___y_389_ = v_a_442_;
v___y_390_ = v___y_428_;
v___y_391_ = v___y_433_;
v___y_392_ = v___y_437_;
v___y_393_ = v___x_448_;
v___y_394_ = v___y_420_;
v___y_395_ = v___y_421_;
v___y_396_ = v___y_422_;
v___y_397_ = v___y_425_;
v___y_398_ = v___y_436_;
v___y_399_ = v___y_426_;
v___y_400_ = v_a_440_;
v___y_401_ = v___y_427_;
v___y_402_ = v___y_430_;
v___y_403_ = v___y_432_;
v___y_404_ = v___y_438_;
v___y_405_ = v___x_450_;
goto v___jp_382_;
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_a_442_);
lean_dec(v_a_440_);
lean_dec_ref(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_423_);
lean_dec(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec_ref(v_type_216_);
v_a_451_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_447_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_447_);
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
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_a_442_);
lean_dec(v_a_440_);
lean_dec_ref(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_423_);
lean_dec(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec_ref(v_type_216_);
v_a_459_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_444_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_444_);
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
lean_dec(v_a_440_);
lean_dec_ref(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_423_);
lean_dec(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec_ref(v_type_216_);
v_a_467_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_441_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_441_);
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
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_423_);
lean_dec(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec_ref(v_type_216_);
v_a_475_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_439_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_439_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
v___jp_483_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12));
v___x_486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13));
v___x_487_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15));
v___x_488_ = lean_box(0);
lean_inc(v_val_484_);
v___x_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_489_, 0, v_val_484_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
lean_inc_ref(v___x_489_);
v___x_490_ = l_Lean_mkConst(v___x_487_, v___x_489_);
lean_inc_ref(v_type_216_);
v___x_491_ = l_Lean_Expr_app___override(v___x_490_, v_type_216_);
v___x_492_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_491_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_538_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_538_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_538_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_538_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
if (lean_obj_tag(v_a_493_) == 1)
{
lean_object* v_val_497_; lean_object* v_inheritedTraceOptions_498_; lean_object* v___x_499_; lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v_a_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
lean_del_object(v___x_495_);
v_val_497_ = lean_ctor_get(v_a_493_, 0);
lean_inc_n(v_val_497_, 2);
lean_dec_ref_known(v_a_493_, 1);
v_inheritedTraceOptions_498_ = lean_ctor_get(v_a_225_, 13);
v___x_499_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18));
v___f_500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19));
v___x_501_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(v___x_499_, v_inheritedTraceOptions_498_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref(v___x_501_);
v___x_503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21));
lean_inc_ref_n(v___x_489_, 3);
v___x_504_ = l_Lean_mkConst(v___x_503_, v___x_489_);
lean_inc_ref_n(v_type_216_, 3);
v___x_505_ = l_Lean_mkAppB(v___x_504_, v_type_216_, v_val_497_);
v___x_506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24));
v___x_507_ = l_Lean_mkConst(v___x_506_, v___x_489_);
lean_inc_ref(v___x_505_);
v___x_508_ = l_Lean_mkAppB(v___x_507_, v_type_216_, v___x_505_);
v___x_509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26));
v___x_510_ = l_Lean_mkConst(v___x_509_, v___x_489_);
lean_inc_ref(v___x_508_);
v___x_511_ = l_Lean_mkAppB(v___x_510_, v_type_216_, v___x_508_);
v___x_512_ = lean_unbox(v_a_502_);
lean_dec(v_a_502_);
if (v___x_512_ == 0)
{
v___y_419_ = v_val_497_;
v___y_420_ = v___x_511_;
v___y_421_ = v___x_489_;
v___y_422_ = v_val_484_;
v___y_423_ = v___x_499_;
v___y_424_ = v___f_500_;
v___y_425_ = v___x_486_;
v___y_426_ = v___x_485_;
v___y_427_ = v___x_505_;
v___y_428_ = v___x_508_;
v___y_429_ = v_a_217_;
v___y_430_ = v_a_218_;
v___y_431_ = v_a_219_;
v___y_432_ = v_a_220_;
v___y_433_ = v_a_221_;
v___y_434_ = v_a_222_;
v___y_435_ = v_a_223_;
v___y_436_ = v_a_224_;
v___y_437_ = v_a_225_;
v___y_438_ = v_a_226_;
goto v___jp_418_;
}
else
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Meta_Grind_updateLastTag(v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec_ref_known(v___x_513_, 1);
v___x_514_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28);
lean_inc_ref(v_type_216_);
v___x_515_ = l_Lean_MessageData_ofExpr(v_type_216_);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_499_, v___x_516_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_dec_ref_known(v___x_517_, 1);
v___y_419_ = v_val_497_;
v___y_420_ = v___x_511_;
v___y_421_ = v___x_489_;
v___y_422_ = v_val_484_;
v___y_423_ = v___x_499_;
v___y_424_ = v___f_500_;
v___y_425_ = v___x_486_;
v___y_426_ = v___x_485_;
v___y_427_ = v___x_505_;
v___y_428_ = v___x_508_;
v___y_429_ = v_a_217_;
v___y_430_ = v_a_218_;
v___y_431_ = v_a_219_;
v___y_432_ = v_a_220_;
v___y_433_ = v_a_221_;
v___y_434_ = v_a_222_;
v___y_435_ = v_a_223_;
v___y_436_ = v_a_224_;
v___y_437_ = v_a_225_;
v___y_438_ = v_a_226_;
goto v___jp_418_;
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v___x_511_);
lean_dec_ref(v___x_508_);
lean_dec_ref(v___x_505_);
lean_dec(v_val_497_);
lean_dec_ref_known(v___x_489_, 2);
lean_dec(v_val_484_);
lean_dec_ref(v_type_216_);
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref(v___x_511_);
lean_dec_ref(v___x_508_);
lean_dec_ref(v___x_505_);
lean_dec(v_val_497_);
lean_dec_ref_known(v___x_489_, 2);
lean_dec(v_val_484_);
lean_dec_ref(v_type_216_);
v_a_526_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_513_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_513_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
else
{
lean_object* v___x_534_; lean_object* v___x_536_; 
lean_dec(v_a_493_);
lean_dec_ref_known(v___x_489_, 2);
lean_dec(v_val_484_);
lean_dec_ref(v_type_216_);
v___x_534_ = lean_box(0);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_534_);
v___x_536_ = v___x_495_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec_ref_known(v___x_489_, 2);
lean_dec(v_val_484_);
lean_dec_ref(v_type_216_);
v_a_539_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_492_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_492_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___boxed(lean_object* v_type_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec(v_a_588_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1(lean_object* v_cls_600_, lean_object* v_msg_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v_cls_600_, v_msg_601_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___boxed(lean_object* v_cls_614_, lean_object* v_msg_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1(v_cls_614_, v_msg_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec(v___y_616_);
return v_res_627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = l_Lean_Level_ofNat(v___x_714_);
return v___x_715_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18));
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___closed__1));
v___x_742_ = l_Lean_Name_append(v___x_741_, v___x_740_);
return v___x_742_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49));
v___x_745_ = l_Lean_stringToMessageData(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f(lean_object* v_type_769_, lean_object* v_base_770_, lean_object* v_semiringInst_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v___x_783_; uint8_t v___x_784_; 
lean_inc_ref(v_semiringInst_771_);
v___x_783_ = l_Lean_Expr_cleanupAnnotations(v_semiringInst_771_);
v___x_784_ = l_Lean_Expr_isApp(v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec_ref(v___x_783_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
v___x_785_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_769_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
return v___x_785_;
}
else
{
lean_object* v_arg_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_arg_786_ = lean_ctor_get(v___x_783_, 1);
lean_inc_ref(v_arg_786_);
v___x_787_ = l_Lean_Expr_appFnCleanup___redArg(v___x_783_);
v___x_788_ = l_Lean_Expr_isApp(v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
lean_dec_ref(v___x_787_);
lean_dec_ref(v_arg_786_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
v___x_789_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_769_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
return v___x_789_;
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_790_ = l_Lean_Expr_appFnCleanup___redArg(v___x_787_);
v___x_791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1));
v___x_792_ = l_Lean_Expr_isConstOf(v___x_790_, v___x_791_);
lean_dec_ref(v___x_790_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
lean_dec_ref(v_arg_786_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
v___x_793_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_769_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
return v___x_793_;
}
else
{
lean_object* v___x_794_; 
lean_inc_ref(v_base_770_);
v___x_794_ = l_Lean_Meta_getDecLevel_x3f(v_base_770_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_1295_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_1295_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_1295_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
if (lean_obj_tag(v_a_795_) == 1)
{
lean_object* v_val_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_797_);
v_val_799_ = lean_ctor_get(v_a_795_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_a_795_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_801_ = v_a_795_;
v_isShared_802_ = v_isSharedCheck_1290_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_val_799_);
lean_dec(v_a_795_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_1290_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4));
v___x_804_ = lean_box(0);
lean_inc(v_val_799_);
v___x_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_805_, 0, v_val_799_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
lean_inc_ref_n(v___x_805_, 5);
v___x_806_ = l_Lean_mkConst(v___x_803_, v___x_805_);
lean_inc_ref(v_base_770_);
v___x_807_ = l_Lean_mkAppB(v___x_806_, v_base_770_, v_arg_786_);
v___x_808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21));
v___x_809_ = l_Lean_mkConst(v___x_808_, v___x_805_);
lean_inc_ref_n(v___x_807_, 2);
lean_inc_ref_n(v_type_769_, 4);
v___x_810_ = l_Lean_mkAppB(v___x_809_, v_type_769_, v___x_807_);
v___x_811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24));
v___x_812_ = l_Lean_mkConst(v___x_811_, v___x_805_);
lean_inc_ref(v___x_810_);
v___x_813_ = l_Lean_mkAppB(v___x_812_, v_type_769_, v___x_810_);
v___x_814_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26));
v___x_815_ = l_Lean_mkConst(v___x_814_, v___x_805_);
lean_inc_ref(v___x_813_);
v___x_816_ = l_Lean_mkAppB(v___x_815_, v_type_769_, v___x_813_);
v___x_817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15));
v___x_818_ = l_Lean_mkConst(v___x_817_, v___x_805_);
v___x_819_ = l_Lean_Expr_app___override(v___x_818_, v_type_769_);
v___x_820_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_819_, v___x_807_, v_a_777_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec_ref_known(v___x_820_, 1);
v___x_821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5));
lean_inc_ref(v___x_805_);
v___x_822_ = l_Lean_mkConst(v___x_821_, v___x_805_);
lean_inc_ref(v_type_769_);
v___x_823_ = l_Lean_Expr_app___override(v___x_822_, v_type_769_);
lean_inc_ref(v___x_810_);
v___x_824_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_823_, v___x_810_, v_a_777_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec_ref_known(v___x_824_, 1);
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7));
lean_inc_ref(v___x_805_);
v___x_826_ = l_Lean_mkConst(v___x_825_, v___x_805_);
lean_inc_ref(v_type_769_);
v___x_827_ = l_Lean_Expr_app___override(v___x_826_, v_type_769_);
lean_inc_ref(v___x_813_);
v___x_828_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_827_, v___x_813_, v_a_777_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec_ref_known(v___x_828_, 1);
v___x_829_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8));
lean_inc_ref(v___x_805_);
v___x_830_ = l_Lean_mkConst(v___x_829_, v___x_805_);
lean_inc_ref(v_type_769_);
v___x_831_ = l_Lean_Expr_app___override(v___x_830_, v_type_769_);
lean_inc_ref(v___x_816_);
v___x_832_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_831_, v___x_816_, v_a_777_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec_ref_known(v___x_832_, 1);
v___x_833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10));
lean_inc_ref_n(v___x_805_, 2);
v___x_834_ = l_Lean_mkConst(v___x_833_, v___x_805_);
lean_inc_ref_n(v_type_769_, 2);
v___x_835_ = l_Lean_Expr_app___override(v___x_834_, v_type_769_);
v___x_836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12));
v___x_837_ = l_Lean_mkConst(v___x_836_, v___x_805_);
lean_inc_ref(v___x_813_);
v___x_838_ = l_Lean_mkAppB(v___x_837_, v_type_769_, v___x_813_);
v___x_839_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_835_, v___x_838_, v_a_777_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref_known(v___x_839_, 1);
v___x_840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__14));
lean_inc_ref_n(v___x_805_, 3);
lean_inc_n(v_val_799_, 2);
v___x_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_841_, 0, v_val_799_);
lean_ctor_set(v___x_841_, 1, v___x_805_);
v___x_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_842_, 0, v_val_799_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
lean_inc_ref(v___x_842_);
v___x_843_ = l_Lean_mkConst(v___x_840_, v___x_842_);
lean_inc_ref_n(v_type_769_, 5);
v___x_844_ = l_Lean_mkApp3(v___x_843_, v_type_769_, v_type_769_, v_type_769_);
v___x_845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__16));
v___x_846_ = l_Lean_mkConst(v___x_845_, v___x_805_);
v___x_847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18));
v___x_848_ = l_Lean_mkConst(v___x_847_, v___x_805_);
lean_inc_ref(v___x_813_);
v___x_849_ = l_Lean_mkAppB(v___x_848_, v_type_769_, v___x_813_);
v___x_850_ = l_Lean_mkAppB(v___x_846_, v_type_769_, v___x_849_);
v___x_851_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_844_, v___x_850_, v_a_777_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec_ref_known(v___x_851_, 1);
v___x_852_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__20));
lean_inc_ref(v___x_842_);
v___x_853_ = l_Lean_mkConst(v___x_852_, v___x_842_);
lean_inc_ref_n(v_type_769_, 5);
v___x_854_ = l_Lean_mkApp3(v___x_853_, v_type_769_, v_type_769_, v_type_769_);
v___x_855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__22));
lean_inc_ref_n(v___x_805_, 2);
v___x_856_ = l_Lean_mkConst(v___x_855_, v___x_805_);
v___x_857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24));
v___x_858_ = l_Lean_mkConst(v___x_857_, v___x_805_);
lean_inc_ref(v___x_813_);
v___x_859_ = l_Lean_mkAppB(v___x_858_, v_type_769_, v___x_813_);
v___x_860_ = l_Lean_mkAppB(v___x_856_, v_type_769_, v___x_859_);
v___x_861_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_854_, v___x_860_, v_a_777_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec_ref_known(v___x_861_, 1);
v___x_862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__26));
v___x_863_ = l_Lean_mkConst(v___x_862_, v___x_842_);
lean_inc_ref_n(v_type_769_, 5);
v___x_864_ = l_Lean_mkApp3(v___x_863_, v_type_769_, v_type_769_, v_type_769_);
v___x_865_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__28));
lean_inc_ref_n(v___x_805_, 2);
v___x_866_ = l_Lean_mkConst(v___x_865_, v___x_805_);
v___x_867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30));
v___x_868_ = l_Lean_mkConst(v___x_867_, v___x_805_);
lean_inc_ref(v___x_810_);
v___x_869_ = l_Lean_mkAppB(v___x_868_, v_type_769_, v___x_810_);
v___x_870_ = l_Lean_mkAppB(v___x_866_, v_type_769_, v___x_869_);
v___x_871_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_864_, v___x_870_, v_a_777_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec_ref_known(v___x_871_, 1);
v___x_872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__32));
lean_inc_ref_n(v___x_805_, 2);
v___x_873_ = l_Lean_mkConst(v___x_872_, v___x_805_);
lean_inc_ref_n(v_type_769_, 2);
v___x_874_ = l_Lean_Expr_app___override(v___x_873_, v_type_769_);
v___x_875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34));
v___x_876_ = l_Lean_mkConst(v___x_875_, v___x_805_);
lean_inc_ref(v___x_810_);
v___x_877_ = l_Lean_mkAppB(v___x_876_, v_type_769_, v___x_810_);
v___x_878_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_874_, v___x_877_, v_a_777_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec_ref_known(v___x_878_, 1);
v___x_879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__36));
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37);
lean_inc_ref_n(v___x_805_, 2);
v___x_929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_805_);
lean_inc(v_val_799_);
v___x_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_930_, 0, v_val_799_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l_Lean_mkConst(v___x_879_, v___x_930_);
v___x_932_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_769_, 3);
v___x_933_ = l_Lean_mkApp3(v___x_931_, v_type_769_, v___x_932_, v_type_769_);
v___x_934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39));
v___x_935_ = l_Lean_mkConst(v___x_934_, v___x_805_);
lean_inc_ref(v___x_813_);
v___x_936_ = l_Lean_mkAppB(v___x_935_, v_type_769_, v___x_813_);
v___x_937_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_933_, v___x_936_, v_a_777_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec_ref_known(v___x_937_, 1);
v___x_938_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__41));
lean_inc_ref_n(v___x_805_, 2);
v___x_939_ = l_Lean_mkConst(v___x_938_, v___x_805_);
lean_inc_ref_n(v_type_769_, 2);
v___x_940_ = l_Lean_Expr_app___override(v___x_939_, v_type_769_);
v___x_941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43));
v___x_942_ = l_Lean_mkConst(v___x_941_, v___x_805_);
lean_inc_ref(v___x_813_);
v___x_943_ = l_Lean_mkAppB(v___x_942_, v_type_769_, v___x_813_);
v___x_944_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_940_, v___x_943_, v_a_777_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec_ref_known(v___x_944_, 1);
v___x_945_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__45));
lean_inc_ref_n(v___x_805_, 2);
v___x_946_ = l_Lean_mkConst(v___x_945_, v___x_805_);
lean_inc_ref_n(v_type_769_, 2);
v___x_947_ = l_Lean_Expr_app___override(v___x_946_, v_type_769_);
v___x_948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47));
v___x_949_ = l_Lean_mkConst(v___x_948_, v___x_805_);
lean_inc_ref(v___x_810_);
v___x_950_ = l_Lean_mkAppB(v___x_949_, v_type_769_, v___x_810_);
v___x_951_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_947_, v___x_950_, v_a_777_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_inheritedTraceOptions_952_; lean_object* v___x_953_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v_options_966_; lean_object* v_inheritedTraceOptions_967_; lean_object* v___y_968_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1021_; lean_object* v_noZeroDivInst_x3f_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v_val_1051_; lean_object* v_charInst_x3f_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___x_1170_; lean_object* v_a_1171_; uint8_t v___x_1172_; 
lean_dec_ref_known(v___x_951_, 1);
v_inheritedTraceOptions_952_ = lean_ctor_get(v_a_780_, 13);
v___x_953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18));
v___x_1170_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(v___x_953_, v_inheritedTraceOptions_952_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref(v___x_1170_);
v___x_1172_ = lean_unbox(v_a_1171_);
lean_dec(v_a_1171_);
if (v___x_1172_ == 0)
{
v___y_1098_ = v_a_772_;
v___y_1099_ = v_a_773_;
v___y_1100_ = v_a_774_;
v___y_1101_ = v_a_775_;
v___y_1102_ = v_a_776_;
v___y_1103_ = v_a_777_;
v___y_1104_ = v_a_778_;
v___y_1105_ = v_a_779_;
v___y_1106_ = v_a_780_;
v___y_1107_ = v_a_781_;
goto v___jp_1097_;
}
else
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_Meta_Grind_updateLastTag(v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_dec_ref_known(v___x_1173_, 1);
v___x_1174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28);
lean_inc_ref(v_type_769_);
v___x_1175_ = l_Lean_MessageData_ofExpr(v_type_769_);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_953_, v___x_1176_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_dec_ref_known(v___x_1177_, 1);
v___y_1098_ = v_a_772_;
v___y_1099_ = v_a_773_;
v___y_1100_ = v_a_774_;
v___y_1101_ = v_a_775_;
v___y_1102_ = v_a_776_;
v___y_1103_ = v_a_777_;
v___y_1104_ = v_a_778_;
v___y_1105_ = v_a_779_;
v___y_1106_ = v_a_780_;
v___y_1107_ = v_a_781_;
goto v___jp_1097_;
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1186_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1173_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1173_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
v___jp_954_:
{
uint8_t v_hasTrace_969_; 
v_hasTrace_969_ = lean_ctor_get_uint8(v_options_966_, sizeof(void*)*1);
if (v_hasTrace_969_ == 0)
{
v___y_882_ = v___y_955_;
v___y_883_ = v___y_956_;
v___y_884_ = v___y_957_;
v___y_885_ = v___y_965_;
goto v___jp_881_;
}
else
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48);
v___x_971_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_967_, v_options_966_, v___x_970_);
if (v___x_971_ == 0)
{
v___y_882_ = v___y_955_;
v___y_883_ = v___y_956_;
v___y_884_ = v___y_957_;
v___y_885_ = v___y_965_;
goto v___jp_881_;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Meta_Grind_updateLastTag(v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_968_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec_ref_known(v___x_972_, 1);
v___x_973_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50);
v___x_974_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_953_, v___x_973_, v___y_963_, v___y_964_, v___y_965_, v___y_968_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_dec_ref_known(v___x_974_, 1);
v___y_882_ = v___y_955_;
v___y_883_ = v___y_956_;
v___y_884_ = v___y_957_;
v___y_885_ = v___y_965_;
goto v___jp_881_;
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_type_769_);
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_type_769_);
v_a_983_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_972_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_972_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
v___jp_991_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_inc_ref(v___y_1005_);
v___x_1006_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___y_1005_);
v___x_1007_ = l_Lean_MessageData_ofFormat(v___x_1006_);
lean_inc_ref(v___y_1004_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___y_1004_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_953_, v___x_1008_, v___y_995_, v___y_996_, v___y_1000_, v___y_1003_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_options_1010_; lean_object* v_inheritedTraceOptions_1011_; 
lean_dec_ref_known(v___x_1009_, 1);
v_options_1010_ = lean_ctor_get(v___y_1000_, 2);
v_inheritedTraceOptions_1011_ = lean_ctor_get(v___y_1000_, 13);
v___y_955_ = v___y_993_;
v___y_956_ = v___y_999_;
v___y_957_ = v___y_994_;
v___y_958_ = v___y_1001_;
v___y_959_ = v___y_998_;
v___y_960_ = v___y_1002_;
v___y_961_ = v___y_997_;
v___y_962_ = v___y_992_;
v___y_963_ = v___y_995_;
v___y_964_ = v___y_996_;
v___y_965_ = v___y_1000_;
v_options_966_ = v_options_1010_;
v_inheritedTraceOptions_967_ = v_inheritedTraceOptions_1011_;
v___y_968_ = v___y_1003_;
goto v___jp_954_;
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec(v___y_999_);
lean_dec(v___y_993_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_type_769_);
v_a_1012_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1009_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1009_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
v___jp_1020_:
{
lean_object* v_options_1033_; lean_object* v_inheritedTraceOptions_1034_; lean_object* v___x_1035_; lean_object* v_a_1036_; uint8_t v___x_1037_; 
v_options_1033_ = lean_ctor_get(v___y_1031_, 2);
v_inheritedTraceOptions_1034_ = lean_ctor_get(v___y_1031_, 13);
v___x_1035_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(v___x_953_, v_inheritedTraceOptions_1034_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = lean_unbox(v_a_1036_);
lean_dec(v_a_1036_);
if (v___x_1037_ == 0)
{
v___y_955_ = v_noZeroDivInst_x3f_1022_;
v___y_956_ = v___y_1021_;
v___y_957_ = v___y_1023_;
v___y_958_ = v___y_1024_;
v___y_959_ = v___y_1025_;
v___y_960_ = v___y_1026_;
v___y_961_ = v___y_1027_;
v___y_962_ = v___y_1028_;
v___y_963_ = v___y_1029_;
v___y_964_ = v___y_1030_;
v___y_965_ = v___y_1031_;
v_options_966_ = v_options_1033_;
v_inheritedTraceOptions_967_ = v_inheritedTraceOptions_1034_;
v___y_968_ = v___y_1032_;
goto v___jp_954_;
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_Meta_Grind_updateLastTag(v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v___x_1039_; 
lean_dec_ref_known(v___x_1038_, 1);
v___x_1039_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11);
if (lean_obj_tag(v_noZeroDivInst_x3f_1022_) == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8));
v___y_992_ = v___y_1028_;
v___y_993_ = v_noZeroDivInst_x3f_1022_;
v___y_994_ = v___y_1023_;
v___y_995_ = v___y_1029_;
v___y_996_ = v___y_1030_;
v___y_997_ = v___y_1027_;
v___y_998_ = v___y_1025_;
v___y_999_ = v___y_1021_;
v___y_1000_ = v___y_1031_;
v___y_1001_ = v___y_1024_;
v___y_1002_ = v___y_1026_;
v___y_1003_ = v___y_1032_;
v___y_1004_ = v___x_1039_;
v___y_1005_ = v___x_1040_;
goto v___jp_991_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9));
v___y_992_ = v___y_1028_;
v___y_993_ = v_noZeroDivInst_x3f_1022_;
v___y_994_ = v___y_1023_;
v___y_995_ = v___y_1029_;
v___y_996_ = v___y_1030_;
v___y_997_ = v___y_1027_;
v___y_998_ = v___y_1025_;
v___y_999_ = v___y_1021_;
v___y_1000_ = v___y_1031_;
v___y_1001_ = v___y_1024_;
v___y_1002_ = v___y_1026_;
v___y_1003_ = v___y_1032_;
v___y_1004_ = v___x_1039_;
v___y_1005_ = v___x_1041_;
goto v___jp_991_;
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_noZeroDivInst_x3f_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_type_769_);
v_a_1042_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1038_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1038_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
v___jp_1050_:
{
lean_object* v___x_1063_; 
lean_inc_ref(v_base_770_);
lean_inc(v_val_799_);
v___x_1063_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v_val_799_, v_base_770_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
if (lean_obj_tag(v_a_1064_) == 1)
{
lean_object* v_val_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1075_; 
v_val_1065_ = lean_ctor_get(v_a_1064_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_a_1064_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1067_ = v_a_1064_;
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_val_1065_);
lean_dec(v_a_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1069_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53));
v___x_1070_ = l_Lean_mkConst(v___x_1069_, v___x_805_);
v___x_1071_ = l_Lean_mkApp4(v___x_1070_, v_base_770_, v_semiringInst_771_, v_val_1051_, v_val_1065_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1071_);
v___x_1073_ = v___x_1067_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
v___y_1021_ = v_charInst_x3f_1052_;
v_noZeroDivInst_x3f_1022_ = v___x_1073_;
v___y_1023_ = v___y_1053_;
v___y_1024_ = v___y_1054_;
v___y_1025_ = v___y_1055_;
v___y_1026_ = v___y_1056_;
v___y_1027_ = v___y_1057_;
v___y_1028_ = v___y_1058_;
v___y_1029_ = v___y_1059_;
v___y_1030_ = v___y_1060_;
v___y_1031_ = v___y_1061_;
v___y_1032_ = v___y_1062_;
goto v___jp_1020_;
}
}
}
else
{
lean_object* v___x_1076_; 
lean_dec(v_a_1064_);
lean_dec_ref(v_val_1051_);
lean_dec_ref_known(v___x_805_, 2);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
v___x_1076_ = lean_box(0);
v___y_1021_ = v_charInst_x3f_1052_;
v_noZeroDivInst_x3f_1022_ = v___x_1076_;
v___y_1023_ = v___y_1053_;
v___y_1024_ = v___y_1054_;
v___y_1025_ = v___y_1055_;
v___y_1026_ = v___y_1056_;
v___y_1027_ = v___y_1057_;
v___y_1028_ = v___y_1058_;
v___y_1029_ = v___y_1059_;
v___y_1030_ = v___y_1060_;
v___y_1031_ = v___y_1061_;
v___y_1032_ = v___y_1062_;
goto v___jp_1020_;
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec(v_charInst_x3f_1052_);
lean_dec_ref(v_val_1051_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1077_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1063_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1063_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
v___jp_1085_:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_box(0);
v___y_1021_ = v___x_1096_;
v_noZeroDivInst_x3f_1022_ = v___x_1096_;
v___y_1023_ = v___y_1086_;
v___y_1024_ = v___y_1087_;
v___y_1025_ = v___y_1088_;
v___y_1026_ = v___y_1089_;
v___y_1027_ = v___y_1090_;
v___y_1028_ = v___y_1091_;
v___y_1029_ = v___y_1092_;
v___y_1030_ = v___y_1093_;
v___y_1031_ = v___y_1094_;
v___y_1032_ = v___y_1095_;
goto v___jp_1020_;
}
v___jp_1097_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__55));
lean_inc_ref(v___x_805_);
v___x_1109_ = l_Lean_mkConst(v___x_1108_, v___x_805_);
lean_inc_ref(v_base_770_);
v___x_1110_ = l_Lean_Expr_app___override(v___x_1109_, v_base_770_);
v___x_1111_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1110_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
if (lean_obj_tag(v_a_1112_) == 1)
{
lean_object* v_val_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_val_1113_ = lean_ctor_get(v_a_1112_, 0);
lean_inc(v_val_1113_);
lean_dec_ref_known(v_a_1112_, 1);
v___x_1114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57));
lean_inc_ref(v___x_805_);
v___x_1115_ = l_Lean_mkConst(v___x_1114_, v___x_805_);
lean_inc_ref(v_base_770_);
v___x_1116_ = l_Lean_mkAppB(v___x_1115_, v_base_770_, v_val_1113_);
v___x_1117_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1116_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
if (lean_obj_tag(v_a_1118_) == 1)
{
lean_object* v_val_1119_; lean_object* v___x_1120_; 
v_val_1119_ = lean_ctor_get(v_a_1118_, 0);
lean_inc(v_val_1119_);
lean_dec_ref_known(v_a_1118_, 1);
lean_inc_ref(v_semiringInst_771_);
lean_inc_ref(v_base_770_);
lean_inc(v_val_799_);
v___x_1120_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_val_799_, v_base_770_, v_semiringInst_771_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1120_, 1);
if (lean_obj_tag(v_a_1121_) == 1)
{
lean_object* v_val_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1142_; 
v_val_1122_ = lean_ctor_get(v_a_1121_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_a_1121_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1124_ = v_a_1121_;
v_isShared_1125_ = v_isSharedCheck_1142_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_val_1122_);
lean_dec(v_a_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1142_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_fst_1126_; lean_object* v_snd_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1141_; 
v_fst_1126_ = lean_ctor_get(v_val_1122_, 0);
v_snd_1127_ = lean_ctor_get(v_val_1122_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_val_1122_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1129_ = v_val_1122_;
v_isShared_1130_ = v_isSharedCheck_1141_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_snd_1127_);
lean_inc(v_fst_1126_);
lean_dec(v_val_1122_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1141_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__59));
lean_inc_ref(v___x_805_);
v___x_1132_ = l_Lean_mkConst(v___x_1131_, v___x_805_);
lean_inc(v_snd_1127_);
v___x_1133_ = l_Lean_mkRawNatLit(v_snd_1127_);
lean_inc(v_val_1119_);
lean_inc_ref(v_semiringInst_771_);
lean_inc_ref(v_base_770_);
v___x_1134_ = l_Lean_mkApp5(v___x_1132_, v_base_770_, v___x_1133_, v_semiringInst_771_, v_val_1119_, v_fst_1126_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1134_);
v___x_1136_ = v___x_1129_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_snd_1127_);
v___x_1136_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1136_);
v___x_1138_ = v___x_1124_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
v_val_1051_ = v_val_1119_;
v_charInst_x3f_1052_ = v___x_1138_;
v___y_1053_ = v___y_1098_;
v___y_1054_ = v___y_1099_;
v___y_1055_ = v___y_1100_;
v___y_1056_ = v___y_1101_;
v___y_1057_ = v___y_1102_;
v___y_1058_ = v___y_1103_;
v___y_1059_ = v___y_1104_;
v___y_1060_ = v___y_1105_;
v___y_1061_ = v___y_1106_;
v___y_1062_ = v___y_1107_;
goto v___jp_1050_;
}
}
}
}
}
else
{
lean_object* v___x_1143_; 
lean_dec(v_a_1121_);
v___x_1143_ = lean_box(0);
v_val_1051_ = v_val_1119_;
v_charInst_x3f_1052_ = v___x_1143_;
v___y_1053_ = v___y_1098_;
v___y_1054_ = v___y_1099_;
v___y_1055_ = v___y_1100_;
v___y_1056_ = v___y_1101_;
v___y_1057_ = v___y_1102_;
v___y_1058_ = v___y_1103_;
v___y_1059_ = v___y_1104_;
v___y_1060_ = v___y_1105_;
v___y_1061_ = v___y_1106_;
v___y_1062_ = v___y_1107_;
goto v___jp_1050_;
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_val_1119_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1144_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1120_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1120_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
if (lean_obj_tag(v_a_1118_) == 1)
{
lean_object* v_val_1152_; lean_object* v___x_1153_; 
v_val_1152_ = lean_ctor_get(v_a_1118_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v_a_1118_, 1);
v___x_1153_ = lean_box(0);
v_val_1051_ = v_val_1152_;
v_charInst_x3f_1052_ = v___x_1153_;
v___y_1053_ = v___y_1098_;
v___y_1054_ = v___y_1099_;
v___y_1055_ = v___y_1100_;
v___y_1056_ = v___y_1101_;
v___y_1057_ = v___y_1102_;
v___y_1058_ = v___y_1103_;
v___y_1059_ = v___y_1104_;
v___y_1060_ = v___y_1105_;
v___y_1061_ = v___y_1106_;
v___y_1062_ = v___y_1107_;
goto v___jp_1050_;
}
else
{
lean_dec(v_a_1118_);
lean_dec_ref_known(v___x_805_, 2);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
v___y_1086_ = v___y_1098_;
v___y_1087_ = v___y_1099_;
v___y_1088_ = v___y_1100_;
v___y_1089_ = v___y_1101_;
v___y_1090_ = v___y_1102_;
v___y_1091_ = v___y_1103_;
v___y_1092_ = v___y_1104_;
v___y_1093_ = v___y_1105_;
v___y_1094_ = v___y_1106_;
v___y_1095_ = v___y_1107_;
goto v___jp_1085_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1154_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1117_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1117_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_dec(v_a_1112_);
lean_dec_ref_known(v___x_805_, 2);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
v___y_1086_ = v___y_1098_;
v___y_1087_ = v___y_1099_;
v___y_1088_ = v___y_1100_;
v___y_1089_ = v___y_1101_;
v___y_1090_ = v___y_1102_;
v___y_1091_ = v___y_1103_;
v___y_1092_ = v___y_1104_;
v___y_1093_ = v___y_1105_;
v___y_1094_ = v___y_1106_;
v___y_1095_ = v___y_1107_;
goto v___jp_1085_;
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1162_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1111_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1111_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1194_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_951_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_951_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1202_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_944_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_944_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1210_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_937_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_937_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
v___jp_881_:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_884_, v___y_885_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v_rings_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
v_rings_888_ = lean_ctor_get(v_a_887_, 0);
lean_inc_ref(v_rings_888_);
lean_dec(v_a_887_);
v___x_889_ = lean_array_get_size(v_rings_888_);
lean_dec_ref(v_rings_888_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1);
v___x_892_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3);
v___x_893_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_893_, 0, v___x_889_);
lean_ctor_set(v___x_893_, 1, v_type_769_);
lean_ctor_set(v___x_893_, 2, v_val_799_);
lean_ctor_set(v___x_893_, 3, v___x_810_);
lean_ctor_set(v___x_893_, 4, v___x_813_);
lean_ctor_set(v___x_893_, 5, v___y_883_);
lean_ctor_set(v___x_893_, 6, v___x_890_);
lean_ctor_set(v___x_893_, 7, v___x_890_);
lean_ctor_set(v___x_893_, 8, v___x_890_);
lean_ctor_set(v___x_893_, 9, v___x_890_);
lean_ctor_set(v___x_893_, 10, v___x_890_);
lean_ctor_set(v___x_893_, 11, v___x_890_);
lean_ctor_set(v___x_893_, 12, v___x_890_);
lean_ctor_set(v___x_893_, 13, v___x_890_);
lean_ctor_set(v___x_893_, 14, v___x_891_);
lean_ctor_set(v___x_893_, 15, v___x_892_);
lean_ctor_set(v___x_893_, 16, v___x_892_);
v___x_894_ = lean_box(1);
v___x_895_ = 0;
v___x_896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4);
v___x_897_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v___x_897_, 0, v___x_893_);
lean_ctor_set(v___x_897_, 1, v___x_890_);
lean_ctor_set(v___x_897_, 2, v___x_890_);
lean_ctor_set(v___x_897_, 3, v___x_816_);
lean_ctor_set(v___x_897_, 4, v___x_807_);
lean_ctor_set(v___x_897_, 5, v___y_882_);
lean_ctor_set(v___x_897_, 6, v___x_890_);
lean_ctor_set(v___x_897_, 7, v___x_890_);
lean_ctor_set(v___x_897_, 8, v___x_891_);
lean_ctor_set(v___x_897_, 9, v___x_880_);
lean_ctor_set(v___x_897_, 10, v___x_880_);
lean_ctor_set(v___x_897_, 11, v___x_894_);
lean_ctor_set(v___x_897_, 12, v___x_804_);
lean_ctor_set(v___x_897_, 13, v___x_891_);
lean_ctor_set(v___x_897_, 14, v___x_896_);
lean_ctor_set(v___x_897_, 15, v___x_880_);
lean_ctor_set(v___x_897_, 16, v___x_890_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*17, v___x_895_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*17 + 1, v___x_895_);
v___f_898_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0), 2, 1);
lean_closure_set(v___f_898_, 0, v___x_897_);
v___x_899_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_900_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_899_, v___f_898_, v___y_884_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_910_; 
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v___x_900_, 0);
lean_dec(v_unused_911_);
v___x_902_ = v___x_900_;
v_isShared_903_ = v_isSharedCheck_910_;
goto v_resetjp_901_;
}
else
{
lean_dec(v___x_900_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_910_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_889_);
v___x_905_ = v___x_801_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_889_);
v___x_905_ = v_reuseFailAlloc_909_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_907_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_905_);
v___x_907_ = v___x_902_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_del_object(v___x_801_);
v_a_912_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_900_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_900_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_type_769_);
v_a_920_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_886_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_886_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1218_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_878_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_878_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1226_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_871_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_871_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
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
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref_known(v___x_842_, 2);
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1234_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_861_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_861_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref_known(v___x_842_, 2);
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1242_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_851_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_851_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1250_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_839_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_839_);
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
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1258_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_832_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_832_);
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
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1266_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_828_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_828_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1274_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_824_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_824_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_807_);
lean_dec_ref_known(v___x_805_, 2);
lean_del_object(v___x_801_);
lean_dec(v_val_799_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1282_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_820_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_820_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
lean_dec(v_a_795_);
lean_dec_ref(v_arg_786_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v___x_1291_ = lean_box(0);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_1291_);
v___x_1293_ = v___x_797_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_arg_786_);
lean_dec_ref(v_semiringInst_771_);
lean_dec_ref(v_base_770_);
lean_dec_ref(v_type_769_);
v_a_1296_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_794_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_794_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___boxed(lean_object* v_type_1304_, lean_object* v_base_1305_, lean_object* v_semiringInst_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f(v_type_1304_, v_base_1305_, v_semiringInst_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec(v_a_1307_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(lean_object* v_type_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1));
v___x_1339_ = lean_unsigned_to_nat(2u);
v___x_1340_ = l_Lean_Expr_isAppOfArity(v_type_1326_, v___x_1338_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
return v___x_1341_;
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1342_ = l_Lean_Expr_appFn_x21(v_type_1326_);
v___x_1343_ = l_Lean_Expr_appArg_x21(v___x_1342_);
lean_dec_ref(v___x_1342_);
v___x_1344_ = l_Lean_Expr_appArg_x21(v_type_1326_);
v___x_1345_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f(v_type_1326_, v___x_1343_, v___x_1344_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
return v___x_1345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___boxed(lean_object* v_type_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_a_1348_);
lean_dec(v_a_1347_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1391_, lean_object* v_k_1392_, lean_object* v_v_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1391_, v___x_1394_, v_k_1392_, v_v_1393_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(lean_object* v_x_1397_, size_t v_x_1398_, size_t v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
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
v___x_1442_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_node_1434_, v___x_1439_, v___x_1441_, v_x_1400_, v_x_1401_);
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
lean_object* v_ks_1450_; lean_object* v_vs_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1471_; 
v_ks_1450_ = lean_ctor_get(v_x_1397_, 0);
v_vs_1451_ = lean_ctor_get(v_x_1397_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_x_1397_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1453_ = v_x_1397_;
v_isShared_1454_ = v_isSharedCheck_1471_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_vs_1451_);
lean_inc(v_ks_1450_);
lean_dec(v_x_1397_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1471_;
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
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_ks_1450_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_vs_1451_);
v___x_1456_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v_newNode_1457_; uint8_t v___y_1459_; size_t v___x_1465_; uint8_t v___x_1466_; 
v_newNode_1457_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v___x_1456_, v_x_1400_, v_x_1401_);
v___x_1465_ = ((size_t)7ULL);
v___x_1466_ = lean_usize_dec_le(v___x_1465_, v_x_1399_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1457_);
v___x_1468_ = lean_unsigned_to_nat(4u);
v___x_1469_ = lean_nat_dec_lt(v___x_1467_, v___x_1468_);
lean_dec(v___x_1467_);
v___y_1459_ = v___x_1469_;
goto v___jp_1458_;
}
else
{
v___y_1459_ = v___x_1466_;
goto v___jp_1458_;
}
v___jp_1458_:
{
if (v___y_1459_ == 0)
{
lean_object* v_ks_1460_; lean_object* v_vs_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_ks_1460_ = lean_ctor_get(v_newNode_1457_, 0);
lean_inc_ref(v_ks_1460_);
v_vs_1461_ = lean_ctor_get(v_newNode_1457_, 1);
lean_inc_ref(v_vs_1461_);
lean_dec_ref(v_newNode_1457_);
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0);
v___x_1464_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_x_1399_, v_ks_1460_, v_vs_1461_, v___x_1462_, v___x_1463_);
lean_dec_ref(v_vs_1461_);
lean_dec_ref(v_ks_1460_);
return v___x_1464_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_1472_, lean_object* v_keys_1473_, lean_object* v_vals_1474_, lean_object* v_i_1475_, lean_object* v_entries_1476_){
_start:
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = lean_array_get_size(v_keys_1473_);
v___x_1478_ = lean_nat_dec_lt(v_i_1475_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_dec(v_i_1475_);
return v_entries_1476_;
}
else
{
lean_object* v_k_1479_; lean_object* v_v_1480_; size_t v___x_1481_; size_t v___x_1482_; size_t v___x_1483_; uint64_t v___x_1484_; size_t v_h_1485_; size_t v___x_1486_; lean_object* v___x_1487_; size_t v___x_1488_; size_t v___x_1489_; size_t v___x_1490_; size_t v_h_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v_k_1479_ = lean_array_fget_borrowed(v_keys_1473_, v_i_1475_);
v_v_1480_ = lean_array_fget_borrowed(v_vals_1474_, v_i_1475_);
v___x_1481_ = lean_ptr_addr(v_k_1479_);
v___x_1482_ = ((size_t)3ULL);
v___x_1483_ = lean_usize_shift_right(v___x_1481_, v___x_1482_);
v___x_1484_ = lean_usize_to_uint64(v___x_1483_);
v_h_1485_ = lean_uint64_to_usize(v___x_1484_);
v___x_1486_ = ((size_t)5ULL);
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = ((size_t)1ULL);
v___x_1489_ = lean_usize_sub(v_depth_1472_, v___x_1488_);
v___x_1490_ = lean_usize_mul(v___x_1486_, v___x_1489_);
v_h_1491_ = lean_usize_shift_right(v_h_1485_, v___x_1490_);
v___x_1492_ = lean_nat_add(v_i_1475_, v___x_1487_);
lean_dec(v_i_1475_);
lean_inc(v_v_1480_);
lean_inc(v_k_1479_);
v___x_1493_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_entries_1476_, v_h_1491_, v_depth_1472_, v_k_1479_, v_v_1480_);
v_i_1475_ = v___x_1492_;
v_entries_1476_ = v___x_1493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1495_, lean_object* v_keys_1496_, lean_object* v_vals_1497_, lean_object* v_i_1498_, lean_object* v_entries_1499_){
_start:
{
size_t v_depth_boxed_1500_; lean_object* v_res_1501_; 
v_depth_boxed_1500_ = lean_unbox_usize(v_depth_1495_);
lean_dec(v_depth_1495_);
v_res_1501_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1500_, v_keys_1496_, v_vals_1497_, v_i_1498_, v_entries_1499_);
lean_dec_ref(v_vals_1497_);
lean_dec_ref(v_keys_1496_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_, lean_object* v_x_1506_){
_start:
{
size_t v_x_3757__boxed_1507_; size_t v_x_3758__boxed_1508_; lean_object* v_res_1509_; 
v_x_3757__boxed_1507_ = lean_unbox_usize(v_x_1503_);
lean_dec(v_x_1503_);
v_x_3758__boxed_1508_ = lean_unbox_usize(v_x_1504_);
lean_dec(v_x_1504_);
v_res_1509_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_1502_, v_x_3757__boxed_1507_, v_x_3758__boxed_1508_, v_x_1505_, v_x_1506_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(lean_object* v_x_1510_, lean_object* v_x_1511_, lean_object* v_x_1512_){
_start:
{
size_t v___x_1513_; size_t v___x_1514_; size_t v___x_1515_; uint64_t v___x_1516_; size_t v___x_1517_; size_t v___x_1518_; lean_object* v___x_1519_; 
v___x_1513_ = lean_ptr_addr(v_x_1511_);
v___x_1514_ = ((size_t)3ULL);
v___x_1515_ = lean_usize_shift_right(v___x_1513_, v___x_1514_);
v___x_1516_ = lean_usize_to_uint64(v___x_1515_);
v___x_1517_ = lean_uint64_to_usize(v___x_1516_);
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_1510_, v___x_1517_, v___x_1518_, v_x_1511_, v_x_1512_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0(lean_object* v_type_1520_, lean_object* v_a_1521_, lean_object* v_s_1522_){
_start:
{
lean_object* v_rings_1523_; lean_object* v_typeIdOf_1524_; lean_object* v_exprToRingId_1525_; lean_object* v_semirings_1526_; lean_object* v_stypeIdOf_1527_; lean_object* v_exprToSemiringId_1528_; lean_object* v_ncRings_1529_; lean_object* v_exprToNCRingId_1530_; lean_object* v_nctypeIdOf_1531_; lean_object* v_ncSemirings_1532_; lean_object* v_exprToNCSemiringId_1533_; lean_object* v_ncstypeIdOf_1534_; lean_object* v_steps_1535_; uint8_t v_reportedMaxDegreeIssue_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1544_; 
v_rings_1523_ = lean_ctor_get(v_s_1522_, 0);
v_typeIdOf_1524_ = lean_ctor_get(v_s_1522_, 1);
v_exprToRingId_1525_ = lean_ctor_get(v_s_1522_, 2);
v_semirings_1526_ = lean_ctor_get(v_s_1522_, 3);
v_stypeIdOf_1527_ = lean_ctor_get(v_s_1522_, 4);
v_exprToSemiringId_1528_ = lean_ctor_get(v_s_1522_, 5);
v_ncRings_1529_ = lean_ctor_get(v_s_1522_, 6);
v_exprToNCRingId_1530_ = lean_ctor_get(v_s_1522_, 7);
v_nctypeIdOf_1531_ = lean_ctor_get(v_s_1522_, 8);
v_ncSemirings_1532_ = lean_ctor_get(v_s_1522_, 9);
v_exprToNCSemiringId_1533_ = lean_ctor_get(v_s_1522_, 10);
v_ncstypeIdOf_1534_ = lean_ctor_get(v_s_1522_, 11);
v_steps_1535_ = lean_ctor_get(v_s_1522_, 12);
v_reportedMaxDegreeIssue_1536_ = lean_ctor_get_uint8(v_s_1522_, sizeof(void*)*13);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_s_1522_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1538_ = v_s_1522_;
v_isShared_1539_ = v_isSharedCheck_1544_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_steps_1535_);
lean_inc(v_ncstypeIdOf_1534_);
lean_inc(v_exprToNCSemiringId_1533_);
lean_inc(v_ncSemirings_1532_);
lean_inc(v_nctypeIdOf_1531_);
lean_inc(v_exprToNCRingId_1530_);
lean_inc(v_ncRings_1529_);
lean_inc(v_exprToSemiringId_1528_);
lean_inc(v_stypeIdOf_1527_);
lean_inc(v_semirings_1526_);
lean_inc(v_exprToRingId_1525_);
lean_inc(v_typeIdOf_1524_);
lean_inc(v_rings_1523_);
lean_dec(v_s_1522_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1544_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_typeIdOf_1524_, v_type_1520_, v_a_1521_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 1, v___x_1540_);
v___x_1542_ = v___x_1538_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_rings_1523_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_exprToRingId_1525_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_semirings_1526_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v_stypeIdOf_1527_);
lean_ctor_set(v_reuseFailAlloc_1543_, 5, v_exprToSemiringId_1528_);
lean_ctor_set(v_reuseFailAlloc_1543_, 6, v_ncRings_1529_);
lean_ctor_set(v_reuseFailAlloc_1543_, 7, v_exprToNCRingId_1530_);
lean_ctor_set(v_reuseFailAlloc_1543_, 8, v_nctypeIdOf_1531_);
lean_ctor_set(v_reuseFailAlloc_1543_, 9, v_ncSemirings_1532_);
lean_ctor_set(v_reuseFailAlloc_1543_, 10, v_exprToNCSemiringId_1533_);
lean_ctor_set(v_reuseFailAlloc_1543_, 11, v_ncstypeIdOf_1534_);
lean_ctor_set(v_reuseFailAlloc_1543_, 12, v_steps_1535_);
lean_ctor_set_uint8(v_reuseFailAlloc_1543_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1536_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1545_, lean_object* v_vals_1546_, lean_object* v_i_1547_, lean_object* v_k_1548_){
_start:
{
lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = lean_array_get_size(v_keys_1545_);
v___x_1550_ = lean_nat_dec_lt(v_i_1547_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_dec(v_i_1547_);
v___x_1551_ = lean_box(0);
return v___x_1551_;
}
else
{
lean_object* v_k_x27_1552_; size_t v___x_1553_; size_t v___x_1554_; uint8_t v___x_1555_; 
v_k_x27_1552_ = lean_array_fget_borrowed(v_keys_1545_, v_i_1547_);
v___x_1553_ = lean_ptr_addr(v_k_1548_);
v___x_1554_ = lean_ptr_addr(v_k_x27_1552_);
v___x_1555_ = lean_usize_dec_eq(v___x_1553_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_add(v_i_1547_, v___x_1556_);
lean_dec(v_i_1547_);
v_i_1547_ = v___x_1557_;
goto _start;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_array_fget_borrowed(v_vals_1546_, v_i_1547_);
lean_dec(v_i_1547_);
lean_inc(v___x_1559_);
v___x_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
return v___x_1560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1561_, lean_object* v_vals_1562_, lean_object* v_i_1563_, lean_object* v_k_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1561_, v_vals_1562_, v_i_1563_, v_k_1564_);
lean_dec_ref(v_k_1564_);
lean_dec_ref(v_vals_1562_);
lean_dec_ref(v_keys_1561_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_1566_, size_t v_x_1567_, lean_object* v_x_1568_){
_start:
{
if (lean_obj_tag(v_x_1566_) == 0)
{
lean_object* v_es_1569_; lean_object* v___x_1570_; size_t v___x_1571_; size_t v___x_1572_; lean_object* v_j_1573_; lean_object* v___x_1574_; 
v_es_1569_ = lean_ctor_get(v_x_1566_, 0);
v___x_1570_ = lean_box(2);
v___x_1571_ = ((size_t)31ULL);
v___x_1572_ = lean_usize_land(v_x_1567_, v___x_1571_);
v_j_1573_ = lean_usize_to_nat(v___x_1572_);
v___x_1574_ = lean_array_get_borrowed(v___x_1570_, v_es_1569_, v_j_1573_);
lean_dec(v_j_1573_);
switch(lean_obj_tag(v___x_1574_))
{
case 0:
{
lean_object* v_key_1575_; lean_object* v_val_1576_; size_t v___x_1577_; size_t v___x_1578_; uint8_t v___x_1579_; 
v_key_1575_ = lean_ctor_get(v___x_1574_, 0);
v_val_1576_ = lean_ctor_get(v___x_1574_, 1);
v___x_1577_ = lean_ptr_addr(v_x_1568_);
v___x_1578_ = lean_ptr_addr(v_key_1575_);
v___x_1579_ = lean_usize_dec_eq(v___x_1577_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_box(0);
return v___x_1580_;
}
else
{
lean_object* v___x_1581_; 
lean_inc(v_val_1576_);
v___x_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1581_, 0, v_val_1576_);
return v___x_1581_;
}
}
case 1:
{
lean_object* v_node_1582_; size_t v___x_1583_; size_t v___x_1584_; 
v_node_1582_ = lean_ctor_get(v___x_1574_, 0);
v___x_1583_ = ((size_t)5ULL);
v___x_1584_ = lean_usize_shift_right(v_x_1567_, v___x_1583_);
v_x_1566_ = v_node_1582_;
v_x_1567_ = v___x_1584_;
goto _start;
}
default: 
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_box(0);
return v___x_1586_;
}
}
}
else
{
lean_object* v_ks_1587_; lean_object* v_vs_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_ks_1587_ = lean_ctor_get(v_x_1566_, 0);
v_vs_1588_ = lean_ctor_get(v_x_1566_, 1);
v___x_1589_ = lean_unsigned_to_nat(0u);
v___x_1590_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1587_, v_vs_1588_, v___x_1589_, v_x_1568_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_){
_start:
{
size_t v_x_3980__boxed_1594_; lean_object* v_res_1595_; 
v_x_3980__boxed_1594_ = lean_unbox_usize(v_x_1592_);
lean_dec(v_x_1592_);
v_res_1595_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_1591_, v_x_3980__boxed_1594_, v_x_1593_);
lean_dec_ref(v_x_1593_);
lean_dec_ref(v_x_1591_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(lean_object* v_x_1596_, lean_object* v_x_1597_){
_start:
{
size_t v___x_1598_; size_t v___x_1599_; size_t v___x_1600_; uint64_t v___x_1601_; size_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1598_ = lean_ptr_addr(v_x_1597_);
v___x_1599_ = ((size_t)3ULL);
v___x_1600_ = lean_usize_shift_right(v___x_1598_, v___x_1599_);
v___x_1601_ = lean_usize_to_uint64(v___x_1600_);
v___x_1602_ = lean_uint64_to_usize(v___x_1601_);
v___x_1603_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_1596_, v___x_1602_, v_x_1597_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_1604_, v_x_1605_);
lean_dec_ref(v_x_1605_);
lean_dec_ref(v_x_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object* v_type_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1608_, v_a_1616_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1651_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1651_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1651_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v_typeIdOf_1624_; lean_object* v___x_1625_; 
v_typeIdOf_1624_ = lean_ctor_get(v_a_1620_, 1);
lean_inc_ref(v_typeIdOf_1624_);
lean_dec(v_a_1620_);
v___x_1625_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_typeIdOf_1624_, v_type_1607_);
lean_dec_ref(v_typeIdOf_1624_);
if (lean_obj_tag(v___x_1625_) == 1)
{
lean_object* v_val_1626_; lean_object* v___x_1628_; 
lean_dec_ref(v_type_1607_);
v_val_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_val_1626_);
lean_dec_ref_known(v___x_1625_, 1);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v_val_1626_);
v___x_1628_ = v___x_1622_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_val_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
else
{
lean_object* v___x_1630_; 
lean_dec(v___x_1625_);
lean_del_object(v___x_1622_);
lean_inc_ref(v_type_1607_);
v___x_1630_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___f_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc_n(v_a_1631_, 2);
lean_dec_ref_known(v___x_1630_, 1);
v___f_1632_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1632_, 0, v_type_1607_);
lean_closure_set(v___f_1632_, 1, v_a_1631_);
v___x_1633_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1634_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1633_, v___f_1632_, v_a_1608_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; 
v_unused_1642_ = lean_ctor_get(v___x_1634_, 0);
lean_dec(v_unused_1642_);
v___x_1636_ = v___x_1634_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_dec(v___x_1634_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v_a_1631_);
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1631_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v_a_1631_);
v_a_1643_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1634_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1634_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_dec_ref(v_type_1607_);
return v___x_1630_;
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v_type_1607_);
v_a_1652_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1619_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1619_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___boxed(lean_object* v_type_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
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
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(lean_object* v_00_u03b2_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_1674_, v_x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(v_00_u03b2_1677_, v_x_1678_, v_x_1679_);
lean_dec_ref(v_x_1679_);
lean_dec_ref(v_x_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1(lean_object* v_00_u03b2_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_x_1682_, v_x_1683_, v_x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1686_, lean_object* v_x_1687_, size_t v_x_1688_, lean_object* v_x_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_1687_, v_x_1688_, v_x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1691_, lean_object* v_x_1692_, lean_object* v_x_1693_, lean_object* v_x_1694_){
_start:
{
size_t v_x_4150__boxed_1695_; lean_object* v_res_1696_; 
v_x_4150__boxed_1695_ = lean_unbox_usize(v_x_1693_);
lean_dec(v_x_1693_);
v_res_1696_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(v_00_u03b2_1691_, v_x_1692_, v_x_4150__boxed_1695_, v_x_1694_);
lean_dec_ref(v_x_1694_);
lean_dec_ref(v_x_1692_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(lean_object* v_00_u03b2_1697_, lean_object* v_x_1698_, size_t v_x_1699_, size_t v_x_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_1698_, v_x_1699_, v_x_1700_, v_x_1701_, v_x_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1704_, lean_object* v_x_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_, lean_object* v_x_1709_){
_start:
{
size_t v_x_4161__boxed_1710_; size_t v_x_4162__boxed_1711_; lean_object* v_res_1712_; 
v_x_4161__boxed_1710_ = lean_unbox_usize(v_x_1706_);
lean_dec(v_x_1706_);
v_x_4162__boxed_1711_ = lean_unbox_usize(v_x_1707_);
lean_dec(v_x_1707_);
v_res_1712_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(v_00_u03b2_1704_, v_x_1705_, v_x_4161__boxed_1710_, v_x_4162__boxed_1711_, v_x_1708_, v_x_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1713_, lean_object* v_keys_1714_, lean_object* v_vals_1715_, lean_object* v_heq_1716_, lean_object* v_i_1717_, lean_object* v_k_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1714_, v_vals_1715_, v_i_1717_, v_k_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1720_, lean_object* v_keys_1721_, lean_object* v_vals_1722_, lean_object* v_heq_1723_, lean_object* v_i_1724_, lean_object* v_k_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1720_, v_keys_1721_, v_vals_1722_, v_heq_1723_, v_i_1724_, v_k_1725_);
lean_dec_ref(v_k_1725_);
lean_dec_ref(v_vals_1722_);
lean_dec_ref(v_keys_1721_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1727_, lean_object* v_n_1728_, lean_object* v_k_1729_, lean_object* v_v_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v_n_1728_, v_k_1729_, v_v_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1732_, size_t v_depth_1733_, lean_object* v_keys_1734_, lean_object* v_vals_1735_, lean_object* v_heq_1736_, lean_object* v_i_1737_, lean_object* v_entries_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_1733_, v_keys_1734_, v_vals_1735_, v_i_1737_, v_entries_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1740_, lean_object* v_depth_1741_, lean_object* v_keys_1742_, lean_object* v_vals_1743_, lean_object* v_heq_1744_, lean_object* v_i_1745_, lean_object* v_entries_1746_){
_start:
{
size_t v_depth_boxed_1747_; lean_object* v_res_1748_; 
v_depth_boxed_1747_ = lean_unbox_usize(v_depth_1741_);
lean_dec(v_depth_1741_);
v_res_1748_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1740_, v_depth_boxed_1747_, v_keys_1742_, v_vals_1743_, v_heq_1744_, v_i_1745_, v_entries_1746_);
lean_dec_ref(v_vals_1743_);
lean_dec_ref(v_keys_1742_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1750_, v_x_1751_, v_x_1752_, v_x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0(lean_object* v___x_1755_, lean_object* v_s_1756_){
_start:
{
lean_object* v_rings_1757_; lean_object* v_typeIdOf_1758_; lean_object* v_exprToRingId_1759_; lean_object* v_semirings_1760_; lean_object* v_stypeIdOf_1761_; lean_object* v_exprToSemiringId_1762_; lean_object* v_ncRings_1763_; lean_object* v_exprToNCRingId_1764_; lean_object* v_nctypeIdOf_1765_; lean_object* v_ncSemirings_1766_; lean_object* v_exprToNCSemiringId_1767_; lean_object* v_ncstypeIdOf_1768_; lean_object* v_steps_1769_; uint8_t v_reportedMaxDegreeIssue_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1778_; 
v_rings_1757_ = lean_ctor_get(v_s_1756_, 0);
v_typeIdOf_1758_ = lean_ctor_get(v_s_1756_, 1);
v_exprToRingId_1759_ = lean_ctor_get(v_s_1756_, 2);
v_semirings_1760_ = lean_ctor_get(v_s_1756_, 3);
v_stypeIdOf_1761_ = lean_ctor_get(v_s_1756_, 4);
v_exprToSemiringId_1762_ = lean_ctor_get(v_s_1756_, 5);
v_ncRings_1763_ = lean_ctor_get(v_s_1756_, 6);
v_exprToNCRingId_1764_ = lean_ctor_get(v_s_1756_, 7);
v_nctypeIdOf_1765_ = lean_ctor_get(v_s_1756_, 8);
v_ncSemirings_1766_ = lean_ctor_get(v_s_1756_, 9);
v_exprToNCSemiringId_1767_ = lean_ctor_get(v_s_1756_, 10);
v_ncstypeIdOf_1768_ = lean_ctor_get(v_s_1756_, 11);
v_steps_1769_ = lean_ctor_get(v_s_1756_, 12);
v_reportedMaxDegreeIssue_1770_ = lean_ctor_get_uint8(v_s_1756_, sizeof(void*)*13);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_s_1756_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1772_ = v_s_1756_;
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_steps_1769_);
lean_inc(v_ncstypeIdOf_1768_);
lean_inc(v_exprToNCSemiringId_1767_);
lean_inc(v_ncSemirings_1766_);
lean_inc(v_nctypeIdOf_1765_);
lean_inc(v_exprToNCRingId_1764_);
lean_inc(v_ncRings_1763_);
lean_inc(v_exprToSemiringId_1762_);
lean_inc(v_stypeIdOf_1761_);
lean_inc(v_semirings_1760_);
lean_inc(v_exprToRingId_1759_);
lean_inc(v_typeIdOf_1758_);
lean_inc(v_rings_1757_);
lean_dec(v_s_1756_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1774_ = lean_array_push(v_ncRings_1763_, v___x_1755_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 6, v___x_1774_);
v___x_1776_ = v___x_1772_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_rings_1757_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_typeIdOf_1758_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v_exprToRingId_1759_);
lean_ctor_set(v_reuseFailAlloc_1777_, 3, v_semirings_1760_);
lean_ctor_set(v_reuseFailAlloc_1777_, 4, v_stypeIdOf_1761_);
lean_ctor_set(v_reuseFailAlloc_1777_, 5, v_exprToSemiringId_1762_);
lean_ctor_set(v_reuseFailAlloc_1777_, 6, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1777_, 7, v_exprToNCRingId_1764_);
lean_ctor_set(v_reuseFailAlloc_1777_, 8, v_nctypeIdOf_1765_);
lean_ctor_set(v_reuseFailAlloc_1777_, 9, v_ncSemirings_1766_);
lean_ctor_set(v_reuseFailAlloc_1777_, 10, v_exprToNCSemiringId_1767_);
lean_ctor_set(v_reuseFailAlloc_1777_, 11, v_ncstypeIdOf_1768_);
lean_ctor_set(v_reuseFailAlloc_1777_, 12, v_steps_1769_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1770_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(lean_object* v_type_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v_val_1854_; lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_leCarrierIsSort(v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; uint8_t v___x_1911_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v___x_1911_ = lean_unbox(v_a_1910_);
lean_dec(v_a_1910_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; 
lean_inc_ref(v_type_1779_);
v___x_1912_ = l_Lean_Meta_getDecLevel(v_type_1779_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v_val_1854_ = v_a_1913_;
goto v___jp_1853_;
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v_type_1779_);
v_a_1914_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1912_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1912_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v___x_1922_; 
lean_inc_ref(v_type_1779_);
v___x_1922_ = l_Lean_Meta_getDecLevel_x3f(v_type_1779_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1932_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1932_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1932_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
if (lean_obj_tag(v_a_1923_) == 1)
{
lean_object* v_val_1927_; 
lean_del_object(v___x_1925_);
v_val_1927_ = lean_ctor_get(v_a_1923_, 0);
lean_inc(v_val_1927_);
lean_dec_ref_known(v_a_1923_, 1);
v_val_1854_ = v_val_1927_;
goto v___jp_1853_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
lean_dec(v_a_1923_);
lean_dec_ref(v_type_1779_);
v___x_1928_ = lean_box(0);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1928_);
v___x_1930_ = v___x_1925_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
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
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec_ref(v_type_1779_);
v_a_1933_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1922_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1922_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec_ref(v_type_1779_);
v_a_1941_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1909_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1909_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
v___jp_1791_:
{
lean_object* v___x_1805_; 
lean_inc_ref(v___y_1793_);
lean_inc_ref(v_type_1779_);
lean_inc(v___y_1794_);
v___x_1805_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v___y_1794_, v_type_1779_, v___y_1793_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1805_, 1);
v___x_1807_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_1795_, v___y_1803_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v_ncRings_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___f_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v___x_1807_, 1);
v_ncRings_1809_ = lean_ctor_get(v_a_1808_, 6);
lean_inc_ref(v_ncRings_1809_);
lean_dec(v_a_1808_);
v___x_1810_ = lean_array_get_size(v_ncRings_1809_);
lean_dec_ref(v_ncRings_1809_);
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_unsigned_to_nat(32u);
v___x_1813_ = lean_mk_empty_array_with_capacity(v___x_1812_);
lean_dec_ref(v___x_1813_);
v___x_1814_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1);
v___x_1815_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3);
v___x_1816_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1810_);
lean_ctor_set(v___x_1816_, 1, v_type_1779_);
lean_ctor_set(v___x_1816_, 2, v___y_1794_);
lean_ctor_set(v___x_1816_, 3, v___y_1792_);
lean_ctor_set(v___x_1816_, 4, v___y_1793_);
lean_ctor_set(v___x_1816_, 5, v_a_1806_);
lean_ctor_set(v___x_1816_, 6, v___x_1811_);
lean_ctor_set(v___x_1816_, 7, v___x_1811_);
lean_ctor_set(v___x_1816_, 8, v___x_1811_);
lean_ctor_set(v___x_1816_, 9, v___x_1811_);
lean_ctor_set(v___x_1816_, 10, v___x_1811_);
lean_ctor_set(v___x_1816_, 11, v___x_1811_);
lean_ctor_set(v___x_1816_, 12, v___x_1811_);
lean_ctor_set(v___x_1816_, 13, v___x_1811_);
lean_ctor_set(v___x_1816_, 14, v___x_1814_);
lean_ctor_set(v___x_1816_, 15, v___x_1815_);
lean_ctor_set(v___x_1816_, 16, v___x_1815_);
v___f_1817_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1817_, 0, v___x_1816_);
v___x_1818_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1819_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1818_, v___f_1817_, v___y_1795_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1827_; 
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v___x_1819_, 0);
lean_dec(v_unused_1828_);
v___x_1821_ = v___x_1819_;
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
else
{
lean_dec(v___x_1819_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1810_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v_a_1829_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1819_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1819_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec(v_a_1806_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v_type_1779_);
v_a_1837_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1807_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1807_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v_type_1779_);
v_a_1845_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1805_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1805_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
v___jp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5));
v___x_1856_ = lean_box(0);
lean_inc(v_val_1854_);
v___x_1857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1857_, 0, v_val_1854_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
lean_inc_ref(v___x_1857_);
v___x_1858_ = l_Lean_mkConst(v___x_1855_, v___x_1857_);
lean_inc_ref(v_type_1779_);
v___x_1859_ = l_Lean_Expr_app___override(v___x_1858_, v_type_1779_);
v___x_1860_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1859_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1900_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1900_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1900_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
if (lean_obj_tag(v_a_1861_) == 1)
{
lean_object* v_options_1865_; lean_object* v_val_1866_; lean_object* v_inheritedTraceOptions_1867_; uint8_t v_hasTrace_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_del_object(v___x_1863_);
v_options_1865_ = lean_ctor_get(v_a_1788_, 2);
v_val_1866_ = lean_ctor_get(v_a_1861_, 0);
lean_inc_n(v_val_1866_, 2);
lean_dec_ref_known(v_a_1861_, 1);
v_inheritedTraceOptions_1867_ = lean_ctor_get(v_a_1788_, 13);
v_hasTrace_1868_ = lean_ctor_get_uint8(v_options_1865_, sizeof(void*)*1);
v___x_1869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24));
v___x_1870_ = l_Lean_mkConst(v___x_1869_, v___x_1857_);
lean_inc_ref(v_type_1779_);
v___x_1871_ = l_Lean_mkAppB(v___x_1870_, v_type_1779_, v_val_1866_);
if (v_hasTrace_1868_ == 0)
{
v___y_1792_ = v_val_1866_;
v___y_1793_ = v___x_1871_;
v___y_1794_ = v_val_1854_;
v___y_1795_ = v_a_1780_;
v___y_1796_ = v_a_1781_;
v___y_1797_ = v_a_1782_;
v___y_1798_ = v_a_1783_;
v___y_1799_ = v_a_1784_;
v___y_1800_ = v_a_1785_;
v___y_1801_ = v_a_1786_;
v___y_1802_ = v_a_1787_;
v___y_1803_ = v_a_1788_;
v___y_1804_ = v_a_1789_;
goto v___jp_1791_;
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18));
v___x_1873_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48);
v___x_1874_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1867_, v_options_1865_, v___x_1873_);
if (v___x_1874_ == 0)
{
v___y_1792_ = v_val_1866_;
v___y_1793_ = v___x_1871_;
v___y_1794_ = v_val_1854_;
v___y_1795_ = v_a_1780_;
v___y_1796_ = v_a_1781_;
v___y_1797_ = v_a_1782_;
v___y_1798_ = v_a_1783_;
v___y_1799_ = v_a_1784_;
v___y_1800_ = v_a_1785_;
v___y_1801_ = v_a_1786_;
v___y_1802_ = v_a_1787_;
v___y_1803_ = v_a_1788_;
v___y_1804_ = v_a_1789_;
goto v___jp_1791_;
}
else
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_Meta_Grind_updateLastTag(v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_dec_ref_known(v___x_1875_, 1);
v___x_1876_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28);
lean_inc_ref(v_type_1779_);
v___x_1877_ = l_Lean_MessageData_ofExpr(v_type_1779_);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_1872_, v___x_1878_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_dec_ref_known(v___x_1879_, 1);
v___y_1792_ = v_val_1866_;
v___y_1793_ = v___x_1871_;
v___y_1794_ = v_val_1854_;
v___y_1795_ = v_a_1780_;
v___y_1796_ = v_a_1781_;
v___y_1797_ = v_a_1782_;
v___y_1798_ = v_a_1783_;
v___y_1799_ = v_a_1784_;
v___y_1800_ = v_a_1785_;
v___y_1801_ = v_a_1786_;
v___y_1802_ = v_a_1787_;
v___y_1803_ = v_a_1788_;
v___y_1804_ = v_a_1789_;
goto v___jp_1791_;
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v___x_1871_);
lean_dec(v_val_1866_);
lean_dec(v_val_1854_);
lean_dec_ref(v_type_1779_);
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v___x_1871_);
lean_dec(v_val_1866_);
lean_dec(v_val_1854_);
lean_dec_ref(v_type_1779_);
v_a_1888_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1875_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1875_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1898_; 
lean_dec(v_a_1861_);
lean_dec_ref_known(v___x_1857_, 2);
lean_dec(v_val_1854_);
lean_dec_ref(v_type_1779_);
v___x_1896_ = lean_box(0);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1896_);
v___x_1898_ = v___x_1863_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec_ref_known(v___x_1857_, 2);
lean_dec(v_val_1854_);
lean_dec_ref(v_type_1779_);
v_a_1901_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1860_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1860_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___boxed(lean_object* v_type_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec(v_a_1950_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0(lean_object* v_type_1962_, lean_object* v_a_1963_, lean_object* v_s_1964_){
_start:
{
lean_object* v_rings_1965_; lean_object* v_typeIdOf_1966_; lean_object* v_exprToRingId_1967_; lean_object* v_semirings_1968_; lean_object* v_stypeIdOf_1969_; lean_object* v_exprToSemiringId_1970_; lean_object* v_ncRings_1971_; lean_object* v_exprToNCRingId_1972_; lean_object* v_nctypeIdOf_1973_; lean_object* v_ncSemirings_1974_; lean_object* v_exprToNCSemiringId_1975_; lean_object* v_ncstypeIdOf_1976_; lean_object* v_steps_1977_; uint8_t v_reportedMaxDegreeIssue_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1986_; 
v_rings_1965_ = lean_ctor_get(v_s_1964_, 0);
v_typeIdOf_1966_ = lean_ctor_get(v_s_1964_, 1);
v_exprToRingId_1967_ = lean_ctor_get(v_s_1964_, 2);
v_semirings_1968_ = lean_ctor_get(v_s_1964_, 3);
v_stypeIdOf_1969_ = lean_ctor_get(v_s_1964_, 4);
v_exprToSemiringId_1970_ = lean_ctor_get(v_s_1964_, 5);
v_ncRings_1971_ = lean_ctor_get(v_s_1964_, 6);
v_exprToNCRingId_1972_ = lean_ctor_get(v_s_1964_, 7);
v_nctypeIdOf_1973_ = lean_ctor_get(v_s_1964_, 8);
v_ncSemirings_1974_ = lean_ctor_get(v_s_1964_, 9);
v_exprToNCSemiringId_1975_ = lean_ctor_get(v_s_1964_, 10);
v_ncstypeIdOf_1976_ = lean_ctor_get(v_s_1964_, 11);
v_steps_1977_ = lean_ctor_get(v_s_1964_, 12);
v_reportedMaxDegreeIssue_1978_ = lean_ctor_get_uint8(v_s_1964_, sizeof(void*)*13);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_s_1964_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1980_ = v_s_1964_;
v_isShared_1981_ = v_isSharedCheck_1986_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_steps_1977_);
lean_inc(v_ncstypeIdOf_1976_);
lean_inc(v_exprToNCSemiringId_1975_);
lean_inc(v_ncSemirings_1974_);
lean_inc(v_nctypeIdOf_1973_);
lean_inc(v_exprToNCRingId_1972_);
lean_inc(v_ncRings_1971_);
lean_inc(v_exprToSemiringId_1970_);
lean_inc(v_stypeIdOf_1969_);
lean_inc(v_semirings_1968_);
lean_inc(v_exprToRingId_1967_);
lean_inc(v_typeIdOf_1966_);
lean_inc(v_rings_1965_);
lean_dec(v_s_1964_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1986_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_nctypeIdOf_1973_, v_type_1962_, v_a_1963_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 8, v___x_1982_);
v___x_1984_ = v___x_1980_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_rings_1965_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_typeIdOf_1966_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_exprToRingId_1967_);
lean_ctor_set(v_reuseFailAlloc_1985_, 3, v_semirings_1968_);
lean_ctor_set(v_reuseFailAlloc_1985_, 4, v_stypeIdOf_1969_);
lean_ctor_set(v_reuseFailAlloc_1985_, 5, v_exprToSemiringId_1970_);
lean_ctor_set(v_reuseFailAlloc_1985_, 6, v_ncRings_1971_);
lean_ctor_set(v_reuseFailAlloc_1985_, 7, v_exprToNCRingId_1972_);
lean_ctor_set(v_reuseFailAlloc_1985_, 8, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1985_, 9, v_ncSemirings_1974_);
lean_ctor_set(v_reuseFailAlloc_1985_, 10, v_exprToNCSemiringId_1975_);
lean_ctor_set(v_reuseFailAlloc_1985_, 11, v_ncstypeIdOf_1976_);
lean_ctor_set(v_reuseFailAlloc_1985_, 12, v_steps_1977_);
lean_ctor_set_uint8(v_reuseFailAlloc_1985_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1978_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object* v_type_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1988_, v_a_1996_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2031_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2031_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2031_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v_nctypeIdOf_2004_; lean_object* v___x_2005_; 
v_nctypeIdOf_2004_ = lean_ctor_get(v_a_2000_, 8);
lean_inc_ref(v_nctypeIdOf_2004_);
lean_dec(v_a_2000_);
v___x_2005_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_nctypeIdOf_2004_, v_type_1987_);
lean_dec_ref(v_nctypeIdOf_2004_);
if (lean_obj_tag(v___x_2005_) == 1)
{
lean_object* v_val_2006_; lean_object* v___x_2008_; 
lean_dec_ref(v_type_1987_);
v_val_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_val_2006_);
lean_dec_ref_known(v___x_2005_, 1);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v_val_2006_);
v___x_2008_ = v___x_2002_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_val_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
else
{
lean_object* v___x_2010_; 
lean_dec(v___x_2005_);
lean_del_object(v___x_2002_);
lean_inc_ref(v_type_1987_);
v___x_2010_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___f_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc_n(v_a_2011_, 2);
lean_dec_ref_known(v___x_2010_, 1);
v___f_2012_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2012_, 0, v_type_1987_);
lean_closure_set(v___f_2012_, 1, v_a_2011_);
v___x_2013_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2014_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2013_, v___f_2012_, v_a_1988_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2021_ == 0)
{
lean_object* v_unused_2022_; 
v_unused_2022_ = lean_ctor_get(v___x_2014_, 0);
lean_dec(v_unused_2022_);
v___x_2016_ = v___x_2014_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_dec(v___x_2014_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v_a_2011_);
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2011_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec(v_a_2011_);
v_a_2023_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2014_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2014_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_dec_ref(v_type_1987_);
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec_ref(v_type_1987_);
v_a_2032_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1999_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1999_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___boxed(lean_object* v_type_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_type_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v_a_2042_);
lean_dec(v_a_2041_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0(lean_object* v_semiringId_2053_, lean_object* v_s_2054_){
_start:
{
lean_object* v_toRing_2055_; lean_object* v_invFn_x3f_2056_; lean_object* v_commSemiringInst_2057_; lean_object* v_commRingInst_2058_; lean_object* v_noZeroDivInst_x3f_2059_; lean_object* v_fieldInst_x3f_2060_; lean_object* v_powIdentityInst_x3f_2061_; lean_object* v_denoteEntries_2062_; lean_object* v_nextId_2063_; lean_object* v_steps_2064_; lean_object* v_queue_2065_; lean_object* v_basis_2066_; lean_object* v_diseqs_2067_; uint8_t v_recheck_2068_; lean_object* v_invSet_2069_; lean_object* v_powIdentityVarCount_2070_; lean_object* v_numEq0_x3f_2071_; uint8_t v_numEq0Updated_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2080_; 
v_toRing_2055_ = lean_ctor_get(v_s_2054_, 0);
v_invFn_x3f_2056_ = lean_ctor_get(v_s_2054_, 1);
v_commSemiringInst_2057_ = lean_ctor_get(v_s_2054_, 3);
v_commRingInst_2058_ = lean_ctor_get(v_s_2054_, 4);
v_noZeroDivInst_x3f_2059_ = lean_ctor_get(v_s_2054_, 5);
v_fieldInst_x3f_2060_ = lean_ctor_get(v_s_2054_, 6);
v_powIdentityInst_x3f_2061_ = lean_ctor_get(v_s_2054_, 7);
v_denoteEntries_2062_ = lean_ctor_get(v_s_2054_, 8);
v_nextId_2063_ = lean_ctor_get(v_s_2054_, 9);
v_steps_2064_ = lean_ctor_get(v_s_2054_, 10);
v_queue_2065_ = lean_ctor_get(v_s_2054_, 11);
v_basis_2066_ = lean_ctor_get(v_s_2054_, 12);
v_diseqs_2067_ = lean_ctor_get(v_s_2054_, 13);
v_recheck_2068_ = lean_ctor_get_uint8(v_s_2054_, sizeof(void*)*17);
v_invSet_2069_ = lean_ctor_get(v_s_2054_, 14);
v_powIdentityVarCount_2070_ = lean_ctor_get(v_s_2054_, 15);
v_numEq0_x3f_2071_ = lean_ctor_get(v_s_2054_, 16);
v_numEq0Updated_2072_ = lean_ctor_get_uint8(v_s_2054_, sizeof(void*)*17 + 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_s_2054_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; 
v_unused_2081_ = lean_ctor_get(v_s_2054_, 2);
lean_dec(v_unused_2081_);
v___x_2074_ = v_s_2054_;
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_numEq0_x3f_2071_);
lean_inc(v_powIdentityVarCount_2070_);
lean_inc(v_invSet_2069_);
lean_inc(v_diseqs_2067_);
lean_inc(v_basis_2066_);
lean_inc(v_queue_2065_);
lean_inc(v_steps_2064_);
lean_inc(v_nextId_2063_);
lean_inc(v_denoteEntries_2062_);
lean_inc(v_powIdentityInst_x3f_2061_);
lean_inc(v_fieldInst_x3f_2060_);
lean_inc(v_noZeroDivInst_x3f_2059_);
lean_inc(v_commRingInst_2058_);
lean_inc(v_commSemiringInst_2057_);
lean_inc(v_invFn_x3f_2056_);
lean_inc(v_toRing_2055_);
lean_dec(v_s_2054_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2080_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2076_, 0, v_semiringId_2053_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 2, v___x_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_toRing_2055_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_invFn_x3f_2056_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_commSemiringInst_2057_);
lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_commRingInst_2058_);
lean_ctor_set(v_reuseFailAlloc_2079_, 5, v_noZeroDivInst_x3f_2059_);
lean_ctor_set(v_reuseFailAlloc_2079_, 6, v_fieldInst_x3f_2060_);
lean_ctor_set(v_reuseFailAlloc_2079_, 7, v_powIdentityInst_x3f_2061_);
lean_ctor_set(v_reuseFailAlloc_2079_, 8, v_denoteEntries_2062_);
lean_ctor_set(v_reuseFailAlloc_2079_, 9, v_nextId_2063_);
lean_ctor_set(v_reuseFailAlloc_2079_, 10, v_steps_2064_);
lean_ctor_set(v_reuseFailAlloc_2079_, 11, v_queue_2065_);
lean_ctor_set(v_reuseFailAlloc_2079_, 12, v_basis_2066_);
lean_ctor_set(v_reuseFailAlloc_2079_, 13, v_diseqs_2067_);
lean_ctor_set(v_reuseFailAlloc_2079_, 14, v_invSet_2069_);
lean_ctor_set(v_reuseFailAlloc_2079_, 15, v_powIdentityVarCount_2070_);
lean_ctor_set(v_reuseFailAlloc_2079_, 16, v_numEq0_x3f_2071_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, sizeof(void*)*17, v_recheck_2068_);
lean_ctor_set_uint8(v_reuseFailAlloc_2079_, sizeof(void*)*17 + 1, v_numEq0Updated_2072_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(lean_object* v_ringId_2082_, lean_object* v_semiringId_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v___f_2086_; uint8_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___f_2086_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2086_, 0, v_semiringId_2083_);
v___x_2087_ = 0;
v___x_2088_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2088_, 0, v_ringId_2082_);
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*1, v___x_2087_);
v___x_2089_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2086_, v___x_2088_, v_a_2084_);
lean_dec_ref_known(v___x_2088_, 1);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___boxed(lean_object* v_ringId_2090_, lean_object* v_semiringId_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_2090_, v_semiringId_2091_, v_a_2092_);
lean_dec(v_a_2092_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(lean_object* v_ringId_2095_, lean_object* v_semiringId_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_2095_, v_semiringId_2096_, v_a_2097_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___boxed(lean_object* v_ringId_2109_, lean_object* v_semiringId_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(v_ringId_2109_, v_semiringId_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
lean_dec(v_a_2111_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0(lean_object* v___x_2123_, lean_object* v_s_2124_){
_start:
{
lean_object* v_rings_2125_; lean_object* v_typeIdOf_2126_; lean_object* v_exprToRingId_2127_; lean_object* v_semirings_2128_; lean_object* v_stypeIdOf_2129_; lean_object* v_exprToSemiringId_2130_; lean_object* v_ncRings_2131_; lean_object* v_exprToNCRingId_2132_; lean_object* v_nctypeIdOf_2133_; lean_object* v_ncSemirings_2134_; lean_object* v_exprToNCSemiringId_2135_; lean_object* v_ncstypeIdOf_2136_; lean_object* v_steps_2137_; uint8_t v_reportedMaxDegreeIssue_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2146_; 
v_rings_2125_ = lean_ctor_get(v_s_2124_, 0);
v_typeIdOf_2126_ = lean_ctor_get(v_s_2124_, 1);
v_exprToRingId_2127_ = lean_ctor_get(v_s_2124_, 2);
v_semirings_2128_ = lean_ctor_get(v_s_2124_, 3);
v_stypeIdOf_2129_ = lean_ctor_get(v_s_2124_, 4);
v_exprToSemiringId_2130_ = lean_ctor_get(v_s_2124_, 5);
v_ncRings_2131_ = lean_ctor_get(v_s_2124_, 6);
v_exprToNCRingId_2132_ = lean_ctor_get(v_s_2124_, 7);
v_nctypeIdOf_2133_ = lean_ctor_get(v_s_2124_, 8);
v_ncSemirings_2134_ = lean_ctor_get(v_s_2124_, 9);
v_exprToNCSemiringId_2135_ = lean_ctor_get(v_s_2124_, 10);
v_ncstypeIdOf_2136_ = lean_ctor_get(v_s_2124_, 11);
v_steps_2137_ = lean_ctor_get(v_s_2124_, 12);
v_reportedMaxDegreeIssue_2138_ = lean_ctor_get_uint8(v_s_2124_, sizeof(void*)*13);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_s_2124_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2140_ = v_s_2124_;
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_steps_2137_);
lean_inc(v_ncstypeIdOf_2136_);
lean_inc(v_exprToNCSemiringId_2135_);
lean_inc(v_ncSemirings_2134_);
lean_inc(v_nctypeIdOf_2133_);
lean_inc(v_exprToNCRingId_2132_);
lean_inc(v_ncRings_2131_);
lean_inc(v_exprToSemiringId_2130_);
lean_inc(v_stypeIdOf_2129_);
lean_inc(v_semirings_2128_);
lean_inc(v_exprToRingId_2127_);
lean_inc(v_typeIdOf_2126_);
lean_inc(v_rings_2125_);
lean_dec(v_s_2124_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = lean_array_push(v_semirings_2128_, v___x_2123_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 3, v___x_2142_);
v___x_2144_ = v___x_2140_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_rings_2125_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_typeIdOf_2126_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_exprToRingId_2127_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v_stypeIdOf_2129_);
lean_ctor_set(v_reuseFailAlloc_2145_, 5, v_exprToSemiringId_2130_);
lean_ctor_set(v_reuseFailAlloc_2145_, 6, v_ncRings_2131_);
lean_ctor_set(v_reuseFailAlloc_2145_, 7, v_exprToNCRingId_2132_);
lean_ctor_set(v_reuseFailAlloc_2145_, 8, v_nctypeIdOf_2133_);
lean_ctor_set(v_reuseFailAlloc_2145_, 9, v_ncSemirings_2134_);
lean_ctor_set(v_reuseFailAlloc_2145_, 10, v_exprToNCSemiringId_2135_);
lean_ctor_set(v_reuseFailAlloc_2145_, 11, v_ncstypeIdOf_2136_);
lean_ctor_set(v_reuseFailAlloc_2145_, 12, v_steps_2137_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2138_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_ref_2153_; lean_object* v___x_2154_; lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2163_; 
v_ref_2153_ = lean_ctor_get(v___y_2150_, 5);
v___x_2154_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(v_msg_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2157_ = v___x_2154_;
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_inc(v_ref_2153_);
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v_ref_2153_);
lean_ctor_set(v___x_2159_, 1, v_a_2155_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set_tag(v___x_2157_, 1);
lean_ctor_set(v___x_2157_, 0, v___x_2159_);
v___x_2161_ = v___x_2157_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
return v_res_2170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0(void){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2171_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0);
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
return v___x_2173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2));
v___x_2176_ = l_Lean_stringToMessageData(v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(lean_object* v_type_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v_val_2190_; lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_leCarrierIsSort(v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; uint8_t v___x_2302_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2300_, 1);
v___x_2302_ = lean_unbox(v_a_2301_);
lean_dec(v_a_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; 
lean_inc_ref(v_type_2177_);
v___x_2303_ = l_Lean_Meta_getDecLevel(v_type_2177_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v_val_2190_ = v_a_2304_;
goto v___jp_2189_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v_type_2177_);
v_a_2305_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2303_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2303_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v___x_2313_; 
lean_inc_ref(v_type_2177_);
v___x_2313_ = l_Lean_Meta_getDecLevel_x3f(v_type_2177_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2323_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2323_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2323_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
if (lean_obj_tag(v_a_2314_) == 1)
{
lean_object* v_val_2318_; 
lean_del_object(v___x_2316_);
v_val_2318_ = lean_ctor_get(v_a_2314_, 0);
lean_inc(v_val_2318_);
lean_dec_ref_known(v_a_2314_, 1);
v_val_2190_ = v_val_2318_;
goto v___jp_2189_;
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
lean_dec(v_a_2314_);
lean_dec_ref(v_type_2177_);
v___x_2319_ = lean_box(0);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2319_);
v___x_2321_ = v___x_2316_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_type_2177_);
v_a_2324_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2313_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2313_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_type_2177_);
v_a_2332_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2300_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2300_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
v___jp_2189_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8));
v___x_2192_ = lean_box(0);
lean_inc(v_val_2190_);
v___x_2193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2193_, 0, v_val_2190_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
lean_inc_ref(v___x_2193_);
v___x_2194_ = l_Lean_mkConst(v___x_2191_, v___x_2193_);
lean_inc_ref(v_type_2177_);
v___x_2195_ = l_Lean_Expr_app___override(v___x_2194_, v_type_2177_);
v___x_2196_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2195_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2291_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2291_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2291_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
if (lean_obj_tag(v_a_2197_) == 1)
{
lean_object* v_val_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_del_object(v___x_2199_);
v_val_2201_ = lean_ctor_get(v_a_2197_, 0);
lean_inc_n(v_val_2201_, 2);
lean_dec_ref_known(v_a_2197_, 1);
v___x_2202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1));
lean_inc_ref(v___x_2193_);
v___x_2203_ = l_Lean_mkConst(v___x_2202_, v___x_2193_);
lean_inc_ref_n(v_type_2177_, 2);
v___x_2204_ = l_Lean_mkAppB(v___x_2203_, v_type_2177_, v_val_2201_);
v___x_2205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1));
v___x_2206_ = l_Lean_mkConst(v___x_2205_, v___x_2193_);
lean_inc_ref(v___x_2204_);
v___x_2207_ = l_Lean_mkAppB(v___x_2206_, v_type_2177_, v___x_2204_);
v___x_2208_ = l_Lean_Meta_Sym_canon(v___x_2207_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2210_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2208_, 1);
v___x_2210_ = l_Lean_Meta_Sym_shareCommon(v_a_2209_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2212_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc_n(v_a_2211_, 2);
lean_dec_ref_known(v___x_2210_, 1);
v___x_2212_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_a_2211_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
if (lean_obj_tag(v_a_2213_) == 1)
{
lean_object* v_val_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_a_2211_);
v_val_2214_ = lean_ctor_get(v_a_2213_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_a_2213_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2216_ = v_a_2213_;
v_isShared_2217_ = v_isSharedCheck_2266_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_val_2214_);
lean_dec(v_a_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2266_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2178_, v_a_2186_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v_semirings_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___f_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v_semirings_2220_ = lean_ctor_get(v_a_2219_, 3);
lean_inc_ref(v_semirings_2220_);
lean_dec(v_a_2219_);
v___x_2221_ = lean_array_get_size(v_semirings_2220_);
lean_dec_ref(v_semirings_2220_);
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1);
v___x_2224_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1);
v___x_2225_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2221_);
lean_ctor_set(v___x_2225_, 1, v_type_2177_);
lean_ctor_set(v___x_2225_, 2, v_val_2190_);
lean_ctor_set(v___x_2225_, 3, v___x_2204_);
lean_ctor_set(v___x_2225_, 4, v___x_2222_);
lean_ctor_set(v___x_2225_, 5, v___x_2222_);
lean_ctor_set(v___x_2225_, 6, v___x_2222_);
lean_ctor_set(v___x_2225_, 7, v___x_2222_);
lean_ctor_set(v___x_2225_, 8, v___x_2223_);
lean_ctor_set(v___x_2225_, 9, v___x_2224_);
lean_ctor_set(v___x_2225_, 10, v___x_2223_);
lean_inc(v_val_2214_);
v___x_2226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v_val_2214_);
lean_ctor_set(v___x_2226_, 2, v_val_2201_);
lean_ctor_set(v___x_2226_, 3, v___x_2222_);
lean_ctor_set(v___x_2226_, 4, v___x_2222_);
v___f_2227_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_2227_, 0, v___x_2226_);
v___x_2228_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2229_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2228_, v___f_2227_, v_a_2178_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v___x_2230_; 
lean_dec_ref_known(v___x_2229_, 1);
v___x_2230_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_val_2214_, v___x_2221_, v_a_2178_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2240_; 
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; 
v_unused_2241_ = lean_ctor_get(v___x_2230_, 0);
lean_dec(v_unused_2241_);
v___x_2232_ = v___x_2230_;
v_isShared_2233_ = v_isSharedCheck_2240_;
goto v_resetjp_2231_;
}
else
{
lean_dec(v___x_2230_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2240_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2221_);
v___x_2235_ = v___x_2216_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2221_);
v___x_2235_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2237_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2235_);
v___x_2237_ = v___x_2232_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_del_object(v___x_2216_);
v_a_2242_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2230_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2230_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_del_object(v___x_2216_);
lean_dec(v_val_2214_);
v_a_2250_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2229_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2229_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_del_object(v___x_2216_);
lean_dec(v_val_2214_);
lean_dec_ref(v___x_2204_);
lean_dec(v_val_2201_);
lean_dec(v_val_2190_);
lean_dec_ref(v_type_2177_);
v_a_2258_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2218_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2218_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec(v_a_2213_);
lean_dec_ref(v___x_2204_);
lean_dec(v_val_2201_);
lean_dec(v_val_2190_);
lean_dec_ref(v_type_2177_);
v___x_2267_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3);
v___x_2268_ = l_Lean_indentExpr(v_a_2211_);
v___x_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v___x_2269_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
return v___x_2270_;
}
}
else
{
lean_dec(v_a_2211_);
lean_dec_ref(v___x_2204_);
lean_dec(v_val_2201_);
lean_dec(v_val_2190_);
lean_dec_ref(v_type_2177_);
return v___x_2212_;
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec_ref(v___x_2204_);
lean_dec(v_val_2201_);
lean_dec(v_val_2190_);
lean_dec_ref(v_type_2177_);
v_a_2271_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2210_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2210_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec_ref(v___x_2204_);
lean_dec(v_val_2201_);
lean_dec(v_val_2190_);
lean_dec_ref(v_type_2177_);
v_a_2279_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2208_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2208_);
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
else
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
lean_dec(v_a_2197_);
lean_dec_ref_known(v___x_2193_, 2);
lean_dec(v_val_2190_);
lean_dec_ref(v_type_2177_);
v___x_2287_ = lean_box(0);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2287_);
v___x_2289_ = v___x_2199_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
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
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref_known(v___x_2193_, 2);
lean_dec(v_val_2190_);
lean_dec_ref(v_type_2177_);
v_a_2292_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2196_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2196_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___boxed(lean_object* v_type_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec(v_a_2342_);
lean_dec(v_a_2341_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_2353_, lean_object* v_msg_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_2354_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_2367_, lean_object* v_msg_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(v_00_u03b1_2367_, v_msg_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec(v___y_2369_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0(lean_object* v_type_2381_, lean_object* v_a_2382_, lean_object* v_s_2383_){
_start:
{
lean_object* v_rings_2384_; lean_object* v_typeIdOf_2385_; lean_object* v_exprToRingId_2386_; lean_object* v_semirings_2387_; lean_object* v_stypeIdOf_2388_; lean_object* v_exprToSemiringId_2389_; lean_object* v_ncRings_2390_; lean_object* v_exprToNCRingId_2391_; lean_object* v_nctypeIdOf_2392_; lean_object* v_ncSemirings_2393_; lean_object* v_exprToNCSemiringId_2394_; lean_object* v_ncstypeIdOf_2395_; lean_object* v_steps_2396_; uint8_t v_reportedMaxDegreeIssue_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2405_; 
v_rings_2384_ = lean_ctor_get(v_s_2383_, 0);
v_typeIdOf_2385_ = lean_ctor_get(v_s_2383_, 1);
v_exprToRingId_2386_ = lean_ctor_get(v_s_2383_, 2);
v_semirings_2387_ = lean_ctor_get(v_s_2383_, 3);
v_stypeIdOf_2388_ = lean_ctor_get(v_s_2383_, 4);
v_exprToSemiringId_2389_ = lean_ctor_get(v_s_2383_, 5);
v_ncRings_2390_ = lean_ctor_get(v_s_2383_, 6);
v_exprToNCRingId_2391_ = lean_ctor_get(v_s_2383_, 7);
v_nctypeIdOf_2392_ = lean_ctor_get(v_s_2383_, 8);
v_ncSemirings_2393_ = lean_ctor_get(v_s_2383_, 9);
v_exprToNCSemiringId_2394_ = lean_ctor_get(v_s_2383_, 10);
v_ncstypeIdOf_2395_ = lean_ctor_get(v_s_2383_, 11);
v_steps_2396_ = lean_ctor_get(v_s_2383_, 12);
v_reportedMaxDegreeIssue_2397_ = lean_ctor_get_uint8(v_s_2383_, sizeof(void*)*13);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_s_2383_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2399_ = v_s_2383_;
v_isShared_2400_ = v_isSharedCheck_2405_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_steps_2396_);
lean_inc(v_ncstypeIdOf_2395_);
lean_inc(v_exprToNCSemiringId_2394_);
lean_inc(v_ncSemirings_2393_);
lean_inc(v_nctypeIdOf_2392_);
lean_inc(v_exprToNCRingId_2391_);
lean_inc(v_ncRings_2390_);
lean_inc(v_exprToSemiringId_2389_);
lean_inc(v_stypeIdOf_2388_);
lean_inc(v_semirings_2387_);
lean_inc(v_exprToRingId_2386_);
lean_inc(v_typeIdOf_2385_);
lean_inc(v_rings_2384_);
lean_dec(v_s_2383_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2405_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2401_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_stypeIdOf_2388_, v_type_2381_, v_a_2382_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 4, v___x_2401_);
v___x_2403_ = v___x_2399_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_rings_2384_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_typeIdOf_2385_);
lean_ctor_set(v_reuseFailAlloc_2404_, 2, v_exprToRingId_2386_);
lean_ctor_set(v_reuseFailAlloc_2404_, 3, v_semirings_2387_);
lean_ctor_set(v_reuseFailAlloc_2404_, 4, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2404_, 5, v_exprToSemiringId_2389_);
lean_ctor_set(v_reuseFailAlloc_2404_, 6, v_ncRings_2390_);
lean_ctor_set(v_reuseFailAlloc_2404_, 7, v_exprToNCRingId_2391_);
lean_ctor_set(v_reuseFailAlloc_2404_, 8, v_nctypeIdOf_2392_);
lean_ctor_set(v_reuseFailAlloc_2404_, 9, v_ncSemirings_2393_);
lean_ctor_set(v_reuseFailAlloc_2404_, 10, v_exprToNCSemiringId_2394_);
lean_ctor_set(v_reuseFailAlloc_2404_, 11, v_ncstypeIdOf_2395_);
lean_ctor_set(v_reuseFailAlloc_2404_, 12, v_steps_2396_);
lean_ctor_set_uint8(v_reuseFailAlloc_2404_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2397_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object* v_type_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2407_, v_a_2415_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2450_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2450_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2450_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v_stypeIdOf_2423_; lean_object* v___x_2424_; 
v_stypeIdOf_2423_ = lean_ctor_get(v_a_2419_, 4);
lean_inc_ref(v_stypeIdOf_2423_);
lean_dec(v_a_2419_);
v___x_2424_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_stypeIdOf_2423_, v_type_2406_);
lean_dec_ref(v_stypeIdOf_2423_);
if (lean_obj_tag(v___x_2424_) == 1)
{
lean_object* v_val_2425_; lean_object* v___x_2427_; 
lean_dec_ref(v_type_2406_);
v_val_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_val_2425_);
lean_dec_ref_known(v___x_2424_, 1);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v_val_2425_);
v___x_2427_ = v___x_2421_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_val_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
else
{
lean_object* v___x_2429_; 
lean_dec(v___x_2424_);
lean_del_object(v___x_2421_);
lean_inc_ref(v_type_2406_);
v___x_2429_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___f_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc_n(v_a_2430_, 2);
lean_dec_ref_known(v___x_2429_, 1);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2431_, 0, v_type_2406_);
lean_closure_set(v___f_2431_, 1, v_a_2430_);
v___x_2432_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2433_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2432_, v___f_2431_, v_a_2407_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2440_ == 0)
{
lean_object* v_unused_2441_; 
v_unused_2441_ = lean_ctor_get(v___x_2433_, 0);
lean_dec(v_unused_2441_);
v___x_2435_ = v___x_2433_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_dec(v___x_2433_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v_a_2430_);
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2430_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_a_2430_);
v_a_2442_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2433_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2433_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
else
{
lean_dec_ref(v_type_2406_);
return v___x_2429_;
}
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec_ref(v_type_2406_);
v_a_2451_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2418_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2418_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___boxed(lean_object* v_type_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_type_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec(v_a_2460_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0(lean_object* v___x_2472_, lean_object* v_s_2473_){
_start:
{
lean_object* v_rings_2474_; lean_object* v_typeIdOf_2475_; lean_object* v_exprToRingId_2476_; lean_object* v_semirings_2477_; lean_object* v_stypeIdOf_2478_; lean_object* v_exprToSemiringId_2479_; lean_object* v_ncRings_2480_; lean_object* v_exprToNCRingId_2481_; lean_object* v_nctypeIdOf_2482_; lean_object* v_ncSemirings_2483_; lean_object* v_exprToNCSemiringId_2484_; lean_object* v_ncstypeIdOf_2485_; lean_object* v_steps_2486_; uint8_t v_reportedMaxDegreeIssue_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2495_; 
v_rings_2474_ = lean_ctor_get(v_s_2473_, 0);
v_typeIdOf_2475_ = lean_ctor_get(v_s_2473_, 1);
v_exprToRingId_2476_ = lean_ctor_get(v_s_2473_, 2);
v_semirings_2477_ = lean_ctor_get(v_s_2473_, 3);
v_stypeIdOf_2478_ = lean_ctor_get(v_s_2473_, 4);
v_exprToSemiringId_2479_ = lean_ctor_get(v_s_2473_, 5);
v_ncRings_2480_ = lean_ctor_get(v_s_2473_, 6);
v_exprToNCRingId_2481_ = lean_ctor_get(v_s_2473_, 7);
v_nctypeIdOf_2482_ = lean_ctor_get(v_s_2473_, 8);
v_ncSemirings_2483_ = lean_ctor_get(v_s_2473_, 9);
v_exprToNCSemiringId_2484_ = lean_ctor_get(v_s_2473_, 10);
v_ncstypeIdOf_2485_ = lean_ctor_get(v_s_2473_, 11);
v_steps_2486_ = lean_ctor_get(v_s_2473_, 12);
v_reportedMaxDegreeIssue_2487_ = lean_ctor_get_uint8(v_s_2473_, sizeof(void*)*13);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_s_2473_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2489_ = v_s_2473_;
v_isShared_2490_ = v_isSharedCheck_2495_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_steps_2486_);
lean_inc(v_ncstypeIdOf_2485_);
lean_inc(v_exprToNCSemiringId_2484_);
lean_inc(v_ncSemirings_2483_);
lean_inc(v_nctypeIdOf_2482_);
lean_inc(v_exprToNCRingId_2481_);
lean_inc(v_ncRings_2480_);
lean_inc(v_exprToSemiringId_2479_);
lean_inc(v_stypeIdOf_2478_);
lean_inc(v_semirings_2477_);
lean_inc(v_exprToRingId_2476_);
lean_inc(v_typeIdOf_2475_);
lean_inc(v_rings_2474_);
lean_dec(v_s_2473_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2495_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2491_ = lean_array_push(v_ncSemirings_2483_, v___x_2472_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 9, v___x_2491_);
v___x_2493_ = v___x_2489_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_rings_2474_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_typeIdOf_2475_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_exprToRingId_2476_);
lean_ctor_set(v_reuseFailAlloc_2494_, 3, v_semirings_2477_);
lean_ctor_set(v_reuseFailAlloc_2494_, 4, v_stypeIdOf_2478_);
lean_ctor_set(v_reuseFailAlloc_2494_, 5, v_exprToSemiringId_2479_);
lean_ctor_set(v_reuseFailAlloc_2494_, 6, v_ncRings_2480_);
lean_ctor_set(v_reuseFailAlloc_2494_, 7, v_exprToNCRingId_2481_);
lean_ctor_set(v_reuseFailAlloc_2494_, 8, v_nctypeIdOf_2482_);
lean_ctor_set(v_reuseFailAlloc_2494_, 9, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2494_, 10, v_exprToNCSemiringId_2484_);
lean_ctor_set(v_reuseFailAlloc_2494_, 11, v_ncstypeIdOf_2485_);
lean_ctor_set(v_reuseFailAlloc_2494_, 12, v_steps_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2494_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2487_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(lean_object* v_type_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v_val_2505_; lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_leCarrierIsSort(v_a_2501_, v_a_2502_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; uint8_t v___x_2576_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___x_2576_ = lean_unbox(v_a_2575_);
lean_dec(v_a_2575_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; 
lean_inc_ref(v_type_2496_);
v___x_2577_ = l_Lean_Meta_getDecLevel(v_type_2496_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref_known(v___x_2577_, 1);
v_val_2505_ = v_a_2578_;
goto v___jp_2504_;
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec_ref(v_type_2496_);
v_a_2579_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2577_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2577_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_object* v___x_2587_; 
lean_inc_ref(v_type_2496_);
v___x_2587_ = l_Lean_Meta_getDecLevel_x3f(v_type_2496_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2597_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2597_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2597_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
if (lean_obj_tag(v_a_2588_) == 1)
{
lean_object* v_val_2592_; 
lean_del_object(v___x_2590_);
v_val_2592_ = lean_ctor_get(v_a_2588_, 0);
lean_inc(v_val_2592_);
lean_dec_ref_known(v_a_2588_, 1);
v_val_2505_ = v_val_2592_;
goto v___jp_2504_;
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
lean_dec(v_a_2588_);
lean_dec_ref(v_type_2496_);
v___x_2593_ = lean_box(0);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2593_);
v___x_2595_ = v___x_2590_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec_ref(v_type_2496_);
v_a_2598_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2587_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2587_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref(v_type_2496_);
v_a_2606_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2574_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2574_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
v___jp_2504_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7));
v___x_2507_ = lean_box(0);
lean_inc(v_val_2505_);
v___x_2508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2508_, 0, v_val_2505_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = l_Lean_mkConst(v___x_2506_, v___x_2508_);
lean_inc_ref(v_type_2496_);
v___x_2510_ = l_Lean_Expr_app___override(v___x_2509_, v_type_2496_);
v___x_2511_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2510_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2565_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2565_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2565_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
if (lean_obj_tag(v_a_2512_) == 1)
{
lean_object* v_val_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2560_; 
lean_del_object(v___x_2514_);
v_val_2516_ = lean_ctor_get(v_a_2512_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_a_2512_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2518_ = v_a_2512_;
v_isShared_2519_ = v_isSharedCheck_2560_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_val_2516_);
lean_dec(v_a_2512_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2560_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2497_, v_a_2501_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v_ncSemirings_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___f_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v_ncSemirings_2522_ = lean_ctor_get(v_a_2521_, 9);
lean_inc_ref(v_ncSemirings_2522_);
lean_dec(v_a_2521_);
v___x_2523_ = lean_array_get_size(v_ncSemirings_2522_);
lean_dec_ref(v_ncSemirings_2522_);
v___x_2524_ = lean_box(0);
v___x_2525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1);
v___x_2526_ = lean_unsigned_to_nat(32u);
v___x_2527_ = lean_mk_empty_array_with_capacity(v___x_2526_);
lean_dec_ref(v___x_2527_);
v___x_2528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1);
v___x_2529_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2523_);
lean_ctor_set(v___x_2529_, 1, v_type_2496_);
lean_ctor_set(v___x_2529_, 2, v_val_2505_);
lean_ctor_set(v___x_2529_, 3, v_val_2516_);
lean_ctor_set(v___x_2529_, 4, v___x_2524_);
lean_ctor_set(v___x_2529_, 5, v___x_2524_);
lean_ctor_set(v___x_2529_, 6, v___x_2524_);
lean_ctor_set(v___x_2529_, 7, v___x_2524_);
lean_ctor_set(v___x_2529_, 8, v___x_2525_);
lean_ctor_set(v___x_2529_, 9, v___x_2528_);
lean_ctor_set(v___x_2529_, 10, v___x_2525_);
v___f_2530_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2530_, 0, v___x_2529_);
v___x_2531_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2532_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2531_, v___f_2530_, v_a_2497_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2542_; 
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2542_ == 0)
{
lean_object* v_unused_2543_; 
v_unused_2543_ = lean_ctor_get(v___x_2532_, 0);
lean_dec(v_unused_2543_);
v___x_2534_ = v___x_2532_;
v_isShared_2535_ = v_isSharedCheck_2542_;
goto v_resetjp_2533_;
}
else
{
lean_dec(v___x_2532_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2542_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2523_);
v___x_2537_ = v___x_2518_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2523_);
v___x_2537_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2539_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2537_);
v___x_2539_ = v___x_2534_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_del_object(v___x_2518_);
v_a_2544_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2532_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2532_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_del_object(v___x_2518_);
lean_dec(v_val_2516_);
lean_dec(v_val_2505_);
lean_dec_ref(v_type_2496_);
v_a_2552_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2520_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2520_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2563_; 
lean_dec(v_a_2512_);
lean_dec(v_val_2505_);
lean_dec_ref(v_type_2496_);
v___x_2561_ = lean_box(0);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2561_);
v___x_2563_ = v___x_2514_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_val_2505_);
lean_dec_ref(v_type_2496_);
v_a_2566_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2511_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2511_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___boxed(lean_object* v_type_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
lean_dec(v_a_2616_);
lean_dec(v_a_2615_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(lean_object* v_type_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_2623_, v_a_2624_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___boxed(lean_object* v_type_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(v_type_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec(v_a_2637_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0(lean_object* v_type_2649_, lean_object* v_a_2650_, lean_object* v_s_2651_){
_start:
{
lean_object* v_rings_2652_; lean_object* v_typeIdOf_2653_; lean_object* v_exprToRingId_2654_; lean_object* v_semirings_2655_; lean_object* v_stypeIdOf_2656_; lean_object* v_exprToSemiringId_2657_; lean_object* v_ncRings_2658_; lean_object* v_exprToNCRingId_2659_; lean_object* v_nctypeIdOf_2660_; lean_object* v_ncSemirings_2661_; lean_object* v_exprToNCSemiringId_2662_; lean_object* v_ncstypeIdOf_2663_; lean_object* v_steps_2664_; uint8_t v_reportedMaxDegreeIssue_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2673_; 
v_rings_2652_ = lean_ctor_get(v_s_2651_, 0);
v_typeIdOf_2653_ = lean_ctor_get(v_s_2651_, 1);
v_exprToRingId_2654_ = lean_ctor_get(v_s_2651_, 2);
v_semirings_2655_ = lean_ctor_get(v_s_2651_, 3);
v_stypeIdOf_2656_ = lean_ctor_get(v_s_2651_, 4);
v_exprToSemiringId_2657_ = lean_ctor_get(v_s_2651_, 5);
v_ncRings_2658_ = lean_ctor_get(v_s_2651_, 6);
v_exprToNCRingId_2659_ = lean_ctor_get(v_s_2651_, 7);
v_nctypeIdOf_2660_ = lean_ctor_get(v_s_2651_, 8);
v_ncSemirings_2661_ = lean_ctor_get(v_s_2651_, 9);
v_exprToNCSemiringId_2662_ = lean_ctor_get(v_s_2651_, 10);
v_ncstypeIdOf_2663_ = lean_ctor_get(v_s_2651_, 11);
v_steps_2664_ = lean_ctor_get(v_s_2651_, 12);
v_reportedMaxDegreeIssue_2665_ = lean_ctor_get_uint8(v_s_2651_, sizeof(void*)*13);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_s_2651_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2667_ = v_s_2651_;
v_isShared_2668_ = v_isSharedCheck_2673_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_steps_2664_);
lean_inc(v_ncstypeIdOf_2663_);
lean_inc(v_exprToNCSemiringId_2662_);
lean_inc(v_ncSemirings_2661_);
lean_inc(v_nctypeIdOf_2660_);
lean_inc(v_exprToNCRingId_2659_);
lean_inc(v_ncRings_2658_);
lean_inc(v_exprToSemiringId_2657_);
lean_inc(v_stypeIdOf_2656_);
lean_inc(v_semirings_2655_);
lean_inc(v_exprToRingId_2654_);
lean_inc(v_typeIdOf_2653_);
lean_inc(v_rings_2652_);
lean_dec(v_s_2651_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2673_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2669_; lean_object* v___x_2671_; 
v___x_2669_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_ncstypeIdOf_2663_, v_type_2649_, v_a_2650_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 11, v___x_2669_);
v___x_2671_ = v___x_2667_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_rings_2652_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_typeIdOf_2653_);
lean_ctor_set(v_reuseFailAlloc_2672_, 2, v_exprToRingId_2654_);
lean_ctor_set(v_reuseFailAlloc_2672_, 3, v_semirings_2655_);
lean_ctor_set(v_reuseFailAlloc_2672_, 4, v_stypeIdOf_2656_);
lean_ctor_set(v_reuseFailAlloc_2672_, 5, v_exprToSemiringId_2657_);
lean_ctor_set(v_reuseFailAlloc_2672_, 6, v_ncRings_2658_);
lean_ctor_set(v_reuseFailAlloc_2672_, 7, v_exprToNCRingId_2659_);
lean_ctor_set(v_reuseFailAlloc_2672_, 8, v_nctypeIdOf_2660_);
lean_ctor_set(v_reuseFailAlloc_2672_, 9, v_ncSemirings_2661_);
lean_ctor_set(v_reuseFailAlloc_2672_, 10, v_exprToNCSemiringId_2662_);
lean_ctor_set(v_reuseFailAlloc_2672_, 11, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2672_, 12, v_steps_2664_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2665_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object* v_type_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2675_, v_a_2679_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2714_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2714_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2714_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v_ncstypeIdOf_2687_; lean_object* v___x_2688_; 
v_ncstypeIdOf_2687_ = lean_ctor_get(v_a_2683_, 11);
lean_inc_ref(v_ncstypeIdOf_2687_);
lean_dec(v_a_2683_);
v___x_2688_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_ncstypeIdOf_2687_, v_type_2674_);
lean_dec_ref(v_ncstypeIdOf_2687_);
if (lean_obj_tag(v___x_2688_) == 1)
{
lean_object* v_val_2689_; lean_object* v___x_2691_; 
lean_dec_ref(v_type_2674_);
v_val_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_val_2689_);
lean_dec_ref_known(v___x_2688_, 1);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v_val_2689_);
v___x_2691_ = v___x_2685_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_val_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
else
{
lean_object* v___x_2693_; 
lean_dec(v___x_2688_);
lean_del_object(v___x_2685_);
lean_inc_ref(v_type_2674_);
v___x_2693_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___f_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc_n(v_a_2694_, 2);
lean_dec_ref_known(v___x_2693_, 1);
v___f_2695_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2695_, 0, v_type_2674_);
lean_closure_set(v___f_2695_, 1, v_a_2694_);
v___x_2696_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2697_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2696_, v___f_2695_, v_a_2675_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v___x_2697_, 0);
lean_dec(v_unused_2705_);
v___x_2699_ = v___x_2697_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_dec(v___x_2697_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v_a_2694_);
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2694_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec(v_a_2694_);
v_a_2706_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2697_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2697_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
else
{
lean_dec_ref(v_type_2674_);
return v___x_2693_;
}
}
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec_ref(v_type_2674_);
v_a_2715_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2682_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2682_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___boxed(lean_object* v_type_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
lean_dec(v_a_2725_);
lean_dec(v_a_2724_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(lean_object* v_type_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_2732_, v_a_2733_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___boxed(lean_object* v_type_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(v_type_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
lean_dec(v_a_2751_);
lean_dec_ref(v_a_2750_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
lean_dec(v_a_2747_);
lean_dec(v_a_2746_);
return v_res_2757_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin);
lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OrderLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin);
lean_object* initialize_Lean_OrderLevel(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_OrderLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
}
#ifdef __cplusplus
}
#endif
