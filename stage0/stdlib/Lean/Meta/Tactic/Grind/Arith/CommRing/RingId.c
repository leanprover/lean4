// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM import Lean.Meta.Tactic.Grind.Arith.Insts
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0;
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toCommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(134, 95, 181, 253, 18, 104, 213, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(17, 56, 209, 254, 185, 203, 153, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "PowIdentity available: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "NoNatZeroDivisors available: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "new ring: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(134, 3, 13, 60, 96, 160, 201, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "OfCommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ofCommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(219, 56, 247, 159, 186, 83, 86, 251)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(36, 61, 219, 203, 190, 113, 236, 200)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 171, 186, 15, 174, 251, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "toNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__29_value),LEAN_SCALAR_PTR_LITERAL(8, 241, 181, 204, 215, 46, 40, 252)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__31_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__38_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__40_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__40_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__41_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__42 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__42_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__42_value),LEAN_SCALAR_PTR_LITERAL(84, 97, 73, 37, 143, 22, 233, 204)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__44_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__44_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__45_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__46_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__46_value),LEAN_SCALAR_PTR_LITERAL(1, 189, 244, 99, 68, 50, 19, 202)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "PowIdentity available: false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "instNoNatZeroDivisorsQOfAddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__51 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__51_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__51_value),LEAN_SCALAR_PTR_LITERAL(221, 130, 167, 21, 145, 237, 132, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__53_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__54_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__55_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__55_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "instIsCharPQOfAddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57_value),LEAN_SCALAR_PTR_LITERAL(194, 21, 126, 159, 192, 171, 59, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "`grind` unexpected failure, failure to initialize ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2;
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
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__1);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___boxed(lean_object* v___dummy_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg();
return v_res_7_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg();
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0(lean_object* v_00_u03b2_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0(lean_object* v___x_11_, lean_object* v_s_12_){
_start:
{
lean_object* v_rings_13_; lean_object* v_typeIdOf_14_; lean_object* v_exprToRingId_15_; lean_object* v_semirings_16_; lean_object* v_stypeIdOf_17_; lean_object* v_exprToSemiringId_18_; lean_object* v_ncRings_19_; lean_object* v_exprToNCRingId_20_; lean_object* v_nctypeIdOf_21_; lean_object* v_ncSemirings_22_; lean_object* v_exprToNCSemiringId_23_; lean_object* v_ncstypeIdOf_24_; lean_object* v_steps_25_; uint8_t v_reportedMaxDegreeIssue_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_34_; 
v_rings_13_ = lean_ctor_get(v_s_12_, 0);
v_typeIdOf_14_ = lean_ctor_get(v_s_12_, 1);
v_exprToRingId_15_ = lean_ctor_get(v_s_12_, 2);
v_semirings_16_ = lean_ctor_get(v_s_12_, 3);
v_stypeIdOf_17_ = lean_ctor_get(v_s_12_, 4);
v_exprToSemiringId_18_ = lean_ctor_get(v_s_12_, 5);
v_ncRings_19_ = lean_ctor_get(v_s_12_, 6);
v_exprToNCRingId_20_ = lean_ctor_get(v_s_12_, 7);
v_nctypeIdOf_21_ = lean_ctor_get(v_s_12_, 8);
v_ncSemirings_22_ = lean_ctor_get(v_s_12_, 9);
v_exprToNCSemiringId_23_ = lean_ctor_get(v_s_12_, 10);
v_ncstypeIdOf_24_ = lean_ctor_get(v_s_12_, 11);
v_steps_25_ = lean_ctor_get(v_s_12_, 12);
v_reportedMaxDegreeIssue_26_ = lean_ctor_get_uint8(v_s_12_, sizeof(void*)*13);
v_isSharedCheck_34_ = !lean_is_exclusive(v_s_12_);
if (v_isSharedCheck_34_ == 0)
{
v___x_28_ = v_s_12_;
v_isShared_29_ = v_isSharedCheck_34_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_steps_25_);
lean_inc(v_ncstypeIdOf_24_);
lean_inc(v_exprToNCSemiringId_23_);
lean_inc(v_ncSemirings_22_);
lean_inc(v_nctypeIdOf_21_);
lean_inc(v_exprToNCRingId_20_);
lean_inc(v_ncRings_19_);
lean_inc(v_exprToSemiringId_18_);
lean_inc(v_stypeIdOf_17_);
lean_inc(v_semirings_16_);
lean_inc(v_exprToRingId_15_);
lean_inc(v_typeIdOf_14_);
lean_inc(v_rings_13_);
lean_dec(v_s_12_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_34_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; lean_object* v___x_32_; 
v___x_30_ = lean_array_push(v_rings_13_, v___x_11_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v___x_30_);
v___x_32_ = v___x_28_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v_typeIdOf_14_);
lean_ctor_set(v_reuseFailAlloc_33_, 2, v_exprToRingId_15_);
lean_ctor_set(v_reuseFailAlloc_33_, 3, v_semirings_16_);
lean_ctor_set(v_reuseFailAlloc_33_, 4, v_stypeIdOf_17_);
lean_ctor_set(v_reuseFailAlloc_33_, 5, v_exprToSemiringId_18_);
lean_ctor_set(v_reuseFailAlloc_33_, 6, v_ncRings_19_);
lean_ctor_set(v_reuseFailAlloc_33_, 7, v_exprToNCRingId_20_);
lean_ctor_set(v_reuseFailAlloc_33_, 8, v_nctypeIdOf_21_);
lean_ctor_set(v_reuseFailAlloc_33_, 9, v_ncSemirings_22_);
lean_ctor_set(v_reuseFailAlloc_33_, 10, v_exprToNCSemiringId_23_);
lean_ctor_set(v_reuseFailAlloc_33_, 11, v_ncstypeIdOf_24_);
lean_ctor_set(v_reuseFailAlloc_33_, 12, v_steps_25_);
lean_ctor_set_uint8(v_reuseFailAlloc_33_, sizeof(void*)*13, v_reportedMaxDegreeIssue_26_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(lean_object* v___x_38_, lean_object* v_____do__lift_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_toCold_51_; lean_object* v_options_52_; uint8_t v_hasTrace_53_; 
v_toCold_51_ = lean_ctor_get(v___y_48_, 0);
v_options_52_ = lean_ctor_get(v_toCold_51_, 2);
v_hasTrace_53_ = lean_ctor_get_uint8(v_options_52_, sizeof(void*)*1);
if (v_hasTrace_53_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v___x_38_);
v___x_54_ = lean_box(v_hasTrace_53_);
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___closed__1));
v___x_57_ = l_Lean_Name_append(v___x_56_, v___x_38_);
v___x_58_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_39_, v_options_52_, v___x_57_);
lean_dec(v___x_57_);
v___x_59_ = lean_box(v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___boxed(lean_object* v___x_61_, lean_object* v_____do__lift_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(v___x_61_, v_____do__lift_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v_____do__lift_62_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(lean_object* v_msgData_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; lean_object* v_env_82_; lean_object* v___x_83_; lean_object* v_toCold_84_; lean_object* v_mctx_85_; lean_object* v_lctx_86_; lean_object* v_options_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_81_ = lean_st_ref_get(v___y_79_);
v_env_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc_ref(v_env_82_);
lean_dec(v___x_81_);
v___x_83_ = lean_st_ref_get(v___y_77_);
v_toCold_84_ = lean_ctor_get(v___y_78_, 0);
v_mctx_85_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_mctx_85_);
lean_dec(v___x_83_);
v_lctx_86_ = lean_ctor_get(v___y_76_, 2);
v_options_87_ = lean_ctor_get(v_toCold_84_, 2);
lean_inc_ref(v_options_87_);
lean_inc_ref(v_lctx_86_);
v___x_88_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_88_, 0, v_env_82_);
lean_ctor_set(v___x_88_, 1, v_mctx_85_);
lean_ctor_set(v___x_88_, 2, v_lctx_86_);
lean_ctor_set(v___x_88_, 3, v_options_87_);
v___x_89_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v_msgData_75_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1___boxed(lean_object* v_msgData_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(v_msgData_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
return v_res_97_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_98_; double v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_float_of_nat(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(lean_object* v_cls_103_, lean_object* v_msg_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_ref_110_; lean_object* v___x_111_; lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_156_; 
v_ref_110_ = lean_ctor_get(v___y_107_, 2);
v___x_111_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(v_msg_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_156_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_156_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_156_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v_traceState_117_; lean_object* v_env_118_; lean_object* v_nextMacroScope_119_; lean_object* v_ngen_120_; lean_object* v_auxDeclNGen_121_; lean_object* v_cache_122_; lean_object* v_messages_123_; lean_object* v_infoState_124_; lean_object* v_snapshotTasks_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_155_; 
v___x_116_ = lean_st_ref_take(v___y_108_);
v_traceState_117_ = lean_ctor_get(v___x_116_, 4);
v_env_118_ = lean_ctor_get(v___x_116_, 0);
v_nextMacroScope_119_ = lean_ctor_get(v___x_116_, 1);
v_ngen_120_ = lean_ctor_get(v___x_116_, 2);
v_auxDeclNGen_121_ = lean_ctor_get(v___x_116_, 3);
v_cache_122_ = lean_ctor_get(v___x_116_, 5);
v_messages_123_ = lean_ctor_get(v___x_116_, 6);
v_infoState_124_ = lean_ctor_get(v___x_116_, 7);
v_snapshotTasks_125_ = lean_ctor_get(v___x_116_, 8);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_155_ == 0)
{
v___x_127_ = v___x_116_;
v_isShared_128_ = v_isSharedCheck_155_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_snapshotTasks_125_);
lean_inc(v_infoState_124_);
lean_inc(v_messages_123_);
lean_inc(v_cache_122_);
lean_inc(v_traceState_117_);
lean_inc(v_auxDeclNGen_121_);
lean_inc(v_ngen_120_);
lean_inc(v_nextMacroScope_119_);
lean_inc(v_env_118_);
lean_dec(v___x_116_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_155_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
uint64_t v_tid_129_; lean_object* v_traces_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_154_; 
v_tid_129_ = lean_ctor_get_uint64(v_traceState_117_, sizeof(void*)*1);
v_traces_130_ = lean_ctor_get(v_traceState_117_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v_traceState_117_);
if (v_isSharedCheck_154_ == 0)
{
v___x_132_ = v_traceState_117_;
v_isShared_133_ = v_isSharedCheck_154_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_traces_130_);
lean_dec(v_traceState_117_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_154_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_135_; double v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_134_ = lean_box(0);
v___x_135_ = lean_box(0);
v___x_136_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0);
v___x_137_ = 0;
v___x_138_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__1));
v___x_139_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_139_, 0, v_cls_103_);
lean_ctor_set(v___x_139_, 1, v___x_135_);
lean_ctor_set(v___x_139_, 2, v___x_138_);
lean_ctor_set_float(v___x_139_, sizeof(void*)*3, v___x_136_);
lean_ctor_set_float(v___x_139_, sizeof(void*)*3 + 8, v___x_136_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*3 + 16, v___x_137_);
v___x_140_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__2));
v___x_141_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_141_, 0, v___x_139_);
lean_ctor_set(v___x_141_, 1, v_a_112_);
lean_ctor_set(v___x_141_, 2, v___x_140_);
lean_inc(v_ref_110_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v_ref_110_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = l_Lean_PersistentArray_push___redArg(v_traces_130_, v___x_142_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_143_);
v___x_145_ = v___x_132_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_143_);
lean_ctor_set_uint64(v_reuseFailAlloc_153_, sizeof(void*)*1, v_tid_129_);
v___x_145_ = v_reuseFailAlloc_153_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_147_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v___x_145_);
v___x_147_ = v___x_127_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_env_118_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_nextMacroScope_119_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_ngen_120_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_auxDeclNGen_121_);
lean_ctor_set(v_reuseFailAlloc_152_, 4, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_152_, 5, v_cache_122_);
lean_ctor_set(v_reuseFailAlloc_152_, 6, v_messages_123_);
lean_ctor_set(v_reuseFailAlloc_152_, 7, v_infoState_124_);
lean_ctor_set(v_reuseFailAlloc_152_, 8, v_snapshotTasks_125_);
v___x_147_ = v_reuseFailAlloc_152_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_st_ref_put(v___y_108_, v___x_147_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_134_);
v___x_150_ = v___x_114_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_134_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___boxed(lean_object* v_cls_157_, lean_object* v_msg_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v_cls_157_, v_msg_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_unsigned_to_nat(32u);
v___x_192_ = lean_mk_empty_array_with_capacity(v___x_191_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12(void){
_start:
{
size_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_194_ = ((size_t)5ULL);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_unsigned_to_nat(32u);
v___x_197_ = lean_mk_empty_array_with_capacity(v___x_196_);
v___x_198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11);
v___x_199_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
lean_ctor_set(v___x_199_, 2, v___x_195_);
lean_ctor_set(v___x_199_, 3, v___x_195_);
lean_ctor_set_usize(v___x_199_, 4, v___x_194_);
return v___x_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__0);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16));
v___x_213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1___closed__1));
v___x_214_ = l_Lean_Name_append(v___x_213_, v___x_212_);
return v___x_214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24));
v___x_222_ = l_Lean_stringToMessageData(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(lean_object* v_type_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_238_; 
lean_inc_ref(v_type_226_);
v___x_238_ = l_Lean_Meta_getDecLevel(v_type_226_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc_n(v_a_239_, 2);
lean_dec_ref_known(v___x_238_, 1);
v___x_240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3));
v___x_241_ = lean_box(0);
v___x_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_242_, 0, v_a_239_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
lean_inc_ref(v___x_242_);
v___x_243_ = l_Lean_mkConst(v___x_240_, v___x_242_);
lean_inc_ref(v_type_226_);
v___x_244_ = l_Lean_Expr_app___override(v___x_243_, v_type_226_);
v___x_245_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_244_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_504_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_504_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_504_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_504_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
if (lean_obj_tag(v_a_246_) == 1)
{
lean_object* v_val_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_499_; 
lean_del_object(v___x_248_);
v_val_250_ = lean_ctor_get(v_a_246_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v_a_246_);
if (v_isSharedCheck_499_ == 0)
{
v___x_252_ = v_a_246_;
v_isShared_253_ = v_isSharedCheck_499_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_val_250_);
lean_dec(v_a_246_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_499_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_toCold_257_; lean_object* v_inheritedTraceOptions_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___x_315_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___x_475_; lean_object* v_a_476_; uint8_t v___x_477_; 
v___x_254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5));
lean_inc_ref_n(v___x_242_, 3);
v___x_255_ = l_Lean_mkConst(v___x_254_, v___x_242_);
lean_inc(v_val_250_);
lean_inc_ref_n(v_type_226_, 3);
v___x_256_ = l_Lean_mkAppB(v___x_255_, v_type_226_, v_val_250_);
v_toCold_257_ = lean_ctor_get(v_a_235_, 0);
v_inheritedTraceOptions_258_ = lean_ctor_get(v_toCold_257_, 11);
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8));
v___x_260_ = l_Lean_mkConst(v___x_259_, v___x_242_);
lean_inc_ref(v___x_256_);
v___x_261_ = l_Lean_mkAppB(v___x_260_, v_type_226_, v___x_256_);
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10));
v___x_263_ = l_Lean_mkConst(v___x_262_, v___x_242_);
lean_inc_ref(v___x_261_);
v___x_264_ = l_Lean_mkAppB(v___x_263_, v_type_226_, v___x_261_);
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16));
v___x_475_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(v___x_315_, v_inheritedTraceOptions_258_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref(v___x_475_);
v___x_477_ = lean_unbox(v_a_476_);
lean_dec(v_a_476_);
if (v___x_477_ == 0)
{
v___y_428_ = v_a_227_;
v___y_429_ = v_a_228_;
v___y_430_ = v_a_229_;
v___y_431_ = v_a_230_;
v___y_432_ = v_a_231_;
v___y_433_ = v_a_232_;
v___y_434_ = v_a_233_;
v___y_435_ = v_a_234_;
v___y_436_ = v_a_235_;
v___y_437_ = v_a_236_;
goto v___jp_427_;
}
else
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_Meta_Grind_updateLastTag(v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec_ref_known(v___x_478_, 1);
v___x_479_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27);
lean_inc_ref(v_type_226_);
v___x_480_ = l_Lean_MessageData_ofExpr(v_type_226_);
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_315_, v___x_481_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_dec_ref_known(v___x_482_, 1);
v___y_428_ = v_a_227_;
v___y_429_ = v_a_228_;
v___y_430_ = v_a_229_;
v___y_431_ = v_a_230_;
v___y_432_ = v_a_231_;
v___y_433_ = v_a_232_;
v___y_434_ = v_a_233_;
v___y_435_ = v_a_234_;
v___y_436_ = v_a_235_;
v___y_437_ = v_a_236_;
goto v___jp_427_;
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_256_);
lean_del_object(v___x_252_);
lean_dec(v_val_250_);
lean_dec_ref_known(v___x_242_, 2);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_256_);
lean_del_object(v___x_252_);
lean_dec(v_val_250_);
lean_dec_ref_known(v___x_242_, 2);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
v_a_491_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_478_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_478_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
v___jp_265_:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_box(0);
v___x_273_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v_rings_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
v_rings_275_ = lean_ctor_get(v_a_274_, 0);
lean_inc_ref(v_rings_275_);
lean_dec(v_a_274_);
v___x_276_ = lean_array_get_size(v_rings_275_);
lean_dec_ref(v_rings_275_);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12);
v___x_279_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13);
v___x_280_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_280_, 0, v___x_276_);
lean_ctor_set(v___x_280_, 1, v_type_226_);
lean_ctor_set(v___x_280_, 2, v_a_239_);
lean_ctor_set(v___x_280_, 3, v___x_256_);
lean_ctor_set(v___x_280_, 4, v___x_261_);
lean_ctor_set(v___x_280_, 5, v___y_267_);
lean_ctor_set(v___x_280_, 6, v___x_272_);
lean_ctor_set(v___x_280_, 7, v___x_272_);
lean_ctor_set(v___x_280_, 8, v___x_272_);
lean_ctor_set(v___x_280_, 9, v___x_272_);
lean_ctor_set(v___x_280_, 10, v___x_272_);
lean_ctor_set(v___x_280_, 11, v___x_272_);
lean_ctor_set(v___x_280_, 12, v___x_272_);
lean_ctor_set(v___x_280_, 13, v___x_272_);
lean_ctor_set(v___x_280_, 14, v___x_278_);
lean_ctor_set(v___x_280_, 15, v___x_279_);
lean_ctor_set(v___x_280_, 16, v___x_279_);
v___x_281_ = lean_box(1);
v___x_282_ = 0;
v___x_283_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0);
v___x_284_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v___x_284_, 0, v___x_280_);
lean_ctor_set(v___x_284_, 1, v___x_272_);
lean_ctor_set(v___x_284_, 2, v___x_272_);
lean_ctor_set(v___x_284_, 3, v___x_264_);
lean_ctor_set(v___x_284_, 4, v_val_250_);
lean_ctor_set(v___x_284_, 5, v___y_268_);
lean_ctor_set(v___x_284_, 6, v___y_266_);
lean_ctor_set(v___x_284_, 7, v___y_269_);
lean_ctor_set(v___x_284_, 8, v___x_278_);
lean_ctor_set(v___x_284_, 9, v___x_277_);
lean_ctor_set(v___x_284_, 10, v___x_277_);
lean_ctor_set(v___x_284_, 11, v___x_281_);
lean_ctor_set(v___x_284_, 12, v___x_241_);
lean_ctor_set(v___x_284_, 13, v___x_278_);
lean_ctor_set(v___x_284_, 14, v___x_283_);
lean_ctor_set(v___x_284_, 15, v___x_277_);
lean_ctor_set(v___x_284_, 16, v___x_272_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*17, v___x_282_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*17 + 1, v___x_282_);
v___f_285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0), 2, 1);
lean_closure_set(v___f_285_, 0, v___x_284_);
v___x_286_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_287_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_286_, v___f_285_, v___y_270_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_297_; 
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v___x_287_, 0);
lean_dec(v_unused_298_);
v___x_289_ = v___x_287_;
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
else
{
lean_dec(v___x_287_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_276_);
v___x_292_ = v___x_252_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_276_);
v___x_292_ = v_reuseFailAlloc_296_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_294_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_292_);
v___x_294_ = v___x_289_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_del_object(v___x_252_);
v_a_299_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_287_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_287_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec(v___y_269_);
lean_dec(v___y_268_);
lean_dec(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_256_);
lean_del_object(v___x_252_);
lean_dec(v_val_250_);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
v_a_307_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_273_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_273_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
v___jp_316_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
lean_inc_ref(v___y_332_);
v___x_333_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_333_, 0, v___y_332_);
v___x_334_ = l_Lean_MessageData_ofFormat(v___x_333_);
lean_inc_ref(v___y_320_);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___y_320_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_315_, v___x_335_, v___y_330_, v___y_326_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_dec_ref_known(v___x_336_, 1);
v___y_266_ = v___y_327_;
v___y_267_ = v___y_318_;
v___y_268_ = v___y_331_;
v___y_269_ = v___y_324_;
v___y_270_ = v___y_319_;
v___y_271_ = v___y_328_;
goto v___jp_265_;
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec(v___y_331_);
lean_dec(v___y_327_);
lean_dec(v___y_324_);
lean_dec(v___y_318_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_256_);
lean_del_object(v___x_252_);
lean_dec(v_val_250_);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
v___jp_345_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18));
v___x_359_ = l_Lean_mkConst(v___x_358_, v___x_242_);
lean_inc_ref(v_type_226_);
v___x_360_ = l_Lean_Expr_app___override(v___x_359_, v_type_226_);
v___x_361_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_360_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_363_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_361_, 1);
lean_inc_ref(v_type_226_);
lean_inc(v_a_239_);
v___x_363_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(v_a_239_, v_type_226_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_toCold_364_; lean_object* v_options_365_; uint8_t v_hasTrace_366_; 
v_toCold_364_ = lean_ctor_get(v___y_356_, 0);
v_options_365_ = lean_ctor_get(v_toCold_364_, 2);
v_hasTrace_366_ = lean_ctor_get_uint8(v_options_365_, sizeof(void*)*1);
if (v_hasTrace_366_ == 0)
{
lean_object* v_a_367_; 
v_a_367_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_363_, 1);
v___y_266_ = v_a_362_;
v___y_267_ = v___y_346_;
v___y_268_ = v___y_347_;
v___y_269_ = v_a_367_;
v___y_270_ = v___y_348_;
v___y_271_ = v___y_356_;
goto v___jp_265_;
}
else
{
lean_object* v_a_368_; lean_object* v_inheritedTraceOptions_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_a_368_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_363_, 1);
v_inheritedTraceOptions_369_ = lean_ctor_get(v_toCold_364_, 11);
v___x_370_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19);
v___x_371_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_369_, v_options_365_, v___x_370_);
if (v___x_371_ == 0)
{
v___y_266_ = v_a_362_;
v___y_267_ = v___y_346_;
v___y_268_ = v___y_347_;
v___y_269_ = v_a_368_;
v___y_270_ = v___y_348_;
v___y_271_ = v___y_356_;
goto v___jp_265_;
}
else
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_Grind_updateLastTag(v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_373_; 
lean_dec_ref_known(v___x_372_, 1);
v___x_373_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21);
if (lean_obj_tag(v_a_368_) == 0)
{
lean_object* v___x_374_; 
v___x_374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22));
v___y_317_ = v___y_353_;
v___y_318_ = v___y_346_;
v___y_319_ = v___y_348_;
v___y_320_ = v___x_373_;
v___y_321_ = v___y_349_;
v___y_322_ = v___y_350_;
v___y_323_ = v___y_351_;
v___y_324_ = v_a_368_;
v___y_325_ = v___y_352_;
v___y_326_ = v___y_355_;
v___y_327_ = v_a_362_;
v___y_328_ = v___y_356_;
v___y_329_ = v___y_357_;
v___y_330_ = v___y_354_;
v___y_331_ = v___y_347_;
v___y_332_ = v___x_374_;
goto v___jp_316_;
}
else
{
lean_object* v___x_375_; 
v___x_375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23));
v___y_317_ = v___y_353_;
v___y_318_ = v___y_346_;
v___y_319_ = v___y_348_;
v___y_320_ = v___x_373_;
v___y_321_ = v___y_349_;
v___y_322_ = v___y_350_;
v___y_323_ = v___y_351_;
v___y_324_ = v_a_368_;
v___y_325_ = v___y_352_;
v___y_326_ = v___y_355_;
v___y_327_ = v_a_362_;
v___y_328_ = v___y_356_;
v___y_329_ = v___y_357_;
v___y_330_ = v___y_354_;
v___y_331_ = v___y_347_;
v___y_332_ = v___x_375_;
goto v___jp_316_;
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v_a_368_);
lean_dec(v_a_362_);
lean_dec(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_256_);
lean_del_object(v___x_252_);
lean_dec(v_val_250_);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
v_a_376_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_372_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_372_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v_a_362_);
lean_dec(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_256_);
lean_del_object(v___x_252_);
lean_dec(v_val_250_);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
v_a_384_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_363_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_363_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_256_);
lean_del_object(v___x_252_);
lean_dec(v_val_250_);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
v_a_392_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_361_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_361_);
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
v___jp_400_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_inc_ref(v___y_414_);
v___x_415_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_415_, 0, v___y_414_);
v___x_416_ = l_Lean_MessageData_ofFormat(v___x_415_);
lean_inc_ref(v___y_405_);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___y_405_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_315_, v___x_417_, v___y_404_, v___y_409_, v___y_411_, v___y_408_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_dec_ref_known(v___x_418_, 1);
v___y_346_ = v___y_402_;
v___y_347_ = v___y_412_;
v___y_348_ = v___y_403_;
v___y_349_ = v___y_410_;
v___y_350_ = v___y_413_;
v___y_351_ = v___y_406_;
v___y_352_ = v___y_401_;
v___y_353_ = v___y_407_;
v___y_354_ = v___y_404_;
v___y_355_ = v___y_409_;
v___y_356_ = v___y_411_;
v___y_357_ = v___y_408_;
goto v___jp_345_;
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v___y_412_);
lean_dec(v___y_402_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_256_);
lean_del_object(v___x_252_);
lean_dec(v_val_250_);
lean_dec_ref_known(v___x_242_, 2);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
v___jp_427_:
{
lean_object* v___x_438_; 
lean_inc_ref(v___x_261_);
lean_inc_ref(v_type_226_);
lean_inc(v_a_239_);
v___x_438_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_a_239_, v_type_226_, v___x_261_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
lean_inc_ref(v_type_226_);
lean_inc(v_a_239_);
v___x_440_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v_a_239_, v_type_226_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_toCold_441_; lean_object* v_a_442_; lean_object* v_inheritedTraceOptions_443_; lean_object* v___x_444_; lean_object* v_a_445_; uint8_t v___x_446_; 
v_toCold_441_ = lean_ctor_get(v___y_436_, 0);
v_a_442_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_440_, 1);
v_inheritedTraceOptions_443_ = lean_ctor_get(v_toCold_441_, 11);
v___x_444_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(v___x_315_, v_inheritedTraceOptions_443_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref(v___x_444_);
v___x_446_ = lean_unbox(v_a_445_);
lean_dec(v_a_445_);
if (v___x_446_ == 0)
{
v___y_346_ = v_a_439_;
v___y_347_ = v_a_442_;
v___y_348_ = v___y_428_;
v___y_349_ = v___y_429_;
v___y_350_ = v___y_430_;
v___y_351_ = v___y_431_;
v___y_352_ = v___y_432_;
v___y_353_ = v___y_433_;
v___y_354_ = v___y_434_;
v___y_355_ = v___y_435_;
v___y_356_ = v___y_436_;
v___y_357_ = v___y_437_;
goto v___jp_345_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_Grind_updateLastTag(v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; 
lean_dec_ref_known(v___x_447_, 1);
v___x_448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25);
if (lean_obj_tag(v_a_442_) == 0)
{
lean_object* v___x_449_; 
v___x_449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22));
v___y_401_ = v___y_432_;
v___y_402_ = v_a_439_;
v___y_403_ = v___y_428_;
v___y_404_ = v___y_434_;
v___y_405_ = v___x_448_;
v___y_406_ = v___y_431_;
v___y_407_ = v___y_433_;
v___y_408_ = v___y_437_;
v___y_409_ = v___y_435_;
v___y_410_ = v___y_429_;
v___y_411_ = v___y_436_;
v___y_412_ = v_a_442_;
v___y_413_ = v___y_430_;
v___y_414_ = v___x_449_;
goto v___jp_400_;
}
else
{
lean_object* v___x_450_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23));
v___y_401_ = v___y_432_;
v___y_402_ = v_a_439_;
v___y_403_ = v___y_428_;
v___y_404_ = v___y_434_;
v___y_405_ = v___x_448_;
v___y_406_ = v___y_431_;
v___y_407_ = v___y_433_;
v___y_408_ = v___y_437_;
v___y_409_ = v___y_435_;
v___y_410_ = v___y_429_;
v___y_411_ = v___y_436_;
v___y_412_ = v_a_442_;
v___y_413_ = v___y_430_;
v___y_414_ = v___x_450_;
goto v___jp_400_;
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_a_442_);
lean_dec(v_a_439_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_256_);
lean_del_object(v___x_252_);
lean_dec(v_val_250_);
lean_dec_ref_known(v___x_242_, 2);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
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
lean_dec(v_a_439_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_256_);
lean_del_object(v___x_252_);
lean_dec(v_val_250_);
lean_dec_ref_known(v___x_242_, 2);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
v_a_459_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_440_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_440_);
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
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_dec_ref(v___x_256_);
lean_del_object(v___x_252_);
lean_dec(v_val_250_);
lean_dec_ref_known(v___x_242_, 2);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
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
}
else
{
lean_object* v___x_500_; lean_object* v___x_502_; 
lean_dec(v_a_246_);
lean_dec_ref_known(v___x_242_, 2);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
v___x_500_ = lean_box(0);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_500_);
v___x_502_ = v___x_248_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec_ref_known(v___x_242_, 2);
lean_dec(v_a_239_);
lean_dec_ref(v_type_226_);
v_a_505_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_245_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_245_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec_ref(v_type_226_);
v_a_513_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_238_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_238_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___boxed(lean_object* v_type_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec(v_a_522_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1(lean_object* v_cls_534_, lean_object* v_msg_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v_cls_534_, v_msg_535_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___boxed(lean_object* v_cls_548_, lean_object* v_msg_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1(v_cls_548_, v_msg_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec(v___y_550_);
return v_res_561_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = l_Lean_Level_ofNat(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48));
v___x_676_ = l_Lean_stringToMessageData(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f(lean_object* v_type_700_, lean_object* v_base_701_, lean_object* v_semiringInst_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___x_714_; uint8_t v___x_715_; 
lean_inc_ref(v_semiringInst_702_);
v___x_714_ = l_Lean_Expr_cleanupAnnotations(v_semiringInst_702_);
v___x_715_ = l_Lean_Expr_isApp(v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v___x_714_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
v___x_716_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_700_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
return v___x_716_;
}
else
{
lean_object* v_arg_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_arg_717_ = lean_ctor_get(v___x_714_, 1);
lean_inc_ref(v_arg_717_);
v___x_718_ = l_Lean_Expr_appFnCleanup___redArg(v___x_714_);
v___x_719_ = l_Lean_Expr_isApp(v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec_ref(v___x_718_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
v___x_720_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_700_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_718_);
v___x_722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1));
v___x_723_ = l_Lean_Expr_isConstOf(v___x_721_, v___x_722_);
lean_dec_ref(v___x_721_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
v___x_724_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_700_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
return v___x_724_;
}
else
{
lean_object* v___x_725_; 
lean_inc_ref(v_base_701_);
v___x_725_ = l_Lean_Meta_getDecLevel_x3f(v_base_701_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_1229_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_1229_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_1229_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
if (lean_obj_tag(v_a_726_) == 1)
{
lean_object* v_val_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_1224_; 
lean_del_object(v___x_728_);
v_val_730_ = lean_ctor_get(v_a_726_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_a_726_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_732_ = v_a_726_;
v_isShared_733_ = v_isSharedCheck_1224_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_val_730_);
lean_dec(v_a_726_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_1224_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4));
v___x_735_ = lean_box(0);
lean_inc(v_val_730_);
v___x_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_736_, 0, v_val_730_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
lean_inc_ref_n(v___x_736_, 5);
v___x_737_ = l_Lean_mkConst(v___x_734_, v___x_736_);
lean_inc_ref(v_base_701_);
v___x_738_ = l_Lean_mkAppB(v___x_737_, v_base_701_, v_arg_717_);
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5));
v___x_740_ = l_Lean_mkConst(v___x_739_, v___x_736_);
lean_inc_ref_n(v___x_738_, 2);
lean_inc_ref_n(v_type_700_, 4);
v___x_741_ = l_Lean_mkAppB(v___x_740_, v_type_700_, v___x_738_);
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8));
v___x_743_ = l_Lean_mkConst(v___x_742_, v___x_736_);
lean_inc_ref(v___x_741_);
v___x_744_ = l_Lean_mkAppB(v___x_743_, v_type_700_, v___x_741_);
v___x_745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10));
v___x_746_ = l_Lean_mkConst(v___x_745_, v___x_736_);
lean_inc_ref(v___x_744_);
v___x_747_ = l_Lean_mkAppB(v___x_746_, v_type_700_, v___x_744_);
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3));
v___x_749_ = l_Lean_mkConst(v___x_748_, v___x_736_);
v___x_750_ = l_Lean_Expr_app___override(v___x_749_, v_type_700_);
v___x_751_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_750_, v___x_738_, v_a_708_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec_ref_known(v___x_751_, 1);
v___x_752_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5));
lean_inc_ref(v___x_736_);
v___x_753_ = l_Lean_mkConst(v___x_752_, v___x_736_);
lean_inc_ref(v_type_700_);
v___x_754_ = l_Lean_Expr_app___override(v___x_753_, v_type_700_);
lean_inc_ref(v___x_741_);
v___x_755_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_754_, v___x_741_, v_a_708_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec_ref_known(v___x_755_, 1);
v___x_756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7));
lean_inc_ref(v___x_736_);
v___x_757_ = l_Lean_mkConst(v___x_756_, v___x_736_);
lean_inc_ref(v_type_700_);
v___x_758_ = l_Lean_Expr_app___override(v___x_757_, v_type_700_);
lean_inc_ref(v___x_744_);
v___x_759_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_758_, v___x_744_, v_a_708_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
lean_dec_ref_known(v___x_759_, 1);
v___x_760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8));
lean_inc_ref(v___x_736_);
v___x_761_ = l_Lean_mkConst(v___x_760_, v___x_736_);
lean_inc_ref(v_type_700_);
v___x_762_ = l_Lean_Expr_app___override(v___x_761_, v_type_700_);
lean_inc_ref(v___x_747_);
v___x_763_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_762_, v___x_747_, v_a_708_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec_ref_known(v___x_763_, 1);
v___x_764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10));
lean_inc_ref_n(v___x_736_, 2);
v___x_765_ = l_Lean_mkConst(v___x_764_, v___x_736_);
lean_inc_ref_n(v_type_700_, 2);
v___x_766_ = l_Lean_Expr_app___override(v___x_765_, v_type_700_);
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12));
v___x_768_ = l_Lean_mkConst(v___x_767_, v___x_736_);
lean_inc_ref(v___x_744_);
v___x_769_ = l_Lean_mkAppB(v___x_768_, v_type_700_, v___x_744_);
v___x_770_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_766_, v___x_769_, v_a_708_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec_ref_known(v___x_770_, 1);
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__14));
lean_inc_ref_n(v___x_736_, 3);
lean_inc_n(v_val_730_, 2);
v___x_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_772_, 0, v_val_730_);
lean_ctor_set(v___x_772_, 1, v___x_736_);
v___x_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_773_, 0, v_val_730_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
lean_inc_ref(v___x_773_);
v___x_774_ = l_Lean_mkConst(v___x_771_, v___x_773_);
lean_inc_ref_n(v_type_700_, 5);
v___x_775_ = l_Lean_mkApp3(v___x_774_, v_type_700_, v_type_700_, v_type_700_);
v___x_776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__16));
v___x_777_ = l_Lean_mkConst(v___x_776_, v___x_736_);
v___x_778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18));
v___x_779_ = l_Lean_mkConst(v___x_778_, v___x_736_);
lean_inc_ref(v___x_744_);
v___x_780_ = l_Lean_mkAppB(v___x_779_, v_type_700_, v___x_744_);
v___x_781_ = l_Lean_mkAppB(v___x_777_, v_type_700_, v___x_780_);
v___x_782_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_775_, v___x_781_, v_a_708_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref_known(v___x_782_, 1);
v___x_783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__20));
lean_inc_ref(v___x_773_);
v___x_784_ = l_Lean_mkConst(v___x_783_, v___x_773_);
lean_inc_ref_n(v_type_700_, 5);
v___x_785_ = l_Lean_mkApp3(v___x_784_, v_type_700_, v_type_700_, v_type_700_);
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__22));
lean_inc_ref_n(v___x_736_, 2);
v___x_787_ = l_Lean_mkConst(v___x_786_, v___x_736_);
v___x_788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24));
v___x_789_ = l_Lean_mkConst(v___x_788_, v___x_736_);
lean_inc_ref(v___x_744_);
v___x_790_ = l_Lean_mkAppB(v___x_789_, v_type_700_, v___x_744_);
v___x_791_ = l_Lean_mkAppB(v___x_787_, v_type_700_, v___x_790_);
v___x_792_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_785_, v___x_791_, v_a_708_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec_ref_known(v___x_792_, 1);
v___x_793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__26));
v___x_794_ = l_Lean_mkConst(v___x_793_, v___x_773_);
lean_inc_ref_n(v_type_700_, 5);
v___x_795_ = l_Lean_mkApp3(v___x_794_, v_type_700_, v_type_700_, v_type_700_);
v___x_796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__28));
lean_inc_ref_n(v___x_736_, 2);
v___x_797_ = l_Lean_mkConst(v___x_796_, v___x_736_);
v___x_798_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30));
v___x_799_ = l_Lean_mkConst(v___x_798_, v___x_736_);
lean_inc_ref(v___x_741_);
v___x_800_ = l_Lean_mkAppB(v___x_799_, v_type_700_, v___x_741_);
v___x_801_ = l_Lean_mkAppB(v___x_797_, v_type_700_, v___x_800_);
v___x_802_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_795_, v___x_801_, v_a_708_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec_ref_known(v___x_802_, 1);
v___x_803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__32));
lean_inc_ref_n(v___x_736_, 2);
v___x_804_ = l_Lean_mkConst(v___x_803_, v___x_736_);
lean_inc_ref_n(v_type_700_, 2);
v___x_805_ = l_Lean_Expr_app___override(v___x_804_, v_type_700_);
v___x_806_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34));
v___x_807_ = l_Lean_mkConst(v___x_806_, v___x_736_);
lean_inc_ref(v___x_741_);
v___x_808_ = l_Lean_mkAppB(v___x_807_, v_type_700_, v___x_741_);
v___x_809_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_805_, v___x_808_, v_a_708_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec_ref_known(v___x_809_, 1);
v___x_810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__36));
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37);
lean_inc_ref_n(v___x_736_, 2);
v___x_860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_736_);
lean_inc(v_val_730_);
v___x_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_861_, 0, v_val_730_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_Lean_mkConst(v___x_810_, v___x_861_);
v___x_863_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_700_, 3);
v___x_864_ = l_Lean_mkApp3(v___x_862_, v_type_700_, v___x_863_, v_type_700_);
v___x_865_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39));
v___x_866_ = l_Lean_mkConst(v___x_865_, v___x_736_);
lean_inc_ref(v___x_744_);
v___x_867_ = l_Lean_mkAppB(v___x_866_, v_type_700_, v___x_744_);
v___x_868_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_864_, v___x_867_, v_a_708_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec_ref_known(v___x_868_, 1);
v___x_869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__41));
lean_inc_ref_n(v___x_736_, 2);
v___x_870_ = l_Lean_mkConst(v___x_869_, v___x_736_);
lean_inc_ref_n(v_type_700_, 2);
v___x_871_ = l_Lean_Expr_app___override(v___x_870_, v_type_700_);
v___x_872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43));
v___x_873_ = l_Lean_mkConst(v___x_872_, v___x_736_);
lean_inc_ref(v___x_744_);
v___x_874_ = l_Lean_mkAppB(v___x_873_, v_type_700_, v___x_744_);
v___x_875_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_871_, v___x_874_, v_a_708_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec_ref_known(v___x_875_, 1);
v___x_876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__45));
lean_inc_ref_n(v___x_736_, 2);
v___x_877_ = l_Lean_mkConst(v___x_876_, v___x_736_);
lean_inc_ref_n(v_type_700_, 2);
v___x_878_ = l_Lean_Expr_app___override(v___x_877_, v_type_700_);
v___x_879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47));
v___x_880_ = l_Lean_mkConst(v___x_879_, v___x_736_);
lean_inc_ref(v___x_741_);
v___x_881_ = l_Lean_mkAppB(v___x_880_, v_type_700_, v___x_741_);
v___x_882_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_878_, v___x_881_, v_a_708_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_toCold_883_; lean_object* v_inheritedTraceOptions_884_; lean_object* v___x_885_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v_options_898_; lean_object* v_inheritedTraceOptions_899_; lean_object* v___y_900_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_954_; lean_object* v_noZeroDivInst_x3f_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v_val_985_; lean_object* v_charInst_x3f_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___x_1104_; lean_object* v_a_1105_; uint8_t v___x_1106_; 
lean_dec_ref_known(v___x_882_, 1);
v_toCold_883_ = lean_ctor_get(v_a_711_, 0);
v_inheritedTraceOptions_884_ = lean_ctor_get(v_toCold_883_, 11);
v___x_885_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16));
v___x_1104_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(v___x_885_, v_inheritedTraceOptions_884_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = lean_unbox(v_a_1105_);
lean_dec(v_a_1105_);
if (v___x_1106_ == 0)
{
v___y_1032_ = v_a_703_;
v___y_1033_ = v_a_704_;
v___y_1034_ = v_a_705_;
v___y_1035_ = v_a_706_;
v___y_1036_ = v_a_707_;
v___y_1037_ = v_a_708_;
v___y_1038_ = v_a_709_;
v___y_1039_ = v_a_710_;
v___y_1040_ = v_a_711_;
v___y_1041_ = v_a_712_;
goto v___jp_1031_;
}
else
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_Meta_Grind_updateLastTag(v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec_ref_known(v___x_1107_, 1);
v___x_1108_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27);
lean_inc_ref(v_type_700_);
v___x_1109_ = l_Lean_MessageData_ofExpr(v_type_700_);
v___x_1110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_885_, v___x_1110_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_dec_ref_known(v___x_1111_, 1);
v___y_1032_ = v_a_703_;
v___y_1033_ = v_a_704_;
v___y_1034_ = v_a_705_;
v___y_1035_ = v_a_706_;
v___y_1036_ = v_a_707_;
v___y_1037_ = v_a_708_;
v___y_1038_ = v_a_709_;
v___y_1039_ = v_a_710_;
v___y_1040_ = v_a_711_;
v___y_1041_ = v_a_712_;
goto v___jp_1031_;
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1120_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1107_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1107_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
v___jp_886_:
{
uint8_t v_hasTrace_901_; 
v_hasTrace_901_ = lean_ctor_get_uint8(v_options_898_, sizeof(void*)*1);
if (v_hasTrace_901_ == 0)
{
v___y_813_ = v___y_887_;
v___y_814_ = v___y_888_;
v___y_815_ = v___y_889_;
v___y_816_ = v___y_897_;
goto v___jp_812_;
}
else
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19);
v___x_903_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_899_, v_options_898_, v___x_902_);
if (v___x_903_ == 0)
{
v___y_813_ = v___y_887_;
v___y_814_ = v___y_888_;
v___y_815_ = v___y_889_;
v___y_816_ = v___y_897_;
goto v___jp_812_;
}
else
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Meta_Grind_updateLastTag(v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_900_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec_ref_known(v___x_904_, 1);
v___x_905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49);
v___x_906_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_885_, v___x_905_, v___y_895_, v___y_896_, v___y_897_, v___y_900_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_dec_ref_known(v___x_906_, 1);
v___y_813_ = v___y_887_;
v___y_814_ = v___y_888_;
v___y_815_ = v___y_889_;
v___y_816_ = v___y_897_;
goto v___jp_812_;
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_type_700_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_type_700_);
v_a_915_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_904_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_904_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
v___jp_923_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
lean_inc_ref(v___y_937_);
v___x_938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_938_, 0, v___y_937_);
v___x_939_ = l_Lean_MessageData_ofFormat(v___x_938_);
lean_inc_ref(v___y_929_);
v___x_940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_940_, 0, v___y_929_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_885_, v___x_940_, v___y_932_, v___y_928_, v___y_926_, v___y_935_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_toCold_942_; lean_object* v_options_943_; lean_object* v_inheritedTraceOptions_944_; 
lean_dec_ref_known(v___x_941_, 1);
v_toCold_942_ = lean_ctor_get(v___y_926_, 0);
v_options_943_ = lean_ctor_get(v_toCold_942_, 2);
v_inheritedTraceOptions_944_ = lean_ctor_get(v_toCold_942_, 11);
v___y_887_ = v___y_925_;
v___y_888_ = v___y_927_;
v___y_889_ = v___y_931_;
v___y_890_ = v___y_933_;
v___y_891_ = v___y_924_;
v___y_892_ = v___y_930_;
v___y_893_ = v___y_936_;
v___y_894_ = v___y_934_;
v___y_895_ = v___y_932_;
v___y_896_ = v___y_928_;
v___y_897_ = v___y_926_;
v_options_898_ = v_options_943_;
v_inheritedTraceOptions_899_ = v_inheritedTraceOptions_944_;
v___y_900_ = v___y_935_;
goto v___jp_886_;
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v___y_927_);
lean_dec(v___y_925_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_type_700_);
v_a_945_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_941_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_941_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
v___jp_953_:
{
lean_object* v_toCold_966_; lean_object* v_options_967_; lean_object* v_inheritedTraceOptions_968_; lean_object* v___x_969_; lean_object* v_a_970_; uint8_t v___x_971_; 
v_toCold_966_ = lean_ctor_get(v___y_964_, 0);
v_options_967_ = lean_ctor_get(v_toCold_966_, 2);
v_inheritedTraceOptions_968_ = lean_ctor_get(v_toCold_966_, 11);
v___x_969_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(v___x_885_, v_inheritedTraceOptions_968_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref(v___x_969_);
v___x_971_ = lean_unbox(v_a_970_);
lean_dec(v_a_970_);
if (v___x_971_ == 0)
{
v___y_887_ = v_noZeroDivInst_x3f_955_;
v___y_888_ = v___y_954_;
v___y_889_ = v___y_956_;
v___y_890_ = v___y_957_;
v___y_891_ = v___y_958_;
v___y_892_ = v___y_959_;
v___y_893_ = v___y_960_;
v___y_894_ = v___y_961_;
v___y_895_ = v___y_962_;
v___y_896_ = v___y_963_;
v___y_897_ = v___y_964_;
v_options_898_ = v_options_967_;
v_inheritedTraceOptions_899_ = v_inheritedTraceOptions_968_;
v___y_900_ = v___y_965_;
goto v___jp_886_;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Meta_Grind_updateLastTag(v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v___x_973_; 
lean_dec_ref_known(v___x_972_, 1);
v___x_973_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25);
if (lean_obj_tag(v_noZeroDivInst_x3f_955_) == 0)
{
lean_object* v___x_974_; 
v___x_974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22));
v___y_924_ = v___y_958_;
v___y_925_ = v_noZeroDivInst_x3f_955_;
v___y_926_ = v___y_964_;
v___y_927_ = v___y_954_;
v___y_928_ = v___y_963_;
v___y_929_ = v___x_973_;
v___y_930_ = v___y_959_;
v___y_931_ = v___y_956_;
v___y_932_ = v___y_962_;
v___y_933_ = v___y_957_;
v___y_934_ = v___y_961_;
v___y_935_ = v___y_965_;
v___y_936_ = v___y_960_;
v___y_937_ = v___x_974_;
goto v___jp_923_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23));
v___y_924_ = v___y_958_;
v___y_925_ = v_noZeroDivInst_x3f_955_;
v___y_926_ = v___y_964_;
v___y_927_ = v___y_954_;
v___y_928_ = v___y_963_;
v___y_929_ = v___x_973_;
v___y_930_ = v___y_959_;
v___y_931_ = v___y_956_;
v___y_932_ = v___y_962_;
v___y_933_ = v___y_957_;
v___y_934_ = v___y_961_;
v___y_935_ = v___y_965_;
v___y_936_ = v___y_960_;
v___y_937_ = v___x_975_;
goto v___jp_923_;
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_noZeroDivInst_x3f_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_type_700_);
v_a_976_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_972_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_972_);
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
}
v___jp_984_:
{
lean_object* v___x_997_; 
lean_inc_ref(v_base_701_);
lean_inc(v_val_730_);
v___x_997_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v_val_730_, v_base_701_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
if (lean_obj_tag(v_a_998_) == 1)
{
lean_object* v_val_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1009_; 
v_val_999_ = lean_ctor_get(v_a_998_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_a_998_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1001_ = v_a_998_;
v_isShared_1002_ = v_isSharedCheck_1009_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_val_999_);
lean_dec(v_a_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1009_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52));
v___x_1004_ = l_Lean_mkConst(v___x_1003_, v___x_736_);
v___x_1005_ = l_Lean_mkApp4(v___x_1004_, v_base_701_, v_semiringInst_702_, v_val_985_, v_val_999_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1005_);
v___x_1007_ = v___x_1001_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
v___y_954_ = v_charInst_x3f_986_;
v_noZeroDivInst_x3f_955_ = v___x_1007_;
v___y_956_ = v___y_987_;
v___y_957_ = v___y_988_;
v___y_958_ = v___y_989_;
v___y_959_ = v___y_990_;
v___y_960_ = v___y_991_;
v___y_961_ = v___y_992_;
v___y_962_ = v___y_993_;
v___y_963_ = v___y_994_;
v___y_964_ = v___y_995_;
v___y_965_ = v___y_996_;
goto v___jp_953_;
}
}
}
else
{
lean_object* v___x_1010_; 
lean_dec(v_a_998_);
lean_dec_ref(v_val_985_);
lean_dec_ref_known(v___x_736_, 2);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
v___x_1010_ = lean_box(0);
v___y_954_ = v_charInst_x3f_986_;
v_noZeroDivInst_x3f_955_ = v___x_1010_;
v___y_956_ = v___y_987_;
v___y_957_ = v___y_988_;
v___y_958_ = v___y_989_;
v___y_959_ = v___y_990_;
v___y_960_ = v___y_991_;
v___y_961_ = v___y_992_;
v___y_962_ = v___y_993_;
v___y_963_ = v___y_994_;
v___y_964_ = v___y_995_;
v___y_965_ = v___y_996_;
goto v___jp_953_;
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_charInst_x3f_986_);
lean_dec_ref(v_val_985_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1011_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_997_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_997_);
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
v___jp_1019_:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_box(0);
v___y_954_ = v___x_1030_;
v_noZeroDivInst_x3f_955_ = v___x_1030_;
v___y_956_ = v___y_1020_;
v___y_957_ = v___y_1021_;
v___y_958_ = v___y_1022_;
v___y_959_ = v___y_1023_;
v___y_960_ = v___y_1024_;
v___y_961_ = v___y_1025_;
v___y_962_ = v___y_1026_;
v___y_963_ = v___y_1027_;
v___y_964_ = v___y_1028_;
v___y_965_ = v___y_1029_;
goto v___jp_953_;
}
v___jp_1031_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__54));
lean_inc_ref(v___x_736_);
v___x_1043_ = l_Lean_mkConst(v___x_1042_, v___x_736_);
lean_inc_ref(v_base_701_);
v___x_1044_ = l_Lean_Expr_app___override(v___x_1043_, v_base_701_);
v___x_1045_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1044_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
if (lean_obj_tag(v_a_1046_) == 1)
{
lean_object* v_val_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_val_1047_ = lean_ctor_get(v_a_1046_, 0);
lean_inc(v_val_1047_);
lean_dec_ref_known(v_a_1046_, 1);
v___x_1048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56));
lean_inc_ref(v___x_736_);
v___x_1049_ = l_Lean_mkConst(v___x_1048_, v___x_736_);
lean_inc_ref(v_base_701_);
v___x_1050_ = l_Lean_mkAppB(v___x_1049_, v_base_701_, v_val_1047_);
v___x_1051_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1050_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
if (lean_obj_tag(v_a_1052_) == 1)
{
lean_object* v_val_1053_; lean_object* v___x_1054_; 
v_val_1053_ = lean_ctor_get(v_a_1052_, 0);
lean_inc(v_val_1053_);
lean_dec_ref_known(v_a_1052_, 1);
lean_inc_ref(v_semiringInst_702_);
lean_inc_ref(v_base_701_);
lean_inc(v_val_730_);
v___x_1054_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_val_730_, v_base_701_, v_semiringInst_702_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
if (lean_obj_tag(v_a_1055_) == 1)
{
lean_object* v_val_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1076_; 
v_val_1056_ = lean_ctor_get(v_a_1055_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_a_1055_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1058_ = v_a_1055_;
v_isShared_1059_ = v_isSharedCheck_1076_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_val_1056_);
lean_dec(v_a_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1076_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_fst_1060_; lean_object* v_snd_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1075_; 
v_fst_1060_ = lean_ctor_get(v_val_1056_, 0);
v_snd_1061_ = lean_ctor_get(v_val_1056_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_val_1056_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1063_ = v_val_1056_;
v_isShared_1064_ = v_isSharedCheck_1075_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_snd_1061_);
lean_inc(v_fst_1060_);
lean_dec(v_val_1056_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1075_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1065_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58));
lean_inc_ref(v___x_736_);
v___x_1066_ = l_Lean_mkConst(v___x_1065_, v___x_736_);
lean_inc(v_snd_1061_);
v___x_1067_ = l_Lean_mkRawNatLit(v_snd_1061_);
lean_inc(v_val_1053_);
lean_inc_ref(v_semiringInst_702_);
lean_inc_ref(v_base_701_);
v___x_1068_ = l_Lean_mkApp5(v___x_1066_, v_base_701_, v___x_1067_, v_semiringInst_702_, v_val_1053_, v_fst_1060_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1068_);
v___x_1070_ = v___x_1063_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_snd_1061_);
v___x_1070_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1070_);
v___x_1072_ = v___x_1058_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
v_val_985_ = v_val_1053_;
v_charInst_x3f_986_ = v___x_1072_;
v___y_987_ = v___y_1032_;
v___y_988_ = v___y_1033_;
v___y_989_ = v___y_1034_;
v___y_990_ = v___y_1035_;
v___y_991_ = v___y_1036_;
v___y_992_ = v___y_1037_;
v___y_993_ = v___y_1038_;
v___y_994_ = v___y_1039_;
v___y_995_ = v___y_1040_;
v___y_996_ = v___y_1041_;
goto v___jp_984_;
}
}
}
}
}
else
{
lean_object* v___x_1077_; 
lean_dec(v_a_1055_);
v___x_1077_ = lean_box(0);
v_val_985_ = v_val_1053_;
v_charInst_x3f_986_ = v___x_1077_;
v___y_987_ = v___y_1032_;
v___y_988_ = v___y_1033_;
v___y_989_ = v___y_1034_;
v___y_990_ = v___y_1035_;
v___y_991_ = v___y_1036_;
v___y_992_ = v___y_1037_;
v___y_993_ = v___y_1038_;
v___y_994_ = v___y_1039_;
v___y_995_ = v___y_1040_;
v___y_996_ = v___y_1041_;
goto v___jp_984_;
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v_val_1053_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1078_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1054_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1054_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
else
{
if (lean_obj_tag(v_a_1052_) == 1)
{
lean_object* v_val_1086_; lean_object* v___x_1087_; 
v_val_1086_ = lean_ctor_get(v_a_1052_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v_a_1052_, 1);
v___x_1087_ = lean_box(0);
v_val_985_ = v_val_1086_;
v_charInst_x3f_986_ = v___x_1087_;
v___y_987_ = v___y_1032_;
v___y_988_ = v___y_1033_;
v___y_989_ = v___y_1034_;
v___y_990_ = v___y_1035_;
v___y_991_ = v___y_1036_;
v___y_992_ = v___y_1037_;
v___y_993_ = v___y_1038_;
v___y_994_ = v___y_1039_;
v___y_995_ = v___y_1040_;
v___y_996_ = v___y_1041_;
goto v___jp_984_;
}
else
{
lean_dec(v_a_1052_);
lean_dec_ref_known(v___x_736_, 2);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
v___y_1020_ = v___y_1032_;
v___y_1021_ = v___y_1033_;
v___y_1022_ = v___y_1034_;
v___y_1023_ = v___y_1035_;
v___y_1024_ = v___y_1036_;
v___y_1025_ = v___y_1037_;
v___y_1026_ = v___y_1038_;
v___y_1027_ = v___y_1039_;
v___y_1028_ = v___y_1040_;
v___y_1029_ = v___y_1041_;
goto v___jp_1019_;
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1088_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1051_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1051_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_dec(v_a_1046_);
lean_dec_ref_known(v___x_736_, 2);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
v___y_1020_ = v___y_1032_;
v___y_1021_ = v___y_1033_;
v___y_1022_ = v___y_1034_;
v___y_1023_ = v___y_1035_;
v___y_1024_ = v___y_1036_;
v___y_1025_ = v___y_1037_;
v___y_1026_ = v___y_1038_;
v___y_1027_ = v___y_1039_;
v___y_1028_ = v___y_1040_;
v___y_1029_ = v___y_1041_;
goto v___jp_1019_;
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1096_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1045_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1045_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1128_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_882_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_882_);
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
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1136_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_875_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_875_);
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
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1144_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_868_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_868_);
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
v___jp_812_:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v_rings_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___f_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
v_rings_819_ = lean_ctor_get(v_a_818_, 0);
lean_inc_ref(v_rings_819_);
lean_dec(v_a_818_);
v___x_820_ = lean_array_get_size(v_rings_819_);
lean_dec_ref(v_rings_819_);
v___x_821_ = lean_box(0);
v___x_822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12);
v___x_823_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13);
v___x_824_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_824_, 0, v___x_820_);
lean_ctor_set(v___x_824_, 1, v_type_700_);
lean_ctor_set(v___x_824_, 2, v_val_730_);
lean_ctor_set(v___x_824_, 3, v___x_741_);
lean_ctor_set(v___x_824_, 4, v___x_744_);
lean_ctor_set(v___x_824_, 5, v___y_814_);
lean_ctor_set(v___x_824_, 6, v___x_821_);
lean_ctor_set(v___x_824_, 7, v___x_821_);
lean_ctor_set(v___x_824_, 8, v___x_821_);
lean_ctor_set(v___x_824_, 9, v___x_821_);
lean_ctor_set(v___x_824_, 10, v___x_821_);
lean_ctor_set(v___x_824_, 11, v___x_821_);
lean_ctor_set(v___x_824_, 12, v___x_821_);
lean_ctor_set(v___x_824_, 13, v___x_821_);
lean_ctor_set(v___x_824_, 14, v___x_822_);
lean_ctor_set(v___x_824_, 15, v___x_823_);
lean_ctor_set(v___x_824_, 16, v___x_823_);
v___x_825_ = lean_box(1);
v___x_826_ = 0;
v___x_827_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0);
v___x_828_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v___x_828_, 0, v___x_824_);
lean_ctor_set(v___x_828_, 1, v___x_821_);
lean_ctor_set(v___x_828_, 2, v___x_821_);
lean_ctor_set(v___x_828_, 3, v___x_747_);
lean_ctor_set(v___x_828_, 4, v___x_738_);
lean_ctor_set(v___x_828_, 5, v___y_813_);
lean_ctor_set(v___x_828_, 6, v___x_821_);
lean_ctor_set(v___x_828_, 7, v___x_821_);
lean_ctor_set(v___x_828_, 8, v___x_822_);
lean_ctor_set(v___x_828_, 9, v___x_811_);
lean_ctor_set(v___x_828_, 10, v___x_811_);
lean_ctor_set(v___x_828_, 11, v___x_825_);
lean_ctor_set(v___x_828_, 12, v___x_735_);
lean_ctor_set(v___x_828_, 13, v___x_822_);
lean_ctor_set(v___x_828_, 14, v___x_827_);
lean_ctor_set(v___x_828_, 15, v___x_811_);
lean_ctor_set(v___x_828_, 16, v___x_821_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*17, v___x_826_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*17 + 1, v___x_826_);
v___f_829_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0), 2, 1);
lean_closure_set(v___f_829_, 0, v___x_828_);
v___x_830_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_831_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_830_, v___f_829_, v___y_815_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_841_; 
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v___x_831_, 0);
lean_dec(v_unused_842_);
v___x_833_ = v___x_831_;
v_isShared_834_ = v_isSharedCheck_841_;
goto v_resetjp_832_;
}
else
{
lean_dec(v___x_831_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_841_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_820_);
v___x_836_ = v___x_732_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_820_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_838_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_836_);
v___x_838_ = v___x_833_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_del_object(v___x_732_);
v_a_843_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_831_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_831_);
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
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_type_700_);
v_a_851_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_817_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_817_);
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
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1152_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_809_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_809_);
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
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1160_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_802_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_802_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref_known(v___x_773_, 2);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1168_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_792_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_792_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
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
lean_dec_ref_known(v___x_773_, 2);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1176_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_782_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_782_);
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
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1184_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_770_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_770_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
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
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1192_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_763_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_763_);
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
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1200_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_759_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_759_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1208_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_755_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_755_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref_known(v___x_736_, 2);
lean_del_object(v___x_732_);
lean_dec(v_val_730_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1216_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_751_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_751_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
lean_dec(v_a_726_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v___x_1225_ = lean_box(0);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_1225_);
v___x_1227_ = v___x_728_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_semiringInst_702_);
lean_dec_ref(v_base_701_);
lean_dec_ref(v_type_700_);
v_a_1230_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_725_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_725_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___boxed(lean_object* v_type_1238_, lean_object* v_base_1239_, lean_object* v_semiringInst_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f(v_type_1238_, v_base_1239_, v_semiringInst_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec(v_a_1241_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(lean_object* v_type_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1));
v___x_1273_ = lean_unsigned_to_nat(2u);
v___x_1274_ = l_Lean_Expr_isAppOfArity(v_type_1260_, v___x_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
v___x_1275_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1276_ = l_Lean_Expr_appFn_x21(v_type_1260_);
v___x_1277_ = l_Lean_Expr_appArg_x21(v___x_1276_);
lean_dec_ref(v___x_1276_);
v___x_1278_ = l_Lean_Expr_appArg_x21(v_type_1260_);
v___x_1279_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f(v_type_1260_, v___x_1277_, v___x_1278_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___boxed(lean_object* v_type_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec(v_a_1281_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_){
_start:
{
lean_object* v_ks_1297_; lean_object* v_vs_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1324_; 
v_ks_1297_ = lean_ctor_get(v_x_1293_, 0);
v_vs_1298_ = lean_ctor_get(v_x_1293_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_x_1293_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1300_ = v_x_1293_;
v_isShared_1301_ = v_isSharedCheck_1324_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_vs_1298_);
lean_inc(v_ks_1297_);
lean_dec(v_x_1293_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1324_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = lean_array_get_size(v_ks_1297_);
v___x_1303_ = lean_nat_dec_lt(v_x_1294_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
lean_dec(v_x_1294_);
v___x_1304_ = lean_array_push(v_ks_1297_, v_x_1295_);
v___x_1305_ = lean_array_push(v_vs_1298_, v_x_1296_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 1, v___x_1305_);
lean_ctor_set(v___x_1300_, 0, v___x_1304_);
v___x_1307_ = v___x_1300_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
else
{
lean_object* v_k_x27_1309_; size_t v___x_1310_; size_t v___x_1311_; uint8_t v___x_1312_; 
v_k_x27_1309_ = lean_array_fget_borrowed(v_ks_1297_, v_x_1294_);
v___x_1310_ = lean_ptr_addr(v_x_1295_);
v___x_1311_ = lean_ptr_addr(v_k_x27_1309_);
v___x_1312_ = lean_usize_dec_eq(v___x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1314_; 
if (v_isShared_1301_ == 0)
{
v___x_1314_ = v___x_1300_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_ks_1297_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_vs_1298_);
v___x_1314_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_unsigned_to_nat(1u);
v___x_1316_ = lean_nat_add(v_x_1294_, v___x_1315_);
lean_dec(v_x_1294_);
v_x_1293_ = v___x_1314_;
v_x_1294_ = v___x_1316_;
goto _start;
}
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1319_ = lean_array_fset(v_ks_1297_, v_x_1294_, v_x_1295_);
v___x_1320_ = lean_array_fset(v_vs_1298_, v_x_1294_, v_x_1296_);
lean_dec(v_x_1294_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 1, v___x_1320_);
lean_ctor_set(v___x_1300_, 0, v___x_1319_);
v___x_1322_ = v___x_1300_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1325_, lean_object* v_k_1326_, lean_object* v_v_1327_){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1325_, v___x_1328_, v_k_1326_, v_v_1327_);
return v___x_1329_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(lean_object* v_x_1331_, size_t v_x_1332_, size_t v_x_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_){
_start:
{
if (lean_obj_tag(v_x_1331_) == 0)
{
lean_object* v_es_1336_; size_t v___x_1337_; size_t v___x_1338_; lean_object* v_j_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_es_1336_ = lean_ctor_get(v_x_1331_, 0);
v___x_1337_ = ((size_t)31ULL);
v___x_1338_ = lean_usize_land(v_x_1332_, v___x_1337_);
v_j_1339_ = lean_usize_to_nat(v___x_1338_);
v___x_1340_ = lean_array_get_size(v_es_1336_);
v___x_1341_ = lean_nat_dec_lt(v_j_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_dec(v_j_1339_);
lean_dec(v_x_1335_);
lean_dec_ref(v_x_1334_);
return v_x_1331_;
}
else
{
lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1382_; 
lean_inc_ref(v_es_1336_);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_x_1331_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v_x_1331_, 0);
lean_dec(v_unused_1383_);
v___x_1343_ = v_x_1331_;
v_isShared_1344_ = v_isSharedCheck_1382_;
goto v_resetjp_1342_;
}
else
{
lean_dec(v_x_1331_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1382_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_v_1345_; lean_object* v___x_1346_; lean_object* v_xs_x27_1347_; lean_object* v___y_1349_; 
v_v_1345_ = lean_array_fget(v_es_1336_, v_j_1339_);
v___x_1346_ = lean_box(0);
v_xs_x27_1347_ = lean_array_fset(v_es_1336_, v_j_1339_, v___x_1346_);
switch(lean_obj_tag(v_v_1345_))
{
case 0:
{
lean_object* v_key_1354_; lean_object* v_val_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1367_; 
v_key_1354_ = lean_ctor_get(v_v_1345_, 0);
v_val_1355_ = lean_ctor_get(v_v_1345_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_v_1345_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1357_ = v_v_1345_;
v_isShared_1358_ = v_isSharedCheck_1367_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_val_1355_);
lean_inc(v_key_1354_);
lean_dec(v_v_1345_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1367_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
size_t v___x_1359_; size_t v___x_1360_; uint8_t v___x_1361_; 
v___x_1359_ = lean_ptr_addr(v_x_1334_);
v___x_1360_ = lean_ptr_addr(v_key_1354_);
v___x_1361_ = lean_usize_dec_eq(v___x_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_del_object(v___x_1357_);
v___x_1362_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1354_, v_val_1355_, v_x_1334_, v_x_1335_);
v___x_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
v___y_1349_ = v___x_1363_;
goto v___jp_1348_;
}
else
{
lean_object* v___x_1365_; 
lean_dec(v_val_1355_);
lean_dec(v_key_1354_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 1, v_x_1335_);
lean_ctor_set(v___x_1357_, 0, v_x_1334_);
v___x_1365_ = v___x_1357_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_x_1334_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_x_1335_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v___y_1349_ = v___x_1365_;
goto v___jp_1348_;
}
}
}
}
case 1:
{
lean_object* v_node_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1380_; 
v_node_1368_ = lean_ctor_get(v_v_1345_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_v_1345_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1370_ = v_v_1345_;
v_isShared_1371_ = v_isSharedCheck_1380_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_node_1368_);
lean_dec(v_v_1345_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1380_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
size_t v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1372_ = ((size_t)5ULL);
v___x_1373_ = lean_usize_shift_right(v_x_1332_, v___x_1372_);
v___x_1374_ = ((size_t)1ULL);
v___x_1375_ = lean_usize_add(v_x_1333_, v___x_1374_);
v___x_1376_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_node_1368_, v___x_1373_, v___x_1375_, v_x_1334_, v_x_1335_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1376_);
v___x_1378_ = v___x_1370_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
v___y_1349_ = v___x_1378_;
goto v___jp_1348_;
}
}
}
default: 
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v_x_1334_);
lean_ctor_set(v___x_1381_, 1, v_x_1335_);
v___y_1349_ = v___x_1381_;
goto v___jp_1348_;
}
}
v___jp_1348_:
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1350_ = lean_array_fset(v_xs_x27_1347_, v_j_1339_, v___y_1349_);
lean_dec(v_j_1339_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1350_);
v___x_1352_ = v___x_1343_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
else
{
lean_object* v_ks_1384_; lean_object* v_vs_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1403_; 
v_ks_1384_ = lean_ctor_get(v_x_1331_, 0);
v_vs_1385_ = lean_ctor_get(v_x_1331_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_x_1331_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1387_ = v_x_1331_;
v_isShared_1388_ = v_isSharedCheck_1403_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_vs_1385_);
lean_inc(v_ks_1384_);
lean_dec(v_x_1331_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1403_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_ks_1384_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_vs_1385_);
v___x_1390_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v_newNode_1391_; size_t v___x_1392_; uint8_t v___x_1393_; 
v_newNode_1391_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v___x_1390_, v_x_1334_, v_x_1335_);
v___x_1392_ = ((size_t)7ULL);
v___x_1393_ = lean_usize_dec_le(v___x_1392_, v_x_1333_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1391_);
v___x_1395_ = lean_unsigned_to_nat(4u);
v___x_1396_ = lean_nat_dec_lt(v___x_1394_, v___x_1395_);
lean_dec(v___x_1394_);
if (v___x_1396_ == 0)
{
lean_object* v_ks_1397_; lean_object* v_vs_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_ks_1397_ = lean_ctor_get(v_newNode_1391_, 0);
lean_inc_ref(v_ks_1397_);
v_vs_1398_ = lean_ctor_get(v_newNode_1391_, 1);
lean_inc_ref(v_vs_1398_);
lean_dec_ref(v_newNode_1391_);
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0);
v___x_1401_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_x_1333_, v_ks_1397_, v_vs_1398_, v___x_1399_, v___x_1400_);
lean_dec_ref(v_vs_1398_);
lean_dec_ref(v_ks_1397_);
return v___x_1401_;
}
else
{
return v_newNode_1391_;
}
}
else
{
return v_newNode_1391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_1404_, lean_object* v_keys_1405_, lean_object* v_vals_1406_, lean_object* v_i_1407_, lean_object* v_entries_1408_){
_start:
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = lean_array_get_size(v_keys_1405_);
v___x_1410_ = lean_nat_dec_lt(v_i_1407_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_dec(v_i_1407_);
return v_entries_1408_;
}
else
{
lean_object* v_k_1411_; lean_object* v_v_1412_; size_t v___x_1413_; size_t v___x_1414_; size_t v___x_1415_; uint64_t v___x_1416_; size_t v_h_1417_; size_t v___x_1418_; lean_object* v___x_1419_; size_t v___x_1420_; size_t v___x_1421_; size_t v___x_1422_; size_t v_h_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_k_1411_ = lean_array_fget_borrowed(v_keys_1405_, v_i_1407_);
v_v_1412_ = lean_array_fget_borrowed(v_vals_1406_, v_i_1407_);
v___x_1413_ = lean_ptr_addr(v_k_1411_);
v___x_1414_ = ((size_t)3ULL);
v___x_1415_ = lean_usize_shift_right(v___x_1413_, v___x_1414_);
v___x_1416_ = lean_usize_to_uint64(v___x_1415_);
v_h_1417_ = lean_uint64_to_usize(v___x_1416_);
v___x_1418_ = ((size_t)5ULL);
v___x_1419_ = lean_unsigned_to_nat(1u);
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_sub(v_depth_1404_, v___x_1420_);
v___x_1422_ = lean_usize_mul(v___x_1418_, v___x_1421_);
v_h_1423_ = lean_usize_shift_right(v_h_1417_, v___x_1422_);
v___x_1424_ = lean_nat_add(v_i_1407_, v___x_1419_);
lean_dec(v_i_1407_);
lean_inc(v_v_1412_);
lean_inc(v_k_1411_);
v___x_1425_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_entries_1408_, v_h_1423_, v_depth_1404_, v_k_1411_, v_v_1412_);
v_i_1407_ = v___x_1424_;
v_entries_1408_ = v___x_1425_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1427_, lean_object* v_keys_1428_, lean_object* v_vals_1429_, lean_object* v_i_1430_, lean_object* v_entries_1431_){
_start:
{
size_t v_depth_boxed_1432_; lean_object* v_res_1433_; 
v_depth_boxed_1432_ = lean_unbox_usize(v_depth_1427_);
lean_dec(v_depth_1427_);
v_res_1433_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1432_, v_keys_1428_, v_vals_1429_, v_i_1430_, v_entries_1431_);
lean_dec_ref(v_vals_1429_);
lean_dec_ref(v_keys_1428_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_){
_start:
{
size_t v_x_3956__boxed_1439_; size_t v_x_3957__boxed_1440_; lean_object* v_res_1441_; 
v_x_3956__boxed_1439_ = lean_unbox_usize(v_x_1435_);
lean_dec(v_x_1435_);
v_x_3957__boxed_1440_ = lean_unbox_usize(v_x_1436_);
lean_dec(v_x_1436_);
v_res_1441_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_1434_, v_x_3956__boxed_1439_, v_x_3957__boxed_1440_, v_x_1437_, v_x_1438_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_){
_start:
{
size_t v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; uint64_t v___x_1448_; size_t v___x_1449_; size_t v___x_1450_; lean_object* v___x_1451_; 
v___x_1445_ = lean_ptr_addr(v_x_1443_);
v___x_1446_ = ((size_t)3ULL);
v___x_1447_ = lean_usize_shift_right(v___x_1445_, v___x_1446_);
v___x_1448_ = lean_usize_to_uint64(v___x_1447_);
v___x_1449_ = lean_uint64_to_usize(v___x_1448_);
v___x_1450_ = ((size_t)1ULL);
v___x_1451_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_1442_, v___x_1449_, v___x_1450_, v_x_1443_, v_x_1444_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0(lean_object* v_type_1452_, lean_object* v_a_1453_, lean_object* v_s_1454_){
_start:
{
lean_object* v_rings_1455_; lean_object* v_typeIdOf_1456_; lean_object* v_exprToRingId_1457_; lean_object* v_semirings_1458_; lean_object* v_stypeIdOf_1459_; lean_object* v_exprToSemiringId_1460_; lean_object* v_ncRings_1461_; lean_object* v_exprToNCRingId_1462_; lean_object* v_nctypeIdOf_1463_; lean_object* v_ncSemirings_1464_; lean_object* v_exprToNCSemiringId_1465_; lean_object* v_ncstypeIdOf_1466_; lean_object* v_steps_1467_; uint8_t v_reportedMaxDegreeIssue_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1476_; 
v_rings_1455_ = lean_ctor_get(v_s_1454_, 0);
v_typeIdOf_1456_ = lean_ctor_get(v_s_1454_, 1);
v_exprToRingId_1457_ = lean_ctor_get(v_s_1454_, 2);
v_semirings_1458_ = lean_ctor_get(v_s_1454_, 3);
v_stypeIdOf_1459_ = lean_ctor_get(v_s_1454_, 4);
v_exprToSemiringId_1460_ = lean_ctor_get(v_s_1454_, 5);
v_ncRings_1461_ = lean_ctor_get(v_s_1454_, 6);
v_exprToNCRingId_1462_ = lean_ctor_get(v_s_1454_, 7);
v_nctypeIdOf_1463_ = lean_ctor_get(v_s_1454_, 8);
v_ncSemirings_1464_ = lean_ctor_get(v_s_1454_, 9);
v_exprToNCSemiringId_1465_ = lean_ctor_get(v_s_1454_, 10);
v_ncstypeIdOf_1466_ = lean_ctor_get(v_s_1454_, 11);
v_steps_1467_ = lean_ctor_get(v_s_1454_, 12);
v_reportedMaxDegreeIssue_1468_ = lean_ctor_get_uint8(v_s_1454_, sizeof(void*)*13);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_s_1454_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1470_ = v_s_1454_;
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_steps_1467_);
lean_inc(v_ncstypeIdOf_1466_);
lean_inc(v_exprToNCSemiringId_1465_);
lean_inc(v_ncSemirings_1464_);
lean_inc(v_nctypeIdOf_1463_);
lean_inc(v_exprToNCRingId_1462_);
lean_inc(v_ncRings_1461_);
lean_inc(v_exprToSemiringId_1460_);
lean_inc(v_stypeIdOf_1459_);
lean_inc(v_semirings_1458_);
lean_inc(v_exprToRingId_1457_);
lean_inc(v_typeIdOf_1456_);
lean_inc(v_rings_1455_);
lean_dec(v_s_1454_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_typeIdOf_1456_, v_type_1452_, v_a_1453_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 1, v___x_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_rings_1455_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_exprToRingId_1457_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_semirings_1458_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_stypeIdOf_1459_);
lean_ctor_set(v_reuseFailAlloc_1475_, 5, v_exprToSemiringId_1460_);
lean_ctor_set(v_reuseFailAlloc_1475_, 6, v_ncRings_1461_);
lean_ctor_set(v_reuseFailAlloc_1475_, 7, v_exprToNCRingId_1462_);
lean_ctor_set(v_reuseFailAlloc_1475_, 8, v_nctypeIdOf_1463_);
lean_ctor_set(v_reuseFailAlloc_1475_, 9, v_ncSemirings_1464_);
lean_ctor_set(v_reuseFailAlloc_1475_, 10, v_exprToNCSemiringId_1465_);
lean_ctor_set(v_reuseFailAlloc_1475_, 11, v_ncstypeIdOf_1466_);
lean_ctor_set(v_reuseFailAlloc_1475_, 12, v_steps_1467_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1468_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1477_, lean_object* v_vals_1478_, lean_object* v_i_1479_, lean_object* v_k_1480_){
_start:
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = lean_array_get_size(v_keys_1477_);
v___x_1482_ = lean_nat_dec_lt(v_i_1479_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
lean_dec(v_i_1479_);
v___x_1483_ = lean_box(0);
return v___x_1483_;
}
else
{
lean_object* v_k_x27_1484_; size_t v___x_1485_; size_t v___x_1486_; uint8_t v___x_1487_; 
v_k_x27_1484_ = lean_array_fget_borrowed(v_keys_1477_, v_i_1479_);
v___x_1485_ = lean_ptr_addr(v_k_1480_);
v___x_1486_ = lean_ptr_addr(v_k_x27_1484_);
v___x_1487_ = lean_usize_dec_eq(v___x_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_unsigned_to_nat(1u);
v___x_1489_ = lean_nat_add(v_i_1479_, v___x_1488_);
lean_dec(v_i_1479_);
v_i_1479_ = v___x_1489_;
goto _start;
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_array_fget_borrowed(v_vals_1478_, v_i_1479_);
lean_dec(v_i_1479_);
lean_inc(v___x_1491_);
v___x_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
return v___x_1492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1493_, lean_object* v_vals_1494_, lean_object* v_i_1495_, lean_object* v_k_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1493_, v_vals_1494_, v_i_1495_, v_k_1496_);
lean_dec_ref(v_k_1496_);
lean_dec_ref(v_vals_1494_);
lean_dec_ref(v_keys_1493_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_1498_, size_t v_x_1499_, lean_object* v_x_1500_){
_start:
{
if (lean_obj_tag(v_x_1498_) == 0)
{
lean_object* v_es_1501_; lean_object* v___x_1502_; size_t v___x_1503_; size_t v___x_1504_; lean_object* v_j_1505_; lean_object* v___x_1506_; 
v_es_1501_ = lean_ctor_get(v_x_1498_, 0);
v___x_1502_ = lean_box(2);
v___x_1503_ = ((size_t)31ULL);
v___x_1504_ = lean_usize_land(v_x_1499_, v___x_1503_);
v_j_1505_ = lean_usize_to_nat(v___x_1504_);
v___x_1506_ = lean_array_get_borrowed(v___x_1502_, v_es_1501_, v_j_1505_);
lean_dec(v_j_1505_);
switch(lean_obj_tag(v___x_1506_))
{
case 0:
{
lean_object* v_key_1507_; lean_object* v_val_1508_; size_t v___x_1509_; size_t v___x_1510_; uint8_t v___x_1511_; 
v_key_1507_ = lean_ctor_get(v___x_1506_, 0);
v_val_1508_ = lean_ctor_get(v___x_1506_, 1);
v___x_1509_ = lean_ptr_addr(v_x_1500_);
v___x_1510_ = lean_ptr_addr(v_key_1507_);
v___x_1511_ = lean_usize_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_box(0);
return v___x_1512_;
}
else
{
lean_object* v___x_1513_; 
lean_inc(v_val_1508_);
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_val_1508_);
return v___x_1513_;
}
}
case 1:
{
lean_object* v_node_1514_; size_t v___x_1515_; size_t v___x_1516_; 
v_node_1514_ = lean_ctor_get(v___x_1506_, 0);
v___x_1515_ = ((size_t)5ULL);
v___x_1516_ = lean_usize_shift_right(v_x_1499_, v___x_1515_);
v_x_1498_ = v_node_1514_;
v_x_1499_ = v___x_1516_;
goto _start;
}
default: 
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_box(0);
return v___x_1518_;
}
}
}
else
{
lean_object* v_ks_1519_; lean_object* v_vs_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_ks_1519_ = lean_ctor_get(v_x_1498_, 0);
v_vs_1520_ = lean_ctor_get(v_x_1498_, 1);
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1519_, v_vs_1520_, v___x_1521_, v_x_1500_);
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
size_t v_x_4175__boxed_1526_; lean_object* v_res_1527_; 
v_x_4175__boxed_1526_ = lean_unbox_usize(v_x_1524_);
lean_dec(v_x_1524_);
v_res_1527_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_1523_, v_x_4175__boxed_1526_, v_x_1525_);
lean_dec_ref(v_x_1525_);
lean_dec_ref(v_x_1523_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
size_t v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; uint64_t v___x_1533_; size_t v___x_1534_; lean_object* v___x_1535_; 
v___x_1530_ = lean_ptr_addr(v_x_1529_);
v___x_1531_ = ((size_t)3ULL);
v___x_1532_ = lean_usize_shift_right(v___x_1530_, v___x_1531_);
v___x_1533_ = lean_usize_to_uint64(v___x_1532_);
v___x_1534_ = lean_uint64_to_usize(v___x_1533_);
v___x_1535_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_1528_, v___x_1534_, v_x_1529_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_1536_, lean_object* v_x_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_1536_, v_x_1537_);
lean_dec_ref(v_x_1537_);
lean_dec_ref(v_x_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object* v_type_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1540_, v_a_1548_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1583_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1583_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1583_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_typeIdOf_1556_; lean_object* v___x_1557_; 
v_typeIdOf_1556_ = lean_ctor_get(v_a_1552_, 1);
lean_inc_ref(v_typeIdOf_1556_);
lean_dec(v_a_1552_);
v___x_1557_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_typeIdOf_1556_, v_type_1539_);
lean_dec_ref(v_typeIdOf_1556_);
if (lean_obj_tag(v___x_1557_) == 1)
{
lean_object* v_val_1558_; lean_object* v___x_1560_; 
lean_dec_ref(v_type_1539_);
v_val_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1558_);
lean_dec_ref_known(v___x_1557_, 1);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v_val_1558_);
v___x_1560_ = v___x_1554_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_val_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
else
{
lean_object* v___x_1562_; 
lean_dec(v___x_1557_);
lean_del_object(v___x_1554_);
lean_inc_ref(v_type_1539_);
v___x_1562_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___f_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc_n(v_a_1563_, 2);
lean_dec_ref_known(v___x_1562_, 1);
v___f_1564_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1564_, 0, v_type_1539_);
lean_closure_set(v___f_1564_, 1, v_a_1563_);
v___x_1565_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1566_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1565_, v___f_1564_, v_a_1540_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v___x_1566_, 0);
lean_dec(v_unused_1574_);
v___x_1568_ = v___x_1566_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_dec(v___x_1566_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v_a_1563_);
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1563_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec(v_a_1563_);
v_a_1575_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1566_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1566_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_dec_ref(v_type_1539_);
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v_type_1539_);
v_a_1584_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1551_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1551_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___boxed(lean_object* v_type_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec(v_a_1593_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(lean_object* v_00_u03b2_1605_, lean_object* v_x_1606_, lean_object* v_x_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_1606_, v_x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(v_00_u03b2_1609_, v_x_1610_, v_x_1611_);
lean_dec_ref(v_x_1611_);
lean_dec_ref(v_x_1610_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1(lean_object* v_00_u03b2_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_x_1614_, v_x_1615_, v_x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1618_, lean_object* v_x_1619_, size_t v_x_1620_, lean_object* v_x_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_1619_, v_x_1620_, v_x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_){
_start:
{
size_t v_x_4345__boxed_1627_; lean_object* v_res_1628_; 
v_x_4345__boxed_1627_ = lean_unbox_usize(v_x_1625_);
lean_dec(v_x_1625_);
v_res_1628_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(v_00_u03b2_1623_, v_x_1624_, v_x_4345__boxed_1627_, v_x_1626_);
lean_dec_ref(v_x_1626_);
lean_dec_ref(v_x_1624_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(lean_object* v_00_u03b2_1629_, lean_object* v_x_1630_, size_t v_x_1631_, size_t v_x_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_1630_, v_x_1631_, v_x_1632_, v_x_1633_, v_x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
size_t v_x_4356__boxed_1642_; size_t v_x_4357__boxed_1643_; lean_object* v_res_1644_; 
v_x_4356__boxed_1642_ = lean_unbox_usize(v_x_1638_);
lean_dec(v_x_1638_);
v_x_4357__boxed_1643_ = lean_unbox_usize(v_x_1639_);
lean_dec(v_x_1639_);
v_res_1644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(v_00_u03b2_1636_, v_x_1637_, v_x_4356__boxed_1642_, v_x_4357__boxed_1643_, v_x_1640_, v_x_1641_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1645_, lean_object* v_keys_1646_, lean_object* v_vals_1647_, lean_object* v_heq_1648_, lean_object* v_i_1649_, lean_object* v_k_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1646_, v_vals_1647_, v_i_1649_, v_k_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1652_, lean_object* v_keys_1653_, lean_object* v_vals_1654_, lean_object* v_heq_1655_, lean_object* v_i_1656_, lean_object* v_k_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1652_, v_keys_1653_, v_vals_1654_, v_heq_1655_, v_i_1656_, v_k_1657_);
lean_dec_ref(v_k_1657_);
lean_dec_ref(v_vals_1654_);
lean_dec_ref(v_keys_1653_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1659_, lean_object* v_n_1660_, lean_object* v_k_1661_, lean_object* v_v_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v_n_1660_, v_k_1661_, v_v_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1664_, size_t v_depth_1665_, lean_object* v_keys_1666_, lean_object* v_vals_1667_, lean_object* v_heq_1668_, lean_object* v_i_1669_, lean_object* v_entries_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_1665_, v_keys_1666_, v_vals_1667_, v_i_1669_, v_entries_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1672_, lean_object* v_depth_1673_, lean_object* v_keys_1674_, lean_object* v_vals_1675_, lean_object* v_heq_1676_, lean_object* v_i_1677_, lean_object* v_entries_1678_){
_start:
{
size_t v_depth_boxed_1679_; lean_object* v_res_1680_; 
v_depth_boxed_1679_ = lean_unbox_usize(v_depth_1673_);
lean_dec(v_depth_1673_);
v_res_1680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1672_, v_depth_boxed_1679_, v_keys_1674_, v_vals_1675_, v_heq_1676_, v_i_1677_, v_entries_1678_);
lean_dec_ref(v_vals_1675_);
lean_dec_ref(v_keys_1674_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_, lean_object* v_x_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1682_, v_x_1683_, v_x_1684_, v_x_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0(lean_object* v___x_1687_, lean_object* v_s_1688_){
_start:
{
lean_object* v_rings_1689_; lean_object* v_typeIdOf_1690_; lean_object* v_exprToRingId_1691_; lean_object* v_semirings_1692_; lean_object* v_stypeIdOf_1693_; lean_object* v_exprToSemiringId_1694_; lean_object* v_ncRings_1695_; lean_object* v_exprToNCRingId_1696_; lean_object* v_nctypeIdOf_1697_; lean_object* v_ncSemirings_1698_; lean_object* v_exprToNCSemiringId_1699_; lean_object* v_ncstypeIdOf_1700_; lean_object* v_steps_1701_; uint8_t v_reportedMaxDegreeIssue_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1710_; 
v_rings_1689_ = lean_ctor_get(v_s_1688_, 0);
v_typeIdOf_1690_ = lean_ctor_get(v_s_1688_, 1);
v_exprToRingId_1691_ = lean_ctor_get(v_s_1688_, 2);
v_semirings_1692_ = lean_ctor_get(v_s_1688_, 3);
v_stypeIdOf_1693_ = lean_ctor_get(v_s_1688_, 4);
v_exprToSemiringId_1694_ = lean_ctor_get(v_s_1688_, 5);
v_ncRings_1695_ = lean_ctor_get(v_s_1688_, 6);
v_exprToNCRingId_1696_ = lean_ctor_get(v_s_1688_, 7);
v_nctypeIdOf_1697_ = lean_ctor_get(v_s_1688_, 8);
v_ncSemirings_1698_ = lean_ctor_get(v_s_1688_, 9);
v_exprToNCSemiringId_1699_ = lean_ctor_get(v_s_1688_, 10);
v_ncstypeIdOf_1700_ = lean_ctor_get(v_s_1688_, 11);
v_steps_1701_ = lean_ctor_get(v_s_1688_, 12);
v_reportedMaxDegreeIssue_1702_ = lean_ctor_get_uint8(v_s_1688_, sizeof(void*)*13);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_s_1688_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1704_ = v_s_1688_;
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_steps_1701_);
lean_inc(v_ncstypeIdOf_1700_);
lean_inc(v_exprToNCSemiringId_1699_);
lean_inc(v_ncSemirings_1698_);
lean_inc(v_nctypeIdOf_1697_);
lean_inc(v_exprToNCRingId_1696_);
lean_inc(v_ncRings_1695_);
lean_inc(v_exprToSemiringId_1694_);
lean_inc(v_stypeIdOf_1693_);
lean_inc(v_semirings_1692_);
lean_inc(v_exprToRingId_1691_);
lean_inc(v_typeIdOf_1690_);
lean_inc(v_rings_1689_);
lean_dec(v_s_1688_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = lean_array_push(v_ncRings_1695_, v___x_1687_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 6, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_rings_1689_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_typeIdOf_1690_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_exprToRingId_1691_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v_semirings_1692_);
lean_ctor_set(v_reuseFailAlloc_1709_, 4, v_stypeIdOf_1693_);
lean_ctor_set(v_reuseFailAlloc_1709_, 5, v_exprToSemiringId_1694_);
lean_ctor_set(v_reuseFailAlloc_1709_, 6, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1709_, 7, v_exprToNCRingId_1696_);
lean_ctor_set(v_reuseFailAlloc_1709_, 8, v_nctypeIdOf_1697_);
lean_ctor_set(v_reuseFailAlloc_1709_, 9, v_ncSemirings_1698_);
lean_ctor_set(v_reuseFailAlloc_1709_, 10, v_exprToNCSemiringId_1699_);
lean_ctor_set(v_reuseFailAlloc_1709_, 11, v_ncstypeIdOf_1700_);
lean_ctor_set(v_reuseFailAlloc_1709_, 12, v_steps_1701_);
lean_ctor_set_uint8(v_reuseFailAlloc_1709_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1702_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(lean_object* v_type_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v___x_1723_; 
lean_inc_ref(v_type_1711_);
v___x_1723_ = l_Lean_Meta_getDecLevel(v_type_1711_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc_n(v_a_1724_, 2);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5));
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1727_, 0, v_a_1724_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
lean_inc_ref(v___x_1727_);
v___x_1728_ = l_Lean_mkConst(v___x_1725_, v___x_1727_);
lean_inc_ref(v_type_1711_);
v___x_1729_ = l_Lean_Expr_app___override(v___x_1728_, v_type_1711_);
v___x_1730_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1729_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1836_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1836_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1836_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
if (lean_obj_tag(v_a_1731_) == 1)
{
lean_object* v_toCold_1735_; lean_object* v_options_1736_; lean_object* v_val_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1831_; 
lean_del_object(v___x_1733_);
v_toCold_1735_ = lean_ctor_get(v_a_1720_, 0);
v_options_1736_ = lean_ctor_get(v_toCold_1735_, 2);
v_val_1737_ = lean_ctor_get(v_a_1731_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_a_1731_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1739_ = v_a_1731_;
v_isShared_1740_ = v_isSharedCheck_1831_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_val_1737_);
lean_dec(v_a_1731_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1831_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v_inheritedTraceOptions_1741_; uint8_t v_hasTrace_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; 
v_inheritedTraceOptions_1741_ = lean_ctor_get(v_toCold_1735_, 11);
v_hasTrace_1742_ = lean_ctor_get_uint8(v_options_1736_, sizeof(void*)*1);
v___x_1743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8));
v___x_1744_ = l_Lean_mkConst(v___x_1743_, v___x_1727_);
lean_inc(v_val_1737_);
lean_inc_ref(v_type_1711_);
v___x_1745_ = l_Lean_mkAppB(v___x_1744_, v_type_1711_, v_val_1737_);
if (v_hasTrace_1742_ == 0)
{
v___y_1747_ = v_a_1712_;
v___y_1748_ = v_a_1713_;
v___y_1749_ = v_a_1714_;
v___y_1750_ = v_a_1715_;
v___y_1751_ = v_a_1716_;
v___y_1752_ = v_a_1717_;
v___y_1753_ = v_a_1718_;
v___y_1754_ = v_a_1719_;
v___y_1755_ = v_a_1720_;
v___y_1756_ = v_a_1721_;
goto v___jp_1746_;
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1807_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16));
v___x_1808_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19);
v___x_1809_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1741_, v_options_1736_, v___x_1808_);
if (v___x_1809_ == 0)
{
v___y_1747_ = v_a_1712_;
v___y_1748_ = v_a_1713_;
v___y_1749_ = v_a_1714_;
v___y_1750_ = v_a_1715_;
v___y_1751_ = v_a_1716_;
v___y_1752_ = v_a_1717_;
v___y_1753_ = v_a_1718_;
v___y_1754_ = v_a_1719_;
v___y_1755_ = v_a_1720_;
v___y_1756_ = v_a_1721_;
goto v___jp_1746_;
}
else
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_Meta_Grind_updateLastTag(v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec_ref_known(v___x_1810_, 1);
v___x_1811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27);
lean_inc_ref(v_type_1711_);
v___x_1812_ = l_Lean_MessageData_ofExpr(v_type_1711_);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1811_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_1807_, v___x_1813_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_dec_ref_known(v___x_1814_, 1);
v___y_1747_ = v_a_1712_;
v___y_1748_ = v_a_1713_;
v___y_1749_ = v_a_1714_;
v___y_1750_ = v_a_1715_;
v___y_1751_ = v_a_1716_;
v___y_1752_ = v_a_1717_;
v___y_1753_ = v_a_1718_;
v___y_1754_ = v_a_1719_;
v___y_1755_ = v_a_1720_;
v___y_1756_ = v_a_1721_;
goto v___jp_1746_;
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec_ref(v___x_1745_);
lean_del_object(v___x_1739_);
lean_dec(v_val_1737_);
lean_dec(v_a_1724_);
lean_dec_ref(v_type_1711_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec_ref(v___x_1745_);
lean_del_object(v___x_1739_);
lean_dec(v_val_1737_);
lean_dec(v_a_1724_);
lean_dec_ref(v_type_1711_);
v_a_1823_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1810_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1810_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
v___jp_1746_:
{
lean_object* v___x_1757_; 
lean_inc_ref(v___x_1745_);
lean_inc_ref(v_type_1711_);
lean_inc(v_a_1724_);
v___x_1757_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_a_1724_, v_type_1711_, v___x_1745_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_1747_, v___y_1755_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v_ncRings_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___f_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v_ncRings_1761_ = lean_ctor_get(v_a_1760_, 6);
lean_inc_ref(v_ncRings_1761_);
lean_dec(v_a_1760_);
v___x_1762_ = lean_array_get_size(v_ncRings_1761_);
lean_dec_ref(v_ncRings_1761_);
v___x_1763_ = lean_box(0);
v___x_1764_ = lean_unsigned_to_nat(32u);
v___x_1765_ = lean_mk_empty_array_with_capacity(v___x_1764_);
lean_dec_ref(v___x_1765_);
v___x_1766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12);
v___x_1767_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13);
v___x_1768_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1762_);
lean_ctor_set(v___x_1768_, 1, v_type_1711_);
lean_ctor_set(v___x_1768_, 2, v_a_1724_);
lean_ctor_set(v___x_1768_, 3, v_val_1737_);
lean_ctor_set(v___x_1768_, 4, v___x_1745_);
lean_ctor_set(v___x_1768_, 5, v_a_1758_);
lean_ctor_set(v___x_1768_, 6, v___x_1763_);
lean_ctor_set(v___x_1768_, 7, v___x_1763_);
lean_ctor_set(v___x_1768_, 8, v___x_1763_);
lean_ctor_set(v___x_1768_, 9, v___x_1763_);
lean_ctor_set(v___x_1768_, 10, v___x_1763_);
lean_ctor_set(v___x_1768_, 11, v___x_1763_);
lean_ctor_set(v___x_1768_, 12, v___x_1763_);
lean_ctor_set(v___x_1768_, 13, v___x_1763_);
lean_ctor_set(v___x_1768_, 14, v___x_1766_);
lean_ctor_set(v___x_1768_, 15, v___x_1767_);
lean_ctor_set(v___x_1768_, 16, v___x_1767_);
v___f_1769_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1769_, 0, v___x_1768_);
v___x_1770_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1771_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1770_, v___f_1769_, v___y_1747_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1781_; 
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; 
v_unused_1782_ = lean_ctor_get(v___x_1771_, 0);
lean_dec(v_unused_1782_);
v___x_1773_ = v___x_1771_;
v_isShared_1774_ = v_isSharedCheck_1781_;
goto v_resetjp_1772_;
}
else
{
lean_dec(v___x_1771_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1781_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1762_);
v___x_1776_ = v___x_1739_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1762_);
v___x_1776_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1778_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1776_);
v___x_1778_ = v___x_1773_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_del_object(v___x_1739_);
v_a_1783_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1771_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1771_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v_a_1758_);
lean_dec_ref(v___x_1745_);
lean_del_object(v___x_1739_);
lean_dec(v_val_1737_);
lean_dec(v_a_1724_);
lean_dec_ref(v_type_1711_);
v_a_1791_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1759_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1759_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref(v___x_1745_);
lean_del_object(v___x_1739_);
lean_dec(v_val_1737_);
lean_dec(v_a_1724_);
lean_dec_ref(v_type_1711_);
v_a_1799_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1757_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1757_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
lean_dec(v_a_1731_);
lean_dec_ref_known(v___x_1727_, 2);
lean_dec(v_a_1724_);
lean_dec_ref(v_type_1711_);
v___x_1832_ = lean_box(0);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1832_);
v___x_1834_ = v___x_1733_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
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
lean_dec_ref_known(v___x_1727_, 2);
lean_dec(v_a_1724_);
lean_dec_ref(v_type_1711_);
v_a_1837_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1730_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1730_);
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
lean_dec_ref(v_type_1711_);
v_a_1845_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1723_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1723_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___boxed(lean_object* v_type_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec(v_a_1854_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0(lean_object* v_type_1866_, lean_object* v_a_1867_, lean_object* v_s_1868_){
_start:
{
lean_object* v_rings_1869_; lean_object* v_typeIdOf_1870_; lean_object* v_exprToRingId_1871_; lean_object* v_semirings_1872_; lean_object* v_stypeIdOf_1873_; lean_object* v_exprToSemiringId_1874_; lean_object* v_ncRings_1875_; lean_object* v_exprToNCRingId_1876_; lean_object* v_nctypeIdOf_1877_; lean_object* v_ncSemirings_1878_; lean_object* v_exprToNCSemiringId_1879_; lean_object* v_ncstypeIdOf_1880_; lean_object* v_steps_1881_; uint8_t v_reportedMaxDegreeIssue_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1890_; 
v_rings_1869_ = lean_ctor_get(v_s_1868_, 0);
v_typeIdOf_1870_ = lean_ctor_get(v_s_1868_, 1);
v_exprToRingId_1871_ = lean_ctor_get(v_s_1868_, 2);
v_semirings_1872_ = lean_ctor_get(v_s_1868_, 3);
v_stypeIdOf_1873_ = lean_ctor_get(v_s_1868_, 4);
v_exprToSemiringId_1874_ = lean_ctor_get(v_s_1868_, 5);
v_ncRings_1875_ = lean_ctor_get(v_s_1868_, 6);
v_exprToNCRingId_1876_ = lean_ctor_get(v_s_1868_, 7);
v_nctypeIdOf_1877_ = lean_ctor_get(v_s_1868_, 8);
v_ncSemirings_1878_ = lean_ctor_get(v_s_1868_, 9);
v_exprToNCSemiringId_1879_ = lean_ctor_get(v_s_1868_, 10);
v_ncstypeIdOf_1880_ = lean_ctor_get(v_s_1868_, 11);
v_steps_1881_ = lean_ctor_get(v_s_1868_, 12);
v_reportedMaxDegreeIssue_1882_ = lean_ctor_get_uint8(v_s_1868_, sizeof(void*)*13);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_s_1868_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1884_ = v_s_1868_;
v_isShared_1885_ = v_isSharedCheck_1890_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_steps_1881_);
lean_inc(v_ncstypeIdOf_1880_);
lean_inc(v_exprToNCSemiringId_1879_);
lean_inc(v_ncSemirings_1878_);
lean_inc(v_nctypeIdOf_1877_);
lean_inc(v_exprToNCRingId_1876_);
lean_inc(v_ncRings_1875_);
lean_inc(v_exprToSemiringId_1874_);
lean_inc(v_stypeIdOf_1873_);
lean_inc(v_semirings_1872_);
lean_inc(v_exprToRingId_1871_);
lean_inc(v_typeIdOf_1870_);
lean_inc(v_rings_1869_);
lean_dec(v_s_1868_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1890_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1886_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_nctypeIdOf_1877_, v_type_1866_, v_a_1867_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 8, v___x_1886_);
v___x_1888_ = v___x_1884_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_rings_1869_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_typeIdOf_1870_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_exprToRingId_1871_);
lean_ctor_set(v_reuseFailAlloc_1889_, 3, v_semirings_1872_);
lean_ctor_set(v_reuseFailAlloc_1889_, 4, v_stypeIdOf_1873_);
lean_ctor_set(v_reuseFailAlloc_1889_, 5, v_exprToSemiringId_1874_);
lean_ctor_set(v_reuseFailAlloc_1889_, 6, v_ncRings_1875_);
lean_ctor_set(v_reuseFailAlloc_1889_, 7, v_exprToNCRingId_1876_);
lean_ctor_set(v_reuseFailAlloc_1889_, 8, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1889_, 9, v_ncSemirings_1878_);
lean_ctor_set(v_reuseFailAlloc_1889_, 10, v_exprToNCSemiringId_1879_);
lean_ctor_set(v_reuseFailAlloc_1889_, 11, v_ncstypeIdOf_1880_);
lean_ctor_set(v_reuseFailAlloc_1889_, 12, v_steps_1881_);
lean_ctor_set_uint8(v_reuseFailAlloc_1889_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1882_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object* v_type_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1892_, v_a_1900_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1935_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1906_ = v___x_1903_;
v_isShared_1907_ = v_isSharedCheck_1935_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1935_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v_nctypeIdOf_1908_; lean_object* v___x_1909_; 
v_nctypeIdOf_1908_ = lean_ctor_get(v_a_1904_, 8);
lean_inc_ref(v_nctypeIdOf_1908_);
lean_dec(v_a_1904_);
v___x_1909_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_nctypeIdOf_1908_, v_type_1891_);
lean_dec_ref(v_nctypeIdOf_1908_);
if (lean_obj_tag(v___x_1909_) == 1)
{
lean_object* v_val_1910_; lean_object* v___x_1912_; 
lean_dec_ref(v_type_1891_);
v_val_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_val_1910_);
lean_dec_ref_known(v___x_1909_, 1);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v_val_1910_);
v___x_1912_ = v___x_1906_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_val_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
else
{
lean_object* v___x_1914_; 
lean_dec(v___x_1909_);
lean_del_object(v___x_1906_);
lean_inc_ref(v_type_1891_);
v___x_1914_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___f_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc_n(v_a_1915_, 2);
lean_dec_ref_known(v___x_1914_, 1);
v___f_1916_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1916_, 0, v_type_1891_);
lean_closure_set(v___f_1916_, 1, v_a_1915_);
v___x_1917_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1918_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1917_, v___f_1916_, v_a_1892_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; 
v_unused_1926_ = lean_ctor_get(v___x_1918_, 0);
lean_dec(v_unused_1926_);
v___x_1920_ = v___x_1918_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_dec(v___x_1918_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v_a_1915_);
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1915_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec(v_a_1915_);
v_a_1927_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1918_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1918_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_dec_ref(v_type_1891_);
return v___x_1914_;
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v_type_1891_);
v_a_1936_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1903_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1903_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___boxed(lean_object* v_type_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_type_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec(v_a_1945_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0(lean_object* v_semiringId_1957_, lean_object* v_s_1958_){
_start:
{
lean_object* v_toRing_1959_; lean_object* v_invFn_x3f_1960_; lean_object* v_commSemiringInst_1961_; lean_object* v_commRingInst_1962_; lean_object* v_noZeroDivInst_x3f_1963_; lean_object* v_fieldInst_x3f_1964_; lean_object* v_powIdentityInst_x3f_1965_; lean_object* v_denoteEntries_1966_; lean_object* v_nextId_1967_; lean_object* v_steps_1968_; lean_object* v_queue_1969_; lean_object* v_basis_1970_; lean_object* v_diseqs_1971_; uint8_t v_recheck_1972_; lean_object* v_invSet_1973_; lean_object* v_powIdentityVarCount_1974_; lean_object* v_numEq0_x3f_1975_; uint8_t v_numEq0Updated_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1984_; 
v_toRing_1959_ = lean_ctor_get(v_s_1958_, 0);
v_invFn_x3f_1960_ = lean_ctor_get(v_s_1958_, 1);
v_commSemiringInst_1961_ = lean_ctor_get(v_s_1958_, 3);
v_commRingInst_1962_ = lean_ctor_get(v_s_1958_, 4);
v_noZeroDivInst_x3f_1963_ = lean_ctor_get(v_s_1958_, 5);
v_fieldInst_x3f_1964_ = lean_ctor_get(v_s_1958_, 6);
v_powIdentityInst_x3f_1965_ = lean_ctor_get(v_s_1958_, 7);
v_denoteEntries_1966_ = lean_ctor_get(v_s_1958_, 8);
v_nextId_1967_ = lean_ctor_get(v_s_1958_, 9);
v_steps_1968_ = lean_ctor_get(v_s_1958_, 10);
v_queue_1969_ = lean_ctor_get(v_s_1958_, 11);
v_basis_1970_ = lean_ctor_get(v_s_1958_, 12);
v_diseqs_1971_ = lean_ctor_get(v_s_1958_, 13);
v_recheck_1972_ = lean_ctor_get_uint8(v_s_1958_, sizeof(void*)*17);
v_invSet_1973_ = lean_ctor_get(v_s_1958_, 14);
v_powIdentityVarCount_1974_ = lean_ctor_get(v_s_1958_, 15);
v_numEq0_x3f_1975_ = lean_ctor_get(v_s_1958_, 16);
v_numEq0Updated_1976_ = lean_ctor_get_uint8(v_s_1958_, sizeof(void*)*17 + 1);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_s_1958_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v_s_1958_, 2);
lean_dec(v_unused_1985_);
v___x_1978_ = v_s_1958_;
v_isShared_1979_ = v_isSharedCheck_1984_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_numEq0_x3f_1975_);
lean_inc(v_powIdentityVarCount_1974_);
lean_inc(v_invSet_1973_);
lean_inc(v_diseqs_1971_);
lean_inc(v_basis_1970_);
lean_inc(v_queue_1969_);
lean_inc(v_steps_1968_);
lean_inc(v_nextId_1967_);
lean_inc(v_denoteEntries_1966_);
lean_inc(v_powIdentityInst_x3f_1965_);
lean_inc(v_fieldInst_x3f_1964_);
lean_inc(v_noZeroDivInst_x3f_1963_);
lean_inc(v_commRingInst_1962_);
lean_inc(v_commSemiringInst_1961_);
lean_inc(v_invFn_x3f_1960_);
lean_inc(v_toRing_1959_);
lean_dec(v_s_1958_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1984_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v_semiringId_1957_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 2, v___x_1980_);
v___x_1982_ = v___x_1978_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_toRing_1959_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_invFn_x3f_1960_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1983_, 3, v_commSemiringInst_1961_);
lean_ctor_set(v_reuseFailAlloc_1983_, 4, v_commRingInst_1962_);
lean_ctor_set(v_reuseFailAlloc_1983_, 5, v_noZeroDivInst_x3f_1963_);
lean_ctor_set(v_reuseFailAlloc_1983_, 6, v_fieldInst_x3f_1964_);
lean_ctor_set(v_reuseFailAlloc_1983_, 7, v_powIdentityInst_x3f_1965_);
lean_ctor_set(v_reuseFailAlloc_1983_, 8, v_denoteEntries_1966_);
lean_ctor_set(v_reuseFailAlloc_1983_, 9, v_nextId_1967_);
lean_ctor_set(v_reuseFailAlloc_1983_, 10, v_steps_1968_);
lean_ctor_set(v_reuseFailAlloc_1983_, 11, v_queue_1969_);
lean_ctor_set(v_reuseFailAlloc_1983_, 12, v_basis_1970_);
lean_ctor_set(v_reuseFailAlloc_1983_, 13, v_diseqs_1971_);
lean_ctor_set(v_reuseFailAlloc_1983_, 14, v_invSet_1973_);
lean_ctor_set(v_reuseFailAlloc_1983_, 15, v_powIdentityVarCount_1974_);
lean_ctor_set(v_reuseFailAlloc_1983_, 16, v_numEq0_x3f_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*17, v_recheck_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*17 + 1, v_numEq0Updated_1976_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(lean_object* v_ringId_1986_, lean_object* v_semiringId_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v___f_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___f_1990_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1990_, 0, v_semiringId_1987_);
v___x_1991_ = 0;
v___x_1992_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1992_, 0, v_ringId_1986_);
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*1, v___x_1991_);
v___x_1993_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1990_, v___x_1992_, v_a_1988_);
lean_dec_ref_known(v___x_1992_, 1);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___boxed(lean_object* v_ringId_1994_, lean_object* v_semiringId_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_1994_, v_semiringId_1995_, v_a_1996_);
lean_dec(v_a_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(lean_object* v_ringId_1999_, lean_object* v_semiringId_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_1999_, v_semiringId_2000_, v_a_2001_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___boxed(lean_object* v_ringId_2013_, lean_object* v_semiringId_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(v_ringId_2013_, v_semiringId_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
lean_dec(v_a_2016_);
lean_dec(v_a_2015_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0(lean_object* v___x_2027_, lean_object* v_s_2028_){
_start:
{
lean_object* v_rings_2029_; lean_object* v_typeIdOf_2030_; lean_object* v_exprToRingId_2031_; lean_object* v_semirings_2032_; lean_object* v_stypeIdOf_2033_; lean_object* v_exprToSemiringId_2034_; lean_object* v_ncRings_2035_; lean_object* v_exprToNCRingId_2036_; lean_object* v_nctypeIdOf_2037_; lean_object* v_ncSemirings_2038_; lean_object* v_exprToNCSemiringId_2039_; lean_object* v_ncstypeIdOf_2040_; lean_object* v_steps_2041_; uint8_t v_reportedMaxDegreeIssue_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2050_; 
v_rings_2029_ = lean_ctor_get(v_s_2028_, 0);
v_typeIdOf_2030_ = lean_ctor_get(v_s_2028_, 1);
v_exprToRingId_2031_ = lean_ctor_get(v_s_2028_, 2);
v_semirings_2032_ = lean_ctor_get(v_s_2028_, 3);
v_stypeIdOf_2033_ = lean_ctor_get(v_s_2028_, 4);
v_exprToSemiringId_2034_ = lean_ctor_get(v_s_2028_, 5);
v_ncRings_2035_ = lean_ctor_get(v_s_2028_, 6);
v_exprToNCRingId_2036_ = lean_ctor_get(v_s_2028_, 7);
v_nctypeIdOf_2037_ = lean_ctor_get(v_s_2028_, 8);
v_ncSemirings_2038_ = lean_ctor_get(v_s_2028_, 9);
v_exprToNCSemiringId_2039_ = lean_ctor_get(v_s_2028_, 10);
v_ncstypeIdOf_2040_ = lean_ctor_get(v_s_2028_, 11);
v_steps_2041_ = lean_ctor_get(v_s_2028_, 12);
v_reportedMaxDegreeIssue_2042_ = lean_ctor_get_uint8(v_s_2028_, sizeof(void*)*13);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_s_2028_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2044_ = v_s_2028_;
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_steps_2041_);
lean_inc(v_ncstypeIdOf_2040_);
lean_inc(v_exprToNCSemiringId_2039_);
lean_inc(v_ncSemirings_2038_);
lean_inc(v_nctypeIdOf_2037_);
lean_inc(v_exprToNCRingId_2036_);
lean_inc(v_ncRings_2035_);
lean_inc(v_exprToSemiringId_2034_);
lean_inc(v_stypeIdOf_2033_);
lean_inc(v_semirings_2032_);
lean_inc(v_exprToRingId_2031_);
lean_inc(v_typeIdOf_2030_);
lean_inc(v_rings_2029_);
lean_dec(v_s_2028_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = lean_array_push(v_semirings_2032_, v___x_2027_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 3, v___x_2046_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_rings_2029_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_typeIdOf_2030_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_exprToRingId_2031_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_stypeIdOf_2033_);
lean_ctor_set(v_reuseFailAlloc_2049_, 5, v_exprToSemiringId_2034_);
lean_ctor_set(v_reuseFailAlloc_2049_, 6, v_ncRings_2035_);
lean_ctor_set(v_reuseFailAlloc_2049_, 7, v_exprToNCRingId_2036_);
lean_ctor_set(v_reuseFailAlloc_2049_, 8, v_nctypeIdOf_2037_);
lean_ctor_set(v_reuseFailAlloc_2049_, 9, v_ncSemirings_2038_);
lean_ctor_set(v_reuseFailAlloc_2049_, 10, v_exprToNCSemiringId_2039_);
lean_ctor_set(v_reuseFailAlloc_2049_, 11, v_ncstypeIdOf_2040_);
lean_ctor_set(v_reuseFailAlloc_2049_, 12, v_steps_2041_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2042_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v_ref_2057_; lean_object* v___x_2058_; lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2067_; 
v_ref_2057_ = lean_ctor_get(v___y_2054_, 2);
v___x_2058_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(v_msg_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2067_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2067_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
lean_inc(v_ref_2057_);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v_ref_2057_);
lean_ctor_set(v___x_2063_, 1, v_a_2059_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set_tag(v___x_2061_, 1);
lean_ctor_set(v___x_2061_, 0, v___x_2063_);
v___x_2065_ = v___x_2061_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2074_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___redArg___closed__0);
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
return v___x_2076_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1));
v___x_2079_ = l_Lean_stringToMessageData(v___x_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(lean_object* v_type_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v___x_2092_; 
lean_inc_ref(v_type_2080_);
v___x_2092_ = l_Lean_Meta_getDecLevel(v_type_2080_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc_n(v_a_2093_, 2);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8));
v___x_2095_ = lean_box(0);
v___x_2096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2096_, 0, v_a_2093_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
lean_inc_ref(v___x_2096_);
v___x_2097_ = l_Lean_mkConst(v___x_2094_, v___x_2096_);
lean_inc_ref(v_type_2080_);
v___x_2098_ = l_Lean_Expr_app___override(v___x_2097_, v_type_2080_);
v___x_2099_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2098_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2194_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2194_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2194_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
if (lean_obj_tag(v_a_2100_) == 1)
{
lean_object* v_val_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_del_object(v___x_2102_);
v_val_2104_ = lean_ctor_get(v_a_2100_, 0);
lean_inc_n(v_val_2104_, 2);
lean_dec_ref_known(v_a_2100_, 1);
v___x_2105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1));
lean_inc_ref(v___x_2096_);
v___x_2106_ = l_Lean_mkConst(v___x_2105_, v___x_2096_);
lean_inc_ref_n(v_type_2080_, 2);
v___x_2107_ = l_Lean_mkAppB(v___x_2106_, v_type_2080_, v_val_2104_);
v___x_2108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1));
v___x_2109_ = l_Lean_mkConst(v___x_2108_, v___x_2096_);
lean_inc_ref(v___x_2107_);
v___x_2110_ = l_Lean_mkAppB(v___x_2109_, v_type_2080_, v___x_2107_);
v___x_2111_ = l_Lean_Meta_Sym_canon(v___x_2110_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = l_Lean_Meta_Sym_shareCommon(v_a_2112_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2115_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc_n(v_a_2114_, 2);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_a_2114_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2115_, 1);
if (lean_obj_tag(v_a_2116_) == 1)
{
lean_object* v_val_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_a_2114_);
v_val_2117_ = lean_ctor_get(v_a_2116_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_a_2116_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2119_ = v_a_2116_;
v_isShared_2120_ = v_isSharedCheck_2169_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_val_2117_);
lean_dec(v_a_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2169_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2081_, v_a_2089_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v_semirings_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___f_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v_semirings_2123_ = lean_ctor_get(v_a_2122_, 3);
lean_inc_ref(v_semirings_2123_);
lean_dec(v_a_2122_);
v___x_2124_ = lean_array_get_size(v_semirings_2123_);
lean_dec_ref(v_semirings_2123_);
v___x_2125_ = lean_box(0);
v___x_2126_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0);
v___x_2127_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12);
v___x_2128_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2124_);
lean_ctor_set(v___x_2128_, 1, v_type_2080_);
lean_ctor_set(v___x_2128_, 2, v_a_2093_);
lean_ctor_set(v___x_2128_, 3, v___x_2107_);
lean_ctor_set(v___x_2128_, 4, v___x_2125_);
lean_ctor_set(v___x_2128_, 5, v___x_2125_);
lean_ctor_set(v___x_2128_, 6, v___x_2125_);
lean_ctor_set(v___x_2128_, 7, v___x_2125_);
lean_ctor_set(v___x_2128_, 8, v___x_2126_);
lean_ctor_set(v___x_2128_, 9, v___x_2127_);
lean_ctor_set(v___x_2128_, 10, v___x_2126_);
lean_inc(v_val_2117_);
v___x_2129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v_val_2117_);
lean_ctor_set(v___x_2129_, 2, v_val_2104_);
lean_ctor_set(v___x_2129_, 3, v___x_2125_);
lean_ctor_set(v___x_2129_, 4, v___x_2125_);
v___f_2130_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_2130_, 0, v___x_2129_);
v___x_2131_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2132_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2131_, v___f_2130_, v_a_2081_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2133_; 
lean_dec_ref_known(v___x_2132_, 1);
v___x_2133_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_val_2117_, v___x_2124_, v_a_2081_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2143_; 
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; 
v_unused_2144_ = lean_ctor_get(v___x_2133_, 0);
lean_dec(v_unused_2144_);
v___x_2135_ = v___x_2133_;
v_isShared_2136_ = v_isSharedCheck_2143_;
goto v_resetjp_2134_;
}
else
{
lean_dec(v___x_2133_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2143_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2124_);
v___x_2138_ = v___x_2119_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2124_);
v___x_2138_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2138_);
v___x_2140_ = v___x_2135_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_del_object(v___x_2119_);
v_a_2145_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2133_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2133_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_del_object(v___x_2119_);
lean_dec(v_val_2117_);
v_a_2153_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2132_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2132_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
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
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_del_object(v___x_2119_);
lean_dec(v_val_2117_);
lean_dec_ref(v___x_2107_);
lean_dec(v_val_2104_);
lean_dec(v_a_2093_);
lean_dec_ref(v_type_2080_);
v_a_2161_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2121_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2121_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec(v_a_2116_);
lean_dec_ref(v___x_2107_);
lean_dec(v_val_2104_);
lean_dec(v_a_2093_);
lean_dec_ref(v_type_2080_);
v___x_2170_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2);
v___x_2171_ = l_Lean_indentExpr(v_a_2114_);
v___x_2172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v___x_2172_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
return v___x_2173_;
}
}
else
{
lean_dec(v_a_2114_);
lean_dec_ref(v___x_2107_);
lean_dec(v_val_2104_);
lean_dec(v_a_2093_);
lean_dec_ref(v_type_2080_);
return v___x_2115_;
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec_ref(v___x_2107_);
lean_dec(v_val_2104_);
lean_dec(v_a_2093_);
lean_dec_ref(v_type_2080_);
v_a_2174_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2113_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2113_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec_ref(v___x_2107_);
lean_dec(v_val_2104_);
lean_dec(v_a_2093_);
lean_dec_ref(v_type_2080_);
v_a_2182_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2111_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2111_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2192_; 
lean_dec(v_a_2100_);
lean_dec_ref_known(v___x_2096_, 2);
lean_dec(v_a_2093_);
lean_dec_ref(v_type_2080_);
v___x_2190_ = lean_box(0);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2190_);
v___x_2192_ = v___x_2102_;
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
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec_ref_known(v___x_2096_, 2);
lean_dec(v_a_2093_);
lean_dec_ref(v_type_2080_);
v_a_2195_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2099_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2099_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec_ref(v_type_2080_);
v_a_2203_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2092_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2092_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___boxed(lean_object* v_type_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec(v_a_2212_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_2224_, lean_object* v_msg_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_2225_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_2238_, lean_object* v_msg_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(v_00_u03b1_2238_, v_msg_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec(v___y_2240_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0(lean_object* v_type_2252_, lean_object* v_a_2253_, lean_object* v_s_2254_){
_start:
{
lean_object* v_rings_2255_; lean_object* v_typeIdOf_2256_; lean_object* v_exprToRingId_2257_; lean_object* v_semirings_2258_; lean_object* v_stypeIdOf_2259_; lean_object* v_exprToSemiringId_2260_; lean_object* v_ncRings_2261_; lean_object* v_exprToNCRingId_2262_; lean_object* v_nctypeIdOf_2263_; lean_object* v_ncSemirings_2264_; lean_object* v_exprToNCSemiringId_2265_; lean_object* v_ncstypeIdOf_2266_; lean_object* v_steps_2267_; uint8_t v_reportedMaxDegreeIssue_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2276_; 
v_rings_2255_ = lean_ctor_get(v_s_2254_, 0);
v_typeIdOf_2256_ = lean_ctor_get(v_s_2254_, 1);
v_exprToRingId_2257_ = lean_ctor_get(v_s_2254_, 2);
v_semirings_2258_ = lean_ctor_get(v_s_2254_, 3);
v_stypeIdOf_2259_ = lean_ctor_get(v_s_2254_, 4);
v_exprToSemiringId_2260_ = lean_ctor_get(v_s_2254_, 5);
v_ncRings_2261_ = lean_ctor_get(v_s_2254_, 6);
v_exprToNCRingId_2262_ = lean_ctor_get(v_s_2254_, 7);
v_nctypeIdOf_2263_ = lean_ctor_get(v_s_2254_, 8);
v_ncSemirings_2264_ = lean_ctor_get(v_s_2254_, 9);
v_exprToNCSemiringId_2265_ = lean_ctor_get(v_s_2254_, 10);
v_ncstypeIdOf_2266_ = lean_ctor_get(v_s_2254_, 11);
v_steps_2267_ = lean_ctor_get(v_s_2254_, 12);
v_reportedMaxDegreeIssue_2268_ = lean_ctor_get_uint8(v_s_2254_, sizeof(void*)*13);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_s_2254_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2270_ = v_s_2254_;
v_isShared_2271_ = v_isSharedCheck_2276_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_steps_2267_);
lean_inc(v_ncstypeIdOf_2266_);
lean_inc(v_exprToNCSemiringId_2265_);
lean_inc(v_ncSemirings_2264_);
lean_inc(v_nctypeIdOf_2263_);
lean_inc(v_exprToNCRingId_2262_);
lean_inc(v_ncRings_2261_);
lean_inc(v_exprToSemiringId_2260_);
lean_inc(v_stypeIdOf_2259_);
lean_inc(v_semirings_2258_);
lean_inc(v_exprToRingId_2257_);
lean_inc(v_typeIdOf_2256_);
lean_inc(v_rings_2255_);
lean_dec(v_s_2254_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2276_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2272_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_stypeIdOf_2259_, v_type_2252_, v_a_2253_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 4, v___x_2272_);
v___x_2274_ = v___x_2270_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_rings_2255_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_typeIdOf_2256_);
lean_ctor_set(v_reuseFailAlloc_2275_, 2, v_exprToRingId_2257_);
lean_ctor_set(v_reuseFailAlloc_2275_, 3, v_semirings_2258_);
lean_ctor_set(v_reuseFailAlloc_2275_, 4, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2275_, 5, v_exprToSemiringId_2260_);
lean_ctor_set(v_reuseFailAlloc_2275_, 6, v_ncRings_2261_);
lean_ctor_set(v_reuseFailAlloc_2275_, 7, v_exprToNCRingId_2262_);
lean_ctor_set(v_reuseFailAlloc_2275_, 8, v_nctypeIdOf_2263_);
lean_ctor_set(v_reuseFailAlloc_2275_, 9, v_ncSemirings_2264_);
lean_ctor_set(v_reuseFailAlloc_2275_, 10, v_exprToNCSemiringId_2265_);
lean_ctor_set(v_reuseFailAlloc_2275_, 11, v_ncstypeIdOf_2266_);
lean_ctor_set(v_reuseFailAlloc_2275_, 12, v_steps_2267_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2268_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object* v_type_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2278_, v_a_2286_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2321_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2321_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2321_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_stypeIdOf_2294_; lean_object* v___x_2295_; 
v_stypeIdOf_2294_ = lean_ctor_get(v_a_2290_, 4);
lean_inc_ref(v_stypeIdOf_2294_);
lean_dec(v_a_2290_);
v___x_2295_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_stypeIdOf_2294_, v_type_2277_);
lean_dec_ref(v_stypeIdOf_2294_);
if (lean_obj_tag(v___x_2295_) == 1)
{
lean_object* v_val_2296_; lean_object* v___x_2298_; 
lean_dec_ref(v_type_2277_);
v_val_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_val_2296_);
lean_dec_ref_known(v___x_2295_, 1);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v_val_2296_);
v___x_2298_ = v___x_2292_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_val_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
else
{
lean_object* v___x_2300_; 
lean_dec(v___x_2295_);
lean_del_object(v___x_2292_);
lean_inc_ref(v_type_2277_);
v___x_2300_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___f_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc_n(v_a_2301_, 2);
lean_dec_ref_known(v___x_2300_, 1);
v___f_2302_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2302_, 0, v_type_2277_);
lean_closure_set(v___f_2302_, 1, v_a_2301_);
v___x_2303_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2304_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2303_, v___f_2302_, v_a_2278_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2311_ == 0)
{
lean_object* v_unused_2312_; 
v_unused_2312_ = lean_ctor_get(v___x_2304_, 0);
lean_dec(v_unused_2312_);
v___x_2306_ = v___x_2304_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_dec(v___x_2304_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v_a_2301_);
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2301_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec(v_a_2301_);
v_a_2313_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2304_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2304_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
else
{
lean_dec_ref(v_type_2277_);
return v___x_2300_;
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec_ref(v_type_2277_);
v_a_2322_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2289_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2289_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___boxed(lean_object* v_type_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_type_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec(v_a_2331_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0(lean_object* v___x_2343_, lean_object* v_s_2344_){
_start:
{
lean_object* v_rings_2345_; lean_object* v_typeIdOf_2346_; lean_object* v_exprToRingId_2347_; lean_object* v_semirings_2348_; lean_object* v_stypeIdOf_2349_; lean_object* v_exprToSemiringId_2350_; lean_object* v_ncRings_2351_; lean_object* v_exprToNCRingId_2352_; lean_object* v_nctypeIdOf_2353_; lean_object* v_ncSemirings_2354_; lean_object* v_exprToNCSemiringId_2355_; lean_object* v_ncstypeIdOf_2356_; lean_object* v_steps_2357_; uint8_t v_reportedMaxDegreeIssue_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2366_; 
v_rings_2345_ = lean_ctor_get(v_s_2344_, 0);
v_typeIdOf_2346_ = lean_ctor_get(v_s_2344_, 1);
v_exprToRingId_2347_ = lean_ctor_get(v_s_2344_, 2);
v_semirings_2348_ = lean_ctor_get(v_s_2344_, 3);
v_stypeIdOf_2349_ = lean_ctor_get(v_s_2344_, 4);
v_exprToSemiringId_2350_ = lean_ctor_get(v_s_2344_, 5);
v_ncRings_2351_ = lean_ctor_get(v_s_2344_, 6);
v_exprToNCRingId_2352_ = lean_ctor_get(v_s_2344_, 7);
v_nctypeIdOf_2353_ = lean_ctor_get(v_s_2344_, 8);
v_ncSemirings_2354_ = lean_ctor_get(v_s_2344_, 9);
v_exprToNCSemiringId_2355_ = lean_ctor_get(v_s_2344_, 10);
v_ncstypeIdOf_2356_ = lean_ctor_get(v_s_2344_, 11);
v_steps_2357_ = lean_ctor_get(v_s_2344_, 12);
v_reportedMaxDegreeIssue_2358_ = lean_ctor_get_uint8(v_s_2344_, sizeof(void*)*13);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_s_2344_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2360_ = v_s_2344_;
v_isShared_2361_ = v_isSharedCheck_2366_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_steps_2357_);
lean_inc(v_ncstypeIdOf_2356_);
lean_inc(v_exprToNCSemiringId_2355_);
lean_inc(v_ncSemirings_2354_);
lean_inc(v_nctypeIdOf_2353_);
lean_inc(v_exprToNCRingId_2352_);
lean_inc(v_ncRings_2351_);
lean_inc(v_exprToSemiringId_2350_);
lean_inc(v_stypeIdOf_2349_);
lean_inc(v_semirings_2348_);
lean_inc(v_exprToRingId_2347_);
lean_inc(v_typeIdOf_2346_);
lean_inc(v_rings_2345_);
lean_dec(v_s_2344_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2366_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2362_ = lean_array_push(v_ncSemirings_2354_, v___x_2343_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 9, v___x_2362_);
v___x_2364_ = v___x_2360_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_rings_2345_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_typeIdOf_2346_);
lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_exprToRingId_2347_);
lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_semirings_2348_);
lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_stypeIdOf_2349_);
lean_ctor_set(v_reuseFailAlloc_2365_, 5, v_exprToSemiringId_2350_);
lean_ctor_set(v_reuseFailAlloc_2365_, 6, v_ncRings_2351_);
lean_ctor_set(v_reuseFailAlloc_2365_, 7, v_exprToNCRingId_2352_);
lean_ctor_set(v_reuseFailAlloc_2365_, 8, v_nctypeIdOf_2353_);
lean_ctor_set(v_reuseFailAlloc_2365_, 9, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2365_, 10, v_exprToNCSemiringId_2355_);
lean_ctor_set(v_reuseFailAlloc_2365_, 11, v_ncstypeIdOf_2356_);
lean_ctor_set(v_reuseFailAlloc_2365_, 12, v_steps_2357_);
lean_ctor_set_uint8(v_reuseFailAlloc_2365_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2358_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(lean_object* v_type_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v___x_2375_; 
lean_inc_ref(v_type_2367_);
v___x_2375_ = l_Lean_Meta_getDecLevel(v_type_2367_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc_n(v_a_2376_, 2);
lean_dec_ref_known(v___x_2375_, 1);
v___x_2377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7));
v___x_2378_ = lean_box(0);
v___x_2379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2379_, 0, v_a_2376_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = l_Lean_mkConst(v___x_2377_, v___x_2379_);
lean_inc_ref(v_type_2367_);
v___x_2381_ = l_Lean_Expr_app___override(v___x_2380_, v_type_2367_);
v___x_2382_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2381_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2436_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2385_ = v___x_2382_;
v_isShared_2386_ = v_isSharedCheck_2436_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2436_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
if (lean_obj_tag(v_a_2383_) == 1)
{
lean_object* v_val_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2431_; 
lean_del_object(v___x_2385_);
v_val_2387_ = lean_ctor_get(v_a_2383_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_a_2383_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2389_ = v_a_2383_;
v_isShared_2390_ = v_isSharedCheck_2431_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_val_2387_);
lean_dec(v_a_2383_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2431_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2368_, v_a_2372_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v_ncSemirings_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___f_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v_ncSemirings_2393_ = lean_ctor_get(v_a_2392_, 9);
lean_inc_ref(v_ncSemirings_2393_);
lean_dec(v_a_2392_);
v___x_2394_ = lean_array_get_size(v_ncSemirings_2393_);
lean_dec_ref(v_ncSemirings_2393_);
v___x_2395_ = lean_box(0);
v___x_2396_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0);
v___x_2397_ = lean_unsigned_to_nat(32u);
v___x_2398_ = lean_mk_empty_array_with_capacity(v___x_2397_);
lean_dec_ref(v___x_2398_);
v___x_2399_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12);
v___x_2400_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2394_);
lean_ctor_set(v___x_2400_, 1, v_type_2367_);
lean_ctor_set(v___x_2400_, 2, v_a_2376_);
lean_ctor_set(v___x_2400_, 3, v_val_2387_);
lean_ctor_set(v___x_2400_, 4, v___x_2395_);
lean_ctor_set(v___x_2400_, 5, v___x_2395_);
lean_ctor_set(v___x_2400_, 6, v___x_2395_);
lean_ctor_set(v___x_2400_, 7, v___x_2395_);
lean_ctor_set(v___x_2400_, 8, v___x_2396_);
lean_ctor_set(v___x_2400_, 9, v___x_2399_);
lean_ctor_set(v___x_2400_, 10, v___x_2396_);
v___f_2401_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2401_, 0, v___x_2400_);
v___x_2402_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2403_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2402_, v___f_2401_, v_a_2368_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2413_; 
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; 
v_unused_2414_ = lean_ctor_get(v___x_2403_, 0);
lean_dec(v_unused_2414_);
v___x_2405_ = v___x_2403_;
v_isShared_2406_ = v_isSharedCheck_2413_;
goto v_resetjp_2404_;
}
else
{
lean_dec(v___x_2403_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2413_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2394_);
v___x_2408_ = v___x_2389_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2394_);
v___x_2408_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2410_; 
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2408_);
v___x_2410_ = v___x_2405_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_del_object(v___x_2389_);
v_a_2415_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2403_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2403_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_del_object(v___x_2389_);
lean_dec(v_val_2387_);
lean_dec(v_a_2376_);
lean_dec_ref(v_type_2367_);
v_a_2423_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2391_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2391_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2434_; 
lean_dec(v_a_2383_);
lean_dec(v_a_2376_);
lean_dec_ref(v_type_2367_);
v___x_2432_ = lean_box(0);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2432_);
v___x_2434_ = v___x_2385_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec(v_a_2376_);
lean_dec_ref(v_type_2367_);
v_a_2437_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2382_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2382_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v_type_2367_);
v_a_2445_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2375_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2375_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___boxed(lean_object* v_type_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec(v_a_2454_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(lean_object* v_type_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_2462_, v_a_2463_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___boxed(lean_object* v_type_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(v_type_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
lean_dec(v_a_2477_);
lean_dec(v_a_2476_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0(lean_object* v_type_2488_, lean_object* v_a_2489_, lean_object* v_s_2490_){
_start:
{
lean_object* v_rings_2491_; lean_object* v_typeIdOf_2492_; lean_object* v_exprToRingId_2493_; lean_object* v_semirings_2494_; lean_object* v_stypeIdOf_2495_; lean_object* v_exprToSemiringId_2496_; lean_object* v_ncRings_2497_; lean_object* v_exprToNCRingId_2498_; lean_object* v_nctypeIdOf_2499_; lean_object* v_ncSemirings_2500_; lean_object* v_exprToNCSemiringId_2501_; lean_object* v_ncstypeIdOf_2502_; lean_object* v_steps_2503_; uint8_t v_reportedMaxDegreeIssue_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2512_; 
v_rings_2491_ = lean_ctor_get(v_s_2490_, 0);
v_typeIdOf_2492_ = lean_ctor_get(v_s_2490_, 1);
v_exprToRingId_2493_ = lean_ctor_get(v_s_2490_, 2);
v_semirings_2494_ = lean_ctor_get(v_s_2490_, 3);
v_stypeIdOf_2495_ = lean_ctor_get(v_s_2490_, 4);
v_exprToSemiringId_2496_ = lean_ctor_get(v_s_2490_, 5);
v_ncRings_2497_ = lean_ctor_get(v_s_2490_, 6);
v_exprToNCRingId_2498_ = lean_ctor_get(v_s_2490_, 7);
v_nctypeIdOf_2499_ = lean_ctor_get(v_s_2490_, 8);
v_ncSemirings_2500_ = lean_ctor_get(v_s_2490_, 9);
v_exprToNCSemiringId_2501_ = lean_ctor_get(v_s_2490_, 10);
v_ncstypeIdOf_2502_ = lean_ctor_get(v_s_2490_, 11);
v_steps_2503_ = lean_ctor_get(v_s_2490_, 12);
v_reportedMaxDegreeIssue_2504_ = lean_ctor_get_uint8(v_s_2490_, sizeof(void*)*13);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_s_2490_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2506_ = v_s_2490_;
v_isShared_2507_ = v_isSharedCheck_2512_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_steps_2503_);
lean_inc(v_ncstypeIdOf_2502_);
lean_inc(v_exprToNCSemiringId_2501_);
lean_inc(v_ncSemirings_2500_);
lean_inc(v_nctypeIdOf_2499_);
lean_inc(v_exprToNCRingId_2498_);
lean_inc(v_ncRings_2497_);
lean_inc(v_exprToSemiringId_2496_);
lean_inc(v_stypeIdOf_2495_);
lean_inc(v_semirings_2494_);
lean_inc(v_exprToRingId_2493_);
lean_inc(v_typeIdOf_2492_);
lean_inc(v_rings_2491_);
lean_dec(v_s_2490_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2512_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2508_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_ncstypeIdOf_2502_, v_type_2488_, v_a_2489_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 11, v___x_2508_);
v___x_2510_ = v___x_2506_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_rings_2491_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_typeIdOf_2492_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v_exprToRingId_2493_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v_semirings_2494_);
lean_ctor_set(v_reuseFailAlloc_2511_, 4, v_stypeIdOf_2495_);
lean_ctor_set(v_reuseFailAlloc_2511_, 5, v_exprToSemiringId_2496_);
lean_ctor_set(v_reuseFailAlloc_2511_, 6, v_ncRings_2497_);
lean_ctor_set(v_reuseFailAlloc_2511_, 7, v_exprToNCRingId_2498_);
lean_ctor_set(v_reuseFailAlloc_2511_, 8, v_nctypeIdOf_2499_);
lean_ctor_set(v_reuseFailAlloc_2511_, 9, v_ncSemirings_2500_);
lean_ctor_set(v_reuseFailAlloc_2511_, 10, v_exprToNCSemiringId_2501_);
lean_ctor_set(v_reuseFailAlloc_2511_, 11, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2511_, 12, v_steps_2503_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2504_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object* v_type_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2514_, v_a_2518_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2553_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2553_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2553_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v_ncstypeIdOf_2526_; lean_object* v___x_2527_; 
v_ncstypeIdOf_2526_ = lean_ctor_get(v_a_2522_, 11);
lean_inc_ref(v_ncstypeIdOf_2526_);
lean_dec(v_a_2522_);
v___x_2527_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_ncstypeIdOf_2526_, v_type_2513_);
lean_dec_ref(v_ncstypeIdOf_2526_);
if (lean_obj_tag(v___x_2527_) == 1)
{
lean_object* v_val_2528_; lean_object* v___x_2530_; 
lean_dec_ref(v_type_2513_);
v_val_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_val_2528_);
lean_dec_ref_known(v___x_2527_, 1);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v_val_2528_);
v___x_2530_ = v___x_2524_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_val_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
else
{
lean_object* v___x_2532_; 
lean_dec(v___x_2527_);
lean_del_object(v___x_2524_);
lean_inc_ref(v_type_2513_);
v___x_2532_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___f_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc_n(v_a_2533_, 2);
lean_dec_ref_known(v___x_2532_, 1);
v___f_2534_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2534_, 0, v_type_2513_);
lean_closure_set(v___f_2534_, 1, v_a_2533_);
v___x_2535_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2536_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2535_, v___f_2534_, v_a_2514_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v___x_2536_, 0);
lean_dec(v_unused_2544_);
v___x_2538_ = v___x_2536_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_dec(v___x_2536_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v_a_2533_);
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2533_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_a_2533_);
v_a_2545_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2536_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2536_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
else
{
lean_dec_ref(v_type_2513_);
return v___x_2532_;
}
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v_type_2513_);
v_a_2554_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2521_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2521_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___boxed(lean_object* v_type_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec(v_a_2564_);
lean_dec(v_a_2563_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(lean_object* v_type_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_2571_, v_a_2572_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___boxed(lean_object* v_type_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(v_type_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec(v_a_2585_);
return v_res_2596_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(uint8_t builtin);
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
