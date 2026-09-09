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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(17, 56, 209, 254, 185, 203, 153, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toCommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(134, 95, 181, 253, 18, 104, 213, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "PowIdentity available: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "NoNatZeroDivisors available: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "new ring: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__29;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(134, 3, 13, 60, 96, 160, 201, 59)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__50_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__57_value),LEAN_SCALAR_PTR_LITERAL(194, 21, 126, 159, 192, 171, 59, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0(lean_object* v___x_9_, lean_object* v_____do__lift_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v_toCold_22_; lean_object* v_options_23_; uint8_t v_hasTrace_24_; 
v_toCold_22_ = lean_ctor_get(v___y_19_, 0);
v_options_23_ = lean_ctor_get(v_toCold_22_, 2);
v_hasTrace_24_ = lean_ctor_get_uint8(v_options_23_, sizeof(void*)*1);
if (v_hasTrace_24_ == 0)
{
lean_object* v___x_25_; lean_object* v___x_26_; 
lean_dec(v___x_9_);
v___x_25_ = lean_box(v_hasTrace_24_);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_27_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0___closed__1));
v___x_28_ = l_Lean_Name_append(v___x_27_, v___x_9_);
v___x_29_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_10_, v_options_23_, v___x_28_);
lean_dec(v___x_28_);
v___x_30_ = lean_box(v___x_29_);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0___boxed(lean_object* v___x_32_, lean_object* v_____do__lift_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0(v___x_32_, v_____do__lift_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
lean_dec(v___y_35_);
lean_dec(v___y_34_);
lean_dec_ref(v_____do__lift_33_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1(lean_object* v___x_46_, lean_object* v_s_47_){
_start:
{
lean_object* v_rings_48_; lean_object* v_typeIdOf_49_; lean_object* v_exprToRingId_50_; lean_object* v_semirings_51_; lean_object* v_stypeIdOf_52_; lean_object* v_exprToSemiringId_53_; lean_object* v_ncRings_54_; lean_object* v_exprToNCRingId_55_; lean_object* v_nctypeIdOf_56_; lean_object* v_ncSemirings_57_; lean_object* v_exprToNCSemiringId_58_; lean_object* v_ncstypeIdOf_59_; lean_object* v_steps_60_; uint8_t v_reportedMaxDegreeIssue_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_69_; 
v_rings_48_ = lean_ctor_get(v_s_47_, 0);
v_typeIdOf_49_ = lean_ctor_get(v_s_47_, 1);
v_exprToRingId_50_ = lean_ctor_get(v_s_47_, 2);
v_semirings_51_ = lean_ctor_get(v_s_47_, 3);
v_stypeIdOf_52_ = lean_ctor_get(v_s_47_, 4);
v_exprToSemiringId_53_ = lean_ctor_get(v_s_47_, 5);
v_ncRings_54_ = lean_ctor_get(v_s_47_, 6);
v_exprToNCRingId_55_ = lean_ctor_get(v_s_47_, 7);
v_nctypeIdOf_56_ = lean_ctor_get(v_s_47_, 8);
v_ncSemirings_57_ = lean_ctor_get(v_s_47_, 9);
v_exprToNCSemiringId_58_ = lean_ctor_get(v_s_47_, 10);
v_ncstypeIdOf_59_ = lean_ctor_get(v_s_47_, 11);
v_steps_60_ = lean_ctor_get(v_s_47_, 12);
v_reportedMaxDegreeIssue_61_ = lean_ctor_get_uint8(v_s_47_, sizeof(void*)*13);
v_isSharedCheck_69_ = !lean_is_exclusive(v_s_47_);
if (v_isSharedCheck_69_ == 0)
{
v___x_63_ = v_s_47_;
v_isShared_64_ = v_isSharedCheck_69_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_steps_60_);
lean_inc(v_ncstypeIdOf_59_);
lean_inc(v_exprToNCSemiringId_58_);
lean_inc(v_ncSemirings_57_);
lean_inc(v_nctypeIdOf_56_);
lean_inc(v_exprToNCRingId_55_);
lean_inc(v_ncRings_54_);
lean_inc(v_exprToSemiringId_53_);
lean_inc(v_stypeIdOf_52_);
lean_inc(v_semirings_51_);
lean_inc(v_exprToRingId_50_);
lean_inc(v_typeIdOf_49_);
lean_inc(v_rings_48_);
lean_dec(v_s_47_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_69_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_65_ = lean_array_push(v_rings_48_, v___x_46_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v___x_65_);
v___x_67_ = v___x_63_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_typeIdOf_49_);
lean_ctor_set(v_reuseFailAlloc_68_, 2, v_exprToRingId_50_);
lean_ctor_set(v_reuseFailAlloc_68_, 3, v_semirings_51_);
lean_ctor_set(v_reuseFailAlloc_68_, 4, v_stypeIdOf_52_);
lean_ctor_set(v_reuseFailAlloc_68_, 5, v_exprToSemiringId_53_);
lean_ctor_set(v_reuseFailAlloc_68_, 6, v_ncRings_54_);
lean_ctor_set(v_reuseFailAlloc_68_, 7, v_exprToNCRingId_55_);
lean_ctor_set(v_reuseFailAlloc_68_, 8, v_nctypeIdOf_56_);
lean_ctor_set(v_reuseFailAlloc_68_, 9, v_ncSemirings_57_);
lean_ctor_set(v_reuseFailAlloc_68_, 10, v_exprToNCSemiringId_58_);
lean_ctor_set(v_reuseFailAlloc_68_, 11, v_ncstypeIdOf_59_);
lean_ctor_set(v_reuseFailAlloc_68_, 12, v_steps_60_);
lean_ctor_set_uint8(v_reuseFailAlloc_68_, sizeof(void*)*13, v_reportedMaxDegreeIssue_61_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(lean_object* v_msgData_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_76_; lean_object* v_env_77_; lean_object* v___x_78_; lean_object* v_toCold_79_; lean_object* v_mctx_80_; lean_object* v_lctx_81_; lean_object* v_options_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_76_ = lean_st_ref_get(v___y_74_);
v_env_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_env_77_);
lean_dec(v___x_76_);
v___x_78_ = lean_st_ref_get(v___y_72_);
v_toCold_79_ = lean_ctor_get(v___y_73_, 0);
v_mctx_80_ = lean_ctor_get(v___x_78_, 0);
lean_inc_ref(v_mctx_80_);
lean_dec(v___x_78_);
v_lctx_81_ = lean_ctor_get(v___y_71_, 2);
v_options_82_ = lean_ctor_get(v_toCold_79_, 2);
lean_inc_ref(v_options_82_);
lean_inc_ref(v_lctx_81_);
v___x_83_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_83_, 0, v_env_77_);
lean_ctor_set(v___x_83_, 1, v_mctx_80_);
lean_ctor_set(v___x_83_, 2, v_lctx_81_);
lean_ctor_set(v___x_83_, 3, v_options_82_);
v___x_84_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v_msgData_70_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1___boxed(lean_object* v_msgData_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(v_msgData_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_92_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_93_; double v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_float_of_nat(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(lean_object* v_cls_98_, lean_object* v_msg_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_ref_105_; lean_object* v___x_106_; lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_151_; 
v_ref_105_ = lean_ctor_get(v___y_102_, 2);
v___x_106_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(v_msg_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_151_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_151_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_151_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v_traceState_112_; lean_object* v_env_113_; lean_object* v_nextMacroScope_114_; lean_object* v_ngen_115_; lean_object* v_auxDeclNGen_116_; lean_object* v_cache_117_; lean_object* v_messages_118_; lean_object* v_infoState_119_; lean_object* v_snapshotTasks_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_150_; 
v___x_111_ = lean_st_ref_take(v___y_103_);
v_traceState_112_ = lean_ctor_get(v___x_111_, 4);
v_env_113_ = lean_ctor_get(v___x_111_, 0);
v_nextMacroScope_114_ = lean_ctor_get(v___x_111_, 1);
v_ngen_115_ = lean_ctor_get(v___x_111_, 2);
v_auxDeclNGen_116_ = lean_ctor_get(v___x_111_, 3);
v_cache_117_ = lean_ctor_get(v___x_111_, 5);
v_messages_118_ = lean_ctor_get(v___x_111_, 6);
v_infoState_119_ = lean_ctor_get(v___x_111_, 7);
v_snapshotTasks_120_ = lean_ctor_get(v___x_111_, 8);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_150_ == 0)
{
v___x_122_ = v___x_111_;
v_isShared_123_ = v_isSharedCheck_150_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_snapshotTasks_120_);
lean_inc(v_infoState_119_);
lean_inc(v_messages_118_);
lean_inc(v_cache_117_);
lean_inc(v_traceState_112_);
lean_inc(v_auxDeclNGen_116_);
lean_inc(v_ngen_115_);
lean_inc(v_nextMacroScope_114_);
lean_inc(v_env_113_);
lean_dec(v___x_111_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_150_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
uint64_t v_tid_124_; lean_object* v_traces_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_149_; 
v_tid_124_ = lean_ctor_get_uint64(v_traceState_112_, sizeof(void*)*1);
v_traces_125_ = lean_ctor_get(v_traceState_112_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_traceState_112_);
if (v_isSharedCheck_149_ == 0)
{
v___x_127_ = v_traceState_112_;
v_isShared_128_ = v_isSharedCheck_149_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_traces_125_);
lean_dec(v_traceState_112_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_149_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; double v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_129_ = lean_box(0);
v___x_130_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__0);
v___x_131_ = 0;
v___x_132_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__1));
v___x_133_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_133_, 0, v_cls_98_);
lean_ctor_set(v___x_133_, 1, v___x_129_);
lean_ctor_set(v___x_133_, 2, v___x_132_);
lean_ctor_set_float(v___x_133_, sizeof(void*)*3, v___x_130_);
lean_ctor_set_float(v___x_133_, sizeof(void*)*3 + 8, v___x_130_);
lean_ctor_set_uint8(v___x_133_, sizeof(void*)*3 + 16, v___x_131_);
v___x_134_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___closed__2));
v___x_135_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v_a_107_);
lean_ctor_set(v___x_135_, 2, v___x_134_);
lean_inc(v_ref_105_);
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v_ref_105_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = l_Lean_PersistentArray_push___redArg(v_traces_125_, v___x_136_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_137_);
v___x_139_ = v___x_127_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_137_);
lean_ctor_set_uint64(v_reuseFailAlloc_148_, sizeof(void*)*1, v_tid_124_);
v___x_139_ = v_reuseFailAlloc_148_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_141_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 4, v___x_139_);
v___x_141_ = v___x_122_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_env_113_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_nextMacroScope_114_);
lean_ctor_set(v_reuseFailAlloc_147_, 2, v_ngen_115_);
lean_ctor_set(v_reuseFailAlloc_147_, 3, v_auxDeclNGen_116_);
lean_ctor_set(v_reuseFailAlloc_147_, 4, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_147_, 5, v_cache_117_);
lean_ctor_set(v_reuseFailAlloc_147_, 6, v_messages_118_);
lean_ctor_set(v_reuseFailAlloc_147_, 7, v_infoState_119_);
lean_ctor_set(v_reuseFailAlloc_147_, 8, v_snapshotTasks_120_);
v___x_141_ = v_reuseFailAlloc_147_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_142_ = lean_st_ref_put(v___y_103_, v___x_141_);
v___x_143_ = lean_box(0);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_143_);
v___x_145_ = v___x_109_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg___boxed(lean_object* v_cls_152_, lean_object* v_msg_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v_cls_152_, v_msg_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14(void){
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15(void){
_start:
{
size_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_194_ = ((size_t)5ULL);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_unsigned_to_nat(32u);
v___x_197_ = lean_mk_empty_array_with_capacity(v___x_196_);
v___x_198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__14);
v___x_199_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
lean_ctor_set(v___x_199_, 2, v___x_195_);
lean_ctor_set(v___x_199_, 3, v___x_195_);
lean_ctor_set_usize(v___x_199_, 4, v___x_194_);
return v___x_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__16);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18(void){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__0(lean_box(0));
return v___x_203_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6));
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0___closed__1));
v___x_211_ = l_Lean_Name_append(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__22));
v___x_214_ = l_Lean_stringToMessageData(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__26));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__29(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__28));
v___x_222_ = l_Lean_stringToMessageData(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(lean_object* v_type_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___x_235_; 
lean_inc_ref(v_type_223_);
v___x_235_ = l_Lean_Meta_getDecLevel(v_type_223_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc_n(v_a_236_, 2);
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3));
v___x_238_ = lean_box(0);
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v_a_236_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
lean_inc_ref(v___x_239_);
v___x_240_ = l_Lean_mkConst(v___x_237_, v___x_239_);
lean_inc_ref(v_type_223_);
v___x_241_ = l_Lean_Expr_app___override(v___x_240_, v_type_223_);
v___x_242_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_241_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_507_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_507_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_507_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_507_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
if (lean_obj_tag(v_a_243_) == 1)
{
lean_object* v_toCold_247_; lean_object* v_val_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_502_; 
lean_del_object(v___x_245_);
v_toCold_247_ = lean_ctor_get(v_a_232_, 0);
v_val_248_ = lean_ctor_get(v_a_243_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_a_243_);
if (v_isSharedCheck_502_ == 0)
{
v___x_250_ = v_a_243_;
v_isShared_251_ = v_isSharedCheck_502_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_val_248_);
lean_dec(v_a_243_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_502_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v_inheritedTraceOptions_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_501_; 
v_inheritedTraceOptions_252_ = lean_ctor_get(v_toCold_247_, 11);
v___x_253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6));
v___x_254_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0(v___x_253_, v_inheritedTraceOptions_252_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_501_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_501_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_501_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; uint8_t v___x_479_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8));
lean_inc_ref_n(v___x_239_, 3);
v___x_260_ = l_Lean_mkConst(v___x_259_, v___x_239_);
lean_inc(v_val_248_);
lean_inc_ref_n(v_type_223_, 3);
v___x_261_ = l_Lean_mkAppB(v___x_260_, v_type_223_, v_val_248_);
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11));
v___x_263_ = l_Lean_mkConst(v___x_262_, v___x_239_);
lean_inc_ref(v___x_261_);
v___x_264_ = l_Lean_mkAppB(v___x_263_, v_type_223_, v___x_261_);
v___x_265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13));
v___x_266_ = l_Lean_mkConst(v___x_265_, v___x_239_);
lean_inc_ref(v___x_264_);
v___x_267_ = l_Lean_mkAppB(v___x_266_, v_type_223_, v___x_264_);
v___x_479_ = lean_unbox(v_a_255_);
lean_dec(v_a_255_);
if (v___x_479_ == 0)
{
v___y_432_ = v_a_224_;
v___y_433_ = v_a_225_;
v___y_434_ = v_a_226_;
v___y_435_ = v_a_227_;
v___y_436_ = v_a_228_;
v___y_437_ = v_a_229_;
v___y_438_ = v_a_230_;
v___y_439_ = v_a_231_;
v___y_440_ = v_a_232_;
v___y_441_ = v_a_233_;
goto v___jp_431_;
}
else
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Meta_Grind_updateLastTag(v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec_ref_known(v___x_480_, 1);
v___x_481_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__29, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__29);
lean_inc_ref(v_type_223_);
v___x_482_ = l_Lean_MessageData_ofExpr(v_type_223_);
v___x_483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_253_, v___x_483_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_dec_ref_known(v___x_484_, 1);
v___y_432_ = v_a_224_;
v___y_433_ = v_a_225_;
v___y_434_ = v_a_226_;
v___y_435_ = v_a_227_;
v___y_436_ = v_a_228_;
v___y_437_ = v_a_229_;
v___y_438_ = v_a_230_;
v___y_439_ = v_a_231_;
v___y_440_ = v_a_232_;
v___y_441_ = v_a_233_;
goto v___jp_431_;
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_257_);
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
lean_dec_ref_known(v___x_239_, 2);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_257_);
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
lean_dec_ref_known(v___x_239_, 2);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v_a_493_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_480_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_480_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
v___jp_268_:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v_rings_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___f_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v_rings_277_ = lean_ctor_get(v_a_276_, 0);
lean_inc_ref(v_rings_277_);
lean_dec(v_a_276_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_array_get_size(v_rings_277_);
lean_dec_ref(v_rings_277_);
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15);
v___x_282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17);
v___x_283_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_283_, 0, v___x_279_);
lean_ctor_set(v___x_283_, 1, v_type_223_);
lean_ctor_set(v___x_283_, 2, v_a_236_);
lean_ctor_set(v___x_283_, 3, v___x_261_);
lean_ctor_set(v___x_283_, 4, v___x_264_);
lean_ctor_set(v___x_283_, 5, v___y_270_);
lean_ctor_set(v___x_283_, 6, v___x_278_);
lean_ctor_set(v___x_283_, 7, v___x_278_);
lean_ctor_set(v___x_283_, 8, v___x_278_);
lean_ctor_set(v___x_283_, 9, v___x_278_);
lean_ctor_set(v___x_283_, 10, v___x_278_);
lean_ctor_set(v___x_283_, 11, v___x_278_);
lean_ctor_set(v___x_283_, 12, v___x_278_);
lean_ctor_set(v___x_283_, 13, v___x_278_);
lean_ctor_set(v___x_283_, 14, v___x_281_);
lean_ctor_set(v___x_283_, 15, v___x_282_);
lean_ctor_set(v___x_283_, 16, v___x_282_);
v___x_284_ = lean_box(1);
v___x_285_ = 0;
v___x_286_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18);
v___x_287_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v___x_287_, 0, v___x_283_);
lean_ctor_set(v___x_287_, 1, v___x_278_);
lean_ctor_set(v___x_287_, 2, v___x_278_);
lean_ctor_set(v___x_287_, 3, v___x_267_);
lean_ctor_set(v___x_287_, 4, v_val_248_);
lean_ctor_set(v___x_287_, 5, v___y_271_);
lean_ctor_set(v___x_287_, 6, v___y_269_);
lean_ctor_set(v___x_287_, 7, v___y_272_);
lean_ctor_set(v___x_287_, 8, v___x_281_);
lean_ctor_set(v___x_287_, 9, v___x_280_);
lean_ctor_set(v___x_287_, 10, v___x_280_);
lean_ctor_set(v___x_287_, 11, v___x_284_);
lean_ctor_set(v___x_287_, 12, v___x_238_);
lean_ctor_set(v___x_287_, 13, v___x_281_);
lean_ctor_set(v___x_287_, 14, v___x_286_);
lean_ctor_set(v___x_287_, 15, v___x_280_);
lean_ctor_set(v___x_287_, 16, v___x_278_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*17, v___x_285_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*17 + 1, v___x_285_);
v___f_288_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1), 2, 1);
lean_closure_set(v___f_288_, 0, v___x_287_);
v___x_289_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_290_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_289_, v___f_288_, v___y_273_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_300_; 
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v___x_290_, 0);
lean_dec(v_unused_301_);
v___x_292_ = v___x_290_;
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
else
{
lean_dec(v___x_290_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_279_);
v___x_295_ = v___x_250_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_279_);
v___x_295_ = v_reuseFailAlloc_299_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_295_);
v___x_297_ = v___x_292_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_del_object(v___x_250_);
v_a_302_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_290_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_290_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec(v___y_272_);
lean_dec(v___y_271_);
lean_dec(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v_a_310_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_275_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_275_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
v___jp_318_:
{
lean_object* v___x_336_; 
lean_inc_ref(v___y_334_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 3);
lean_ctor_set(v___x_257_, 0, v___y_334_);
v___x_336_ = v___x_257_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___y_334_);
v___x_336_ = v_reuseFailAlloc_348_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = l_Lean_MessageData_ofFormat(v___x_336_);
lean_inc_ref(v___y_322_);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v___y_322_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_253_, v___x_338_, v___y_332_, v___y_328_, v___y_330_, v___y_331_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_dec_ref_known(v___x_339_, 1);
v___y_269_ = v___y_329_;
v___y_270_ = v___y_320_;
v___y_271_ = v___y_333_;
v___y_272_ = v___y_326_;
v___y_273_ = v___y_321_;
v___y_274_ = v___y_330_;
goto v___jp_268_;
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v___y_333_);
lean_dec(v___y_329_);
lean_dec(v___y_326_);
lean_dec(v___y_320_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
v___jp_349_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__20));
v___x_363_ = l_Lean_mkConst(v___x_362_, v___x_239_);
lean_inc_ref(v_type_223_);
v___x_364_ = l_Lean_Expr_app___override(v___x_363_, v_type_223_);
v___x_365_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_364_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_367_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_365_, 1);
lean_inc_ref(v_type_223_);
lean_inc(v_a_236_);
v___x_367_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(v_a_236_, v_type_223_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_toCold_368_; lean_object* v_options_369_; uint8_t v_hasTrace_370_; 
v_toCold_368_ = lean_ctor_get(v___y_360_, 0);
v_options_369_ = lean_ctor_get(v_toCold_368_, 2);
v_hasTrace_370_ = lean_ctor_get_uint8(v_options_369_, sizeof(void*)*1);
if (v_hasTrace_370_ == 0)
{
lean_object* v_a_371_; 
lean_del_object(v___x_257_);
v_a_371_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_367_, 1);
v___y_269_ = v_a_366_;
v___y_270_ = v___y_350_;
v___y_271_ = v___y_351_;
v___y_272_ = v_a_371_;
v___y_273_ = v___y_352_;
v___y_274_ = v___y_360_;
goto v___jp_268_;
}
else
{
lean_object* v_a_372_; lean_object* v_inheritedTraceOptions_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_a_372_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_367_, 1);
v_inheritedTraceOptions_373_ = lean_ctor_get(v_toCold_368_, 11);
v___x_374_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21);
v___x_375_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_373_, v_options_369_, v___x_374_);
if (v___x_375_ == 0)
{
lean_del_object(v___x_257_);
v___y_269_ = v_a_366_;
v___y_270_ = v___y_350_;
v___y_271_ = v___y_351_;
v___y_272_ = v_a_372_;
v___y_273_ = v___y_352_;
v___y_274_ = v___y_360_;
goto v___jp_268_;
}
else
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Meta_Grind_updateLastTag(v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v___x_377_; 
lean_dec_ref_known(v___x_376_, 1);
v___x_377_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__23);
if (lean_obj_tag(v_a_372_) == 0)
{
lean_object* v___x_378_; 
v___x_378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24));
v___y_319_ = v___y_357_;
v___y_320_ = v___y_350_;
v___y_321_ = v___y_352_;
v___y_322_ = v___x_377_;
v___y_323_ = v___y_353_;
v___y_324_ = v___y_354_;
v___y_325_ = v___y_355_;
v___y_326_ = v_a_372_;
v___y_327_ = v___y_356_;
v___y_328_ = v___y_359_;
v___y_329_ = v_a_366_;
v___y_330_ = v___y_360_;
v___y_331_ = v___y_361_;
v___y_332_ = v___y_358_;
v___y_333_ = v___y_351_;
v___y_334_ = v___x_378_;
goto v___jp_318_;
}
else
{
lean_object* v___x_379_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25));
v___y_319_ = v___y_357_;
v___y_320_ = v___y_350_;
v___y_321_ = v___y_352_;
v___y_322_ = v___x_377_;
v___y_323_ = v___y_353_;
v___y_324_ = v___y_354_;
v___y_325_ = v___y_355_;
v___y_326_ = v_a_372_;
v___y_327_ = v___y_356_;
v___y_328_ = v___y_359_;
v___y_329_ = v_a_366_;
v___y_330_ = v___y_360_;
v___y_331_ = v___y_361_;
v___y_332_ = v___y_358_;
v___y_333_ = v___y_351_;
v___y_334_ = v___x_379_;
goto v___jp_318_;
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec(v_a_372_);
lean_dec(v_a_366_);
lean_dec(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_257_);
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v_a_380_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_376_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_376_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_a_366_);
lean_dec(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_257_);
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v_a_388_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_367_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_367_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_257_);
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v_a_396_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_365_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_365_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
v___jp_404_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
lean_inc_ref(v___y_418_);
v___x_419_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_419_, 0, v___y_418_);
v___x_420_ = l_Lean_MessageData_ofFormat(v___x_419_);
lean_inc_ref(v___y_409_);
v___x_421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_421_, 0, v___y_409_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_253_, v___x_421_, v___y_408_, v___y_413_, v___y_415_, v___y_412_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_dec_ref_known(v___x_422_, 1);
v___y_350_ = v___y_406_;
v___y_351_ = v___y_416_;
v___y_352_ = v___y_407_;
v___y_353_ = v___y_414_;
v___y_354_ = v___y_417_;
v___y_355_ = v___y_410_;
v___y_356_ = v___y_405_;
v___y_357_ = v___y_411_;
v___y_358_ = v___y_408_;
v___y_359_ = v___y_413_;
v___y_360_ = v___y_415_;
v___y_361_ = v___y_412_;
goto v___jp_349_;
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec(v___y_416_);
lean_dec(v___y_406_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_257_);
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
lean_dec_ref_known(v___x_239_, 2);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
v___jp_431_:
{
lean_object* v___x_442_; 
lean_inc_ref(v___x_264_);
lean_inc_ref(v_type_223_);
lean_inc(v_a_236_);
v___x_442_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_a_236_, v_type_223_, v___x_264_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_444_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
lean_inc_ref(v_type_223_);
lean_inc(v_a_236_);
v___x_444_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v_a_236_, v_type_223_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_toCold_445_; lean_object* v_a_446_; lean_object* v_inheritedTraceOptions_447_; lean_object* v___x_448_; lean_object* v_a_449_; uint8_t v___x_450_; 
v_toCold_445_ = lean_ctor_get(v___y_440_, 0);
v_a_446_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_444_, 1);
v_inheritedTraceOptions_447_ = lean_ctor_get(v_toCold_445_, 11);
v___x_448_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0(v___x_253_, v_inheritedTraceOptions_447_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref(v___x_448_);
v___x_450_ = lean_unbox(v_a_449_);
lean_dec(v_a_449_);
if (v___x_450_ == 0)
{
v___y_350_ = v_a_443_;
v___y_351_ = v_a_446_;
v___y_352_ = v___y_432_;
v___y_353_ = v___y_433_;
v___y_354_ = v___y_434_;
v___y_355_ = v___y_435_;
v___y_356_ = v___y_436_;
v___y_357_ = v___y_437_;
v___y_358_ = v___y_438_;
v___y_359_ = v___y_439_;
v___y_360_ = v___y_440_;
v___y_361_ = v___y_441_;
goto v___jp_349_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Meta_Grind_updateLastTag(v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v___x_452_; 
lean_dec_ref_known(v___x_451_, 1);
v___x_452_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27);
if (lean_obj_tag(v_a_446_) == 0)
{
lean_object* v___x_453_; 
v___x_453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24));
v___y_405_ = v___y_436_;
v___y_406_ = v_a_443_;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_438_;
v___y_409_ = v___x_452_;
v___y_410_ = v___y_435_;
v___y_411_ = v___y_437_;
v___y_412_ = v___y_441_;
v___y_413_ = v___y_439_;
v___y_414_ = v___y_433_;
v___y_415_ = v___y_440_;
v___y_416_ = v_a_446_;
v___y_417_ = v___y_434_;
v___y_418_ = v___x_453_;
goto v___jp_404_;
}
else
{
lean_object* v___x_454_; 
v___x_454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25));
v___y_405_ = v___y_436_;
v___y_406_ = v_a_443_;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_438_;
v___y_409_ = v___x_452_;
v___y_410_ = v___y_435_;
v___y_411_ = v___y_437_;
v___y_412_ = v___y_441_;
v___y_413_ = v___y_439_;
v___y_414_ = v___y_433_;
v___y_415_ = v___y_440_;
v___y_416_ = v_a_446_;
v___y_417_ = v___y_434_;
v___y_418_ = v___x_454_;
goto v___jp_404_;
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec(v_a_446_);
lean_dec(v_a_443_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_257_);
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
lean_dec_ref_known(v___x_239_, 2);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v_a_455_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_451_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_451_);
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
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_a_443_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_257_);
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
lean_dec_ref_known(v___x_239_, 2);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v_a_463_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_444_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_444_);
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
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_261_);
lean_del_object(v___x_257_);
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
lean_dec_ref_known(v___x_239_, 2);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v_a_471_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_442_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_442_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_dec(v_a_243_);
lean_dec_ref_known(v___x_239_, 2);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v___x_503_ = lean_box(0);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_503_);
v___x_505_ = v___x_245_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref_known(v___x_239_, 2);
lean_dec(v_a_236_);
lean_dec_ref(v_type_223_);
v_a_508_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_242_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_242_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec_ref(v_type_223_);
v_a_516_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_235_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_235_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___boxed(lean_object* v_type_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec(v_a_525_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1(lean_object* v_cls_537_, lean_object* v_msg_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v_cls_537_, v_msg_538_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___boxed(lean_object* v_cls_551_, lean_object* v_msg_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1(v_cls_551_, v_msg_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec(v___y_553_);
return v_res_564_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = l_Lean_Level_ofNat(v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__48));
v___x_679_ = l_Lean_stringToMessageData(v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f(lean_object* v_type_703_, lean_object* v_base_704_, lean_object* v_semiringInst_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
lean_inc_ref(v_semiringInst_705_);
v___x_717_ = l_Lean_Expr_cleanupAnnotations(v_semiringInst_705_);
v___x_718_ = l_Lean_Expr_isApp(v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_dec_ref(v___x_717_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
v___x_719_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_703_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
return v___x_719_;
}
else
{
lean_object* v_arg_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_arg_720_ = lean_ctor_get(v___x_717_, 1);
lean_inc_ref(v_arg_720_);
v___x_721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_717_);
v___x_722_ = l_Lean_Expr_isApp(v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_dec_ref(v___x_721_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
v___x_723_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_703_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
return v___x_723_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_724_ = l_Lean_Expr_appFnCleanup___redArg(v___x_721_);
v___x_725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1));
v___x_726_ = l_Lean_Expr_isConstOf(v___x_724_, v___x_725_);
lean_dec_ref(v___x_724_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
v___x_727_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_703_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
return v___x_727_;
}
else
{
lean_object* v___x_728_; 
lean_inc_ref(v_base_704_);
v___x_728_ = l_Lean_Meta_getDecLevel_x3f(v_base_704_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_1232_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_1232_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_1232_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
if (lean_obj_tag(v_a_729_) == 1)
{
lean_object* v_val_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_1227_; 
lean_del_object(v___x_731_);
v_val_733_ = lean_ctor_get(v_a_729_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_a_729_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_735_ = v_a_729_;
v_isShared_736_ = v_isSharedCheck_1227_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_val_733_);
lean_dec(v_a_729_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_1227_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__4));
v___x_738_ = lean_box(0);
lean_inc(v_val_733_);
v___x_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_739_, 0, v_val_733_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
lean_inc_ref_n(v___x_739_, 5);
v___x_740_ = l_Lean_mkConst(v___x_737_, v___x_739_);
lean_inc_ref(v_base_704_);
v___x_741_ = l_Lean_mkAppB(v___x_740_, v_base_704_, v_arg_720_);
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__8));
v___x_743_ = l_Lean_mkConst(v___x_742_, v___x_739_);
lean_inc_ref_n(v___x_741_, 2);
lean_inc_ref_n(v_type_703_, 4);
v___x_744_ = l_Lean_mkAppB(v___x_743_, v_type_703_, v___x_741_);
v___x_745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11));
v___x_746_ = l_Lean_mkConst(v___x_745_, v___x_739_);
lean_inc_ref(v___x_744_);
v___x_747_ = l_Lean_mkAppB(v___x_746_, v_type_703_, v___x_744_);
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__13));
v___x_749_ = l_Lean_mkConst(v___x_748_, v___x_739_);
lean_inc_ref(v___x_747_);
v___x_750_ = l_Lean_mkAppB(v___x_749_, v_type_703_, v___x_747_);
v___x_751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__3));
v___x_752_ = l_Lean_mkConst(v___x_751_, v___x_739_);
v___x_753_ = l_Lean_Expr_app___override(v___x_752_, v_type_703_);
v___x_754_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_753_, v___x_741_, v_a_711_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec_ref_known(v___x_754_, 1);
v___x_755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5));
lean_inc_ref(v___x_739_);
v___x_756_ = l_Lean_mkConst(v___x_755_, v___x_739_);
lean_inc_ref(v_type_703_);
v___x_757_ = l_Lean_Expr_app___override(v___x_756_, v_type_703_);
lean_inc_ref(v___x_744_);
v___x_758_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_757_, v___x_744_, v_a_711_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec_ref_known(v___x_758_, 1);
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7));
lean_inc_ref(v___x_739_);
v___x_760_ = l_Lean_mkConst(v___x_759_, v___x_739_);
lean_inc_ref(v_type_703_);
v___x_761_ = l_Lean_Expr_app___override(v___x_760_, v_type_703_);
lean_inc_ref(v___x_747_);
v___x_762_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_761_, v___x_747_, v_a_711_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec_ref_known(v___x_762_, 1);
v___x_763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8));
lean_inc_ref(v___x_739_);
v___x_764_ = l_Lean_mkConst(v___x_763_, v___x_739_);
lean_inc_ref(v_type_703_);
v___x_765_ = l_Lean_Expr_app___override(v___x_764_, v_type_703_);
lean_inc_ref(v___x_750_);
v___x_766_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_765_, v___x_750_, v_a_711_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec_ref_known(v___x_766_, 1);
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__10));
lean_inc_ref_n(v___x_739_, 2);
v___x_768_ = l_Lean_mkConst(v___x_767_, v___x_739_);
lean_inc_ref_n(v_type_703_, 2);
v___x_769_ = l_Lean_Expr_app___override(v___x_768_, v_type_703_);
v___x_770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__12));
v___x_771_ = l_Lean_mkConst(v___x_770_, v___x_739_);
lean_inc_ref(v___x_747_);
v___x_772_ = l_Lean_mkAppB(v___x_771_, v_type_703_, v___x_747_);
v___x_773_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_769_, v___x_772_, v_a_711_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_dec_ref_known(v___x_773_, 1);
v___x_774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__14));
lean_inc_ref_n(v___x_739_, 3);
lean_inc_n(v_val_733_, 2);
v___x_775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_775_, 0, v_val_733_);
lean_ctor_set(v___x_775_, 1, v___x_739_);
v___x_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_776_, 0, v_val_733_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
lean_inc_ref(v___x_776_);
v___x_777_ = l_Lean_mkConst(v___x_774_, v___x_776_);
lean_inc_ref_n(v_type_703_, 5);
v___x_778_ = l_Lean_mkApp3(v___x_777_, v_type_703_, v_type_703_, v_type_703_);
v___x_779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__16));
v___x_780_ = l_Lean_mkConst(v___x_779_, v___x_739_);
v___x_781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__18));
v___x_782_ = l_Lean_mkConst(v___x_781_, v___x_739_);
lean_inc_ref(v___x_747_);
v___x_783_ = l_Lean_mkAppB(v___x_782_, v_type_703_, v___x_747_);
v___x_784_ = l_Lean_mkAppB(v___x_780_, v_type_703_, v___x_783_);
v___x_785_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_778_, v___x_784_, v_a_711_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec_ref_known(v___x_785_, 1);
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__20));
lean_inc_ref(v___x_776_);
v___x_787_ = l_Lean_mkConst(v___x_786_, v___x_776_);
lean_inc_ref_n(v_type_703_, 5);
v___x_788_ = l_Lean_mkApp3(v___x_787_, v_type_703_, v_type_703_, v_type_703_);
v___x_789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__22));
lean_inc_ref_n(v___x_739_, 2);
v___x_790_ = l_Lean_mkConst(v___x_789_, v___x_739_);
v___x_791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__24));
v___x_792_ = l_Lean_mkConst(v___x_791_, v___x_739_);
lean_inc_ref(v___x_747_);
v___x_793_ = l_Lean_mkAppB(v___x_792_, v_type_703_, v___x_747_);
v___x_794_ = l_Lean_mkAppB(v___x_790_, v_type_703_, v___x_793_);
v___x_795_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_788_, v___x_794_, v_a_711_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec_ref_known(v___x_795_, 1);
v___x_796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__26));
v___x_797_ = l_Lean_mkConst(v___x_796_, v___x_776_);
lean_inc_ref_n(v_type_703_, 5);
v___x_798_ = l_Lean_mkApp3(v___x_797_, v_type_703_, v_type_703_, v_type_703_);
v___x_799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__28));
lean_inc_ref_n(v___x_739_, 2);
v___x_800_ = l_Lean_mkConst(v___x_799_, v___x_739_);
v___x_801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__30));
v___x_802_ = l_Lean_mkConst(v___x_801_, v___x_739_);
lean_inc_ref(v___x_744_);
v___x_803_ = l_Lean_mkAppB(v___x_802_, v_type_703_, v___x_744_);
v___x_804_ = l_Lean_mkAppB(v___x_800_, v_type_703_, v___x_803_);
v___x_805_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_798_, v___x_804_, v_a_711_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec_ref_known(v___x_805_, 1);
v___x_806_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__32));
lean_inc_ref_n(v___x_739_, 2);
v___x_807_ = l_Lean_mkConst(v___x_806_, v___x_739_);
lean_inc_ref_n(v_type_703_, 2);
v___x_808_ = l_Lean_Expr_app___override(v___x_807_, v_type_703_);
v___x_809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__34));
v___x_810_ = l_Lean_mkConst(v___x_809_, v___x_739_);
lean_inc_ref(v___x_744_);
v___x_811_ = l_Lean_mkAppB(v___x_810_, v_type_703_, v___x_744_);
v___x_812_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_808_, v___x_811_, v_a_711_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec_ref_known(v___x_812_, 1);
v___x_813_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__36));
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__37);
lean_inc_ref_n(v___x_739_, 2);
v___x_863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v___x_739_);
lean_inc(v_val_733_);
v___x_864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_864_, 0, v_val_733_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Lean_mkConst(v___x_813_, v___x_864_);
v___x_866_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_703_, 3);
v___x_867_ = l_Lean_mkApp3(v___x_865_, v_type_703_, v___x_866_, v_type_703_);
v___x_868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__39));
v___x_869_ = l_Lean_mkConst(v___x_868_, v___x_739_);
lean_inc_ref(v___x_747_);
v___x_870_ = l_Lean_mkAppB(v___x_869_, v_type_703_, v___x_747_);
v___x_871_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_867_, v___x_870_, v_a_711_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec_ref_known(v___x_871_, 1);
v___x_872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__41));
lean_inc_ref_n(v___x_739_, 2);
v___x_873_ = l_Lean_mkConst(v___x_872_, v___x_739_);
lean_inc_ref_n(v_type_703_, 2);
v___x_874_ = l_Lean_Expr_app___override(v___x_873_, v_type_703_);
v___x_875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__43));
v___x_876_ = l_Lean_mkConst(v___x_875_, v___x_739_);
lean_inc_ref(v___x_747_);
v___x_877_ = l_Lean_mkAppB(v___x_876_, v_type_703_, v___x_747_);
v___x_878_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_874_, v___x_877_, v_a_711_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec_ref_known(v___x_878_, 1);
v___x_879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__45));
lean_inc_ref_n(v___x_739_, 2);
v___x_880_ = l_Lean_mkConst(v___x_879_, v___x_739_);
lean_inc_ref_n(v_type_703_, 2);
v___x_881_ = l_Lean_Expr_app___override(v___x_880_, v_type_703_);
v___x_882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__47));
v___x_883_ = l_Lean_mkConst(v___x_882_, v___x_739_);
lean_inc_ref(v___x_744_);
v___x_884_ = l_Lean_mkAppB(v___x_883_, v_type_703_, v___x_744_);
v___x_885_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_881_, v___x_884_, v_a_711_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_toCold_886_; lean_object* v_inheritedTraceOptions_887_; lean_object* v___x_888_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v_options_901_; lean_object* v_inheritedTraceOptions_902_; lean_object* v___y_903_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_957_; lean_object* v_noZeroDivInst_x3f_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v_val_988_; lean_object* v_charInst_x3f_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___x_1107_; lean_object* v_a_1108_; uint8_t v___x_1109_; 
lean_dec_ref_known(v___x_885_, 1);
v_toCold_886_ = lean_ctor_get(v_a_714_, 0);
v_inheritedTraceOptions_887_ = lean_ctor_get(v_toCold_886_, 11);
v___x_888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6));
v___x_1107_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0(v___x_888_, v_inheritedTraceOptions_887_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref(v___x_1107_);
v___x_1109_ = lean_unbox(v_a_1108_);
lean_dec(v_a_1108_);
if (v___x_1109_ == 0)
{
v___y_1035_ = v_a_706_;
v___y_1036_ = v_a_707_;
v___y_1037_ = v_a_708_;
v___y_1038_ = v_a_709_;
v___y_1039_ = v_a_710_;
v___y_1040_ = v_a_711_;
v___y_1041_ = v_a_712_;
v___y_1042_ = v_a_713_;
v___y_1043_ = v_a_714_;
v___y_1044_ = v_a_715_;
goto v___jp_1034_;
}
else
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Meta_Grind_updateLastTag(v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec_ref_known(v___x_1110_, 1);
v___x_1111_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__29, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__29);
lean_inc_ref(v_type_703_);
v___x_1112_ = l_Lean_MessageData_ofExpr(v_type_703_);
v___x_1113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_888_, v___x_1113_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_dec_ref_known(v___x_1114_, 1);
v___y_1035_ = v_a_706_;
v___y_1036_ = v_a_707_;
v___y_1037_ = v_a_708_;
v___y_1038_ = v_a_709_;
v___y_1039_ = v_a_710_;
v___y_1040_ = v_a_711_;
v___y_1041_ = v_a_712_;
v___y_1042_ = v_a_713_;
v___y_1043_ = v_a_714_;
v___y_1044_ = v_a_715_;
goto v___jp_1034_;
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1123_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1110_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1110_);
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
v___jp_889_:
{
uint8_t v_hasTrace_904_; 
v_hasTrace_904_ = lean_ctor_get_uint8(v_options_901_, sizeof(void*)*1);
if (v_hasTrace_904_ == 0)
{
v___y_816_ = v___y_891_;
v___y_817_ = v___y_890_;
v___y_818_ = v___y_892_;
v___y_819_ = v___y_900_;
goto v___jp_815_;
}
else
{
lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21);
v___x_906_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_902_, v_options_901_, v___x_905_);
if (v___x_906_ == 0)
{
v___y_816_ = v___y_891_;
v___y_817_ = v___y_890_;
v___y_818_ = v___y_892_;
v___y_819_ = v___y_900_;
goto v___jp_815_;
}
else
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Meta_Grind_updateLastTag(v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_903_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec_ref_known(v___x_907_, 1);
v___x_908_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__49);
v___x_909_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_888_, v___x_908_, v___y_898_, v___y_899_, v___y_900_, v___y_903_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_dec_ref_known(v___x_909_, 1);
v___y_816_ = v___y_891_;
v___y_817_ = v___y_890_;
v___y_818_ = v___y_892_;
v___y_819_ = v___y_900_;
goto v___jp_815_;
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_type_703_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_type_703_);
v_a_918_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_907_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_907_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
v___jp_926_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_inc_ref(v___y_940_);
v___x_941_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_941_, 0, v___y_940_);
v___x_942_ = l_Lean_MessageData_ofFormat(v___x_941_);
lean_inc_ref(v___y_931_);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___y_931_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_888_, v___x_943_, v___y_935_, v___y_932_, v___y_933_, v___y_930_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_toCold_945_; lean_object* v_options_946_; lean_object* v_inheritedTraceOptions_947_; 
lean_dec_ref_known(v___x_944_, 1);
v_toCold_945_ = lean_ctor_get(v___y_933_, 0);
v_options_946_ = lean_ctor_get(v_toCold_945_, 2);
v_inheritedTraceOptions_947_ = lean_ctor_get(v_toCold_945_, 11);
v___y_890_ = v___y_939_;
v___y_891_ = v___y_938_;
v___y_892_ = v___y_927_;
v___y_893_ = v___y_929_;
v___y_894_ = v___y_934_;
v___y_895_ = v___y_928_;
v___y_896_ = v___y_937_;
v___y_897_ = v___y_936_;
v___y_898_ = v___y_935_;
v___y_899_ = v___y_932_;
v___y_900_ = v___y_933_;
v_options_901_ = v_options_946_;
v_inheritedTraceOptions_902_ = v_inheritedTraceOptions_947_;
v___y_903_ = v___y_930_;
goto v___jp_889_;
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_type_703_);
v_a_948_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_944_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_944_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
v___jp_956_:
{
lean_object* v_toCold_969_; lean_object* v_options_970_; lean_object* v_inheritedTraceOptions_971_; lean_object* v___x_972_; lean_object* v_a_973_; uint8_t v___x_974_; 
v_toCold_969_ = lean_ctor_get(v___y_967_, 0);
v_options_970_ = lean_ctor_get(v_toCold_969_, 2);
v_inheritedTraceOptions_971_ = lean_ctor_get(v_toCold_969_, 11);
v___x_972_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__0(v___x_888_, v_inheritedTraceOptions_971_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref(v___x_972_);
v___x_974_ = lean_unbox(v_a_973_);
lean_dec(v_a_973_);
if (v___x_974_ == 0)
{
v___y_890_ = v___y_957_;
v___y_891_ = v_noZeroDivInst_x3f_958_;
v___y_892_ = v___y_959_;
v___y_893_ = v___y_960_;
v___y_894_ = v___y_961_;
v___y_895_ = v___y_962_;
v___y_896_ = v___y_963_;
v___y_897_ = v___y_964_;
v___y_898_ = v___y_965_;
v___y_899_ = v___y_966_;
v___y_900_ = v___y_967_;
v_options_901_ = v_options_970_;
v_inheritedTraceOptions_902_ = v_inheritedTraceOptions_971_;
v___y_903_ = v___y_968_;
goto v___jp_889_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_Meta_Grind_updateLastTag(v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v___x_976_; 
lean_dec_ref_known(v___x_975_, 1);
v___x_976_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__27);
if (lean_obj_tag(v_noZeroDivInst_x3f_958_) == 0)
{
lean_object* v___x_977_; 
v___x_977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__24));
v___y_927_ = v___y_959_;
v___y_928_ = v___y_962_;
v___y_929_ = v___y_960_;
v___y_930_ = v___y_968_;
v___y_931_ = v___x_976_;
v___y_932_ = v___y_966_;
v___y_933_ = v___y_967_;
v___y_934_ = v___y_961_;
v___y_935_ = v___y_965_;
v___y_936_ = v___y_964_;
v___y_937_ = v___y_963_;
v___y_938_ = v_noZeroDivInst_x3f_958_;
v___y_939_ = v___y_957_;
v___y_940_ = v___x_977_;
goto v___jp_926_;
}
else
{
lean_object* v___x_978_; 
v___x_978_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__25));
v___y_927_ = v___y_959_;
v___y_928_ = v___y_962_;
v___y_929_ = v___y_960_;
v___y_930_ = v___y_968_;
v___y_931_ = v___x_976_;
v___y_932_ = v___y_966_;
v___y_933_ = v___y_967_;
v___y_934_ = v___y_961_;
v___y_935_ = v___y_965_;
v___y_936_ = v___y_964_;
v___y_937_ = v___y_963_;
v___y_938_ = v_noZeroDivInst_x3f_958_;
v___y_939_ = v___y_957_;
v___y_940_ = v___x_978_;
goto v___jp_926_;
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec(v_noZeroDivInst_x3f_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_type_703_);
v_a_979_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_975_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_975_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
v___jp_987_:
{
lean_object* v___x_1000_; 
lean_inc_ref(v_base_704_);
lean_inc(v_val_733_);
v___x_1000_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(v_val_733_, v_base_704_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
if (lean_obj_tag(v_a_1001_) == 1)
{
lean_object* v_val_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1012_; 
v_val_1002_ = lean_ctor_get(v_a_1001_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_a_1001_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1004_ = v_a_1001_;
v_isShared_1005_ = v_isSharedCheck_1012_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_val_1002_);
lean_dec(v_a_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1012_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__52));
v___x_1007_ = l_Lean_mkConst(v___x_1006_, v___x_739_);
v___x_1008_ = l_Lean_mkApp4(v___x_1007_, v_base_704_, v_semiringInst_705_, v_val_988_, v_val_1002_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1008_);
v___x_1010_ = v___x_1004_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
v___y_957_ = v_charInst_x3f_989_;
v_noZeroDivInst_x3f_958_ = v___x_1010_;
v___y_959_ = v___y_990_;
v___y_960_ = v___y_991_;
v___y_961_ = v___y_992_;
v___y_962_ = v___y_993_;
v___y_963_ = v___y_994_;
v___y_964_ = v___y_995_;
v___y_965_ = v___y_996_;
v___y_966_ = v___y_997_;
v___y_967_ = v___y_998_;
v___y_968_ = v___y_999_;
goto v___jp_956_;
}
}
}
else
{
lean_object* v___x_1013_; 
lean_dec(v_a_1001_);
lean_dec_ref(v_val_988_);
lean_dec_ref_known(v___x_739_, 2);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
v___x_1013_ = lean_box(0);
v___y_957_ = v_charInst_x3f_989_;
v_noZeroDivInst_x3f_958_ = v___x_1013_;
v___y_959_ = v___y_990_;
v___y_960_ = v___y_991_;
v___y_961_ = v___y_992_;
v___y_962_ = v___y_993_;
v___y_963_ = v___y_994_;
v___y_964_ = v___y_995_;
v___y_965_ = v___y_996_;
v___y_966_ = v___y_997_;
v___y_967_ = v___y_998_;
v___y_968_ = v___y_999_;
goto v___jp_956_;
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_charInst_x3f_989_);
lean_dec_ref(v_val_988_);
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1014_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1000_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1000_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
v___jp_1022_:
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_box(0);
v___y_957_ = v___x_1033_;
v_noZeroDivInst_x3f_958_ = v___x_1033_;
v___y_959_ = v___y_1023_;
v___y_960_ = v___y_1024_;
v___y_961_ = v___y_1025_;
v___y_962_ = v___y_1026_;
v___y_963_ = v___y_1027_;
v___y_964_ = v___y_1028_;
v___y_965_ = v___y_1029_;
v___y_966_ = v___y_1030_;
v___y_967_ = v___y_1031_;
v___y_968_ = v___y_1032_;
goto v___jp_956_;
}
v___jp_1034_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1045_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__54));
lean_inc_ref(v___x_739_);
v___x_1046_ = l_Lean_mkConst(v___x_1045_, v___x_739_);
lean_inc_ref(v_base_704_);
v___x_1047_ = l_Lean_Expr_app___override(v___x_1046_, v_base_704_);
v___x_1048_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1047_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
if (lean_obj_tag(v_a_1049_) == 1)
{
lean_object* v_val_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_val_1050_ = lean_ctor_get(v_a_1049_, 0);
lean_inc(v_val_1050_);
lean_dec_ref_known(v_a_1049_, 1);
v___x_1051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__56));
lean_inc_ref(v___x_739_);
v___x_1052_ = l_Lean_mkConst(v___x_1051_, v___x_739_);
lean_inc_ref(v_base_704_);
v___x_1053_ = l_Lean_mkAppB(v___x_1052_, v_base_704_, v_val_1050_);
v___x_1054_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1053_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
if (lean_obj_tag(v_a_1055_) == 1)
{
lean_object* v_val_1056_; lean_object* v___x_1057_; 
v_val_1056_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_val_1056_);
lean_dec_ref_known(v_a_1055_, 1);
lean_inc_ref(v_semiringInst_705_);
lean_inc_ref(v_base_704_);
lean_inc(v_val_733_);
v___x_1057_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_val_733_, v_base_704_, v_semiringInst_705_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v___x_1057_, 1);
if (lean_obj_tag(v_a_1058_) == 1)
{
lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1079_; 
v_val_1059_ = lean_ctor_get(v_a_1058_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_a_1058_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1061_ = v_a_1058_;
v_isShared_1062_ = v_isSharedCheck_1079_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v_a_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1079_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1078_; 
v_fst_1063_ = lean_ctor_get(v_val_1059_, 0);
v_snd_1064_ = lean_ctor_get(v_val_1059_, 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_val_1059_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1066_ = v_val_1059_;
v_isShared_1067_ = v_isSharedCheck_1078_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_snd_1064_);
lean_inc(v_fst_1063_);
lean_dec(v_val_1059_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1078_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__58));
lean_inc_ref(v___x_739_);
v___x_1069_ = l_Lean_mkConst(v___x_1068_, v___x_739_);
lean_inc(v_snd_1064_);
v___x_1070_ = l_Lean_mkRawNatLit(v_snd_1064_);
lean_inc(v_val_1056_);
lean_inc_ref(v_semiringInst_705_);
lean_inc_ref(v_base_704_);
v___x_1071_ = l_Lean_mkApp5(v___x_1069_, v_base_704_, v___x_1070_, v_semiringInst_705_, v_val_1056_, v_fst_1063_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1071_);
v___x_1073_ = v___x_1066_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_snd_1064_);
v___x_1073_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1073_);
v___x_1075_ = v___x_1061_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
v_val_988_ = v_val_1056_;
v_charInst_x3f_989_ = v___x_1075_;
v___y_990_ = v___y_1035_;
v___y_991_ = v___y_1036_;
v___y_992_ = v___y_1037_;
v___y_993_ = v___y_1038_;
v___y_994_ = v___y_1039_;
v___y_995_ = v___y_1040_;
v___y_996_ = v___y_1041_;
v___y_997_ = v___y_1042_;
v___y_998_ = v___y_1043_;
v___y_999_ = v___y_1044_;
goto v___jp_987_;
}
}
}
}
}
else
{
lean_object* v___x_1080_; 
lean_dec(v_a_1058_);
v___x_1080_ = lean_box(0);
v_val_988_ = v_val_1056_;
v_charInst_x3f_989_ = v___x_1080_;
v___y_990_ = v___y_1035_;
v___y_991_ = v___y_1036_;
v___y_992_ = v___y_1037_;
v___y_993_ = v___y_1038_;
v___y_994_ = v___y_1039_;
v___y_995_ = v___y_1040_;
v___y_996_ = v___y_1041_;
v___y_997_ = v___y_1042_;
v___y_998_ = v___y_1043_;
v___y_999_ = v___y_1044_;
goto v___jp_987_;
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_val_1056_);
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1081_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1057_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1057_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
if (lean_obj_tag(v_a_1055_) == 1)
{
lean_object* v_val_1089_; lean_object* v___x_1090_; 
v_val_1089_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_val_1089_);
lean_dec_ref_known(v_a_1055_, 1);
v___x_1090_ = lean_box(0);
v_val_988_ = v_val_1089_;
v_charInst_x3f_989_ = v___x_1090_;
v___y_990_ = v___y_1035_;
v___y_991_ = v___y_1036_;
v___y_992_ = v___y_1037_;
v___y_993_ = v___y_1038_;
v___y_994_ = v___y_1039_;
v___y_995_ = v___y_1040_;
v___y_996_ = v___y_1041_;
v___y_997_ = v___y_1042_;
v___y_998_ = v___y_1043_;
v___y_999_ = v___y_1044_;
goto v___jp_987_;
}
else
{
lean_dec(v_a_1055_);
lean_dec_ref_known(v___x_739_, 2);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
v___y_1023_ = v___y_1035_;
v___y_1024_ = v___y_1036_;
v___y_1025_ = v___y_1037_;
v___y_1026_ = v___y_1038_;
v___y_1027_ = v___y_1039_;
v___y_1028_ = v___y_1040_;
v___y_1029_ = v___y_1041_;
v___y_1030_ = v___y_1042_;
v___y_1031_ = v___y_1043_;
v___y_1032_ = v___y_1044_;
goto v___jp_1022_;
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1091_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1054_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1054_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_dec(v_a_1049_);
lean_dec_ref_known(v___x_739_, 2);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
v___y_1023_ = v___y_1035_;
v___y_1024_ = v___y_1036_;
v___y_1025_ = v___y_1037_;
v___y_1026_ = v___y_1038_;
v___y_1027_ = v___y_1039_;
v___y_1028_ = v___y_1040_;
v___y_1029_ = v___y_1041_;
v___y_1030_ = v___y_1042_;
v___y_1031_ = v___y_1043_;
v___y_1032_ = v___y_1044_;
goto v___jp_1022_;
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1099_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1048_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1048_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1131_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_885_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_885_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1139_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_878_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_878_);
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
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1147_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_871_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_871_);
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
v___jp_815_:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_818_, v___y_819_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v_rings_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___f_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_820_, 1);
v_rings_822_ = lean_ctor_get(v_a_821_, 0);
lean_inc_ref(v_rings_822_);
lean_dec(v_a_821_);
v___x_823_ = lean_array_get_size(v_rings_822_);
lean_dec_ref(v_rings_822_);
v___x_824_ = lean_box(0);
v___x_825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15);
v___x_826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17);
v___x_827_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_827_, 0, v___x_823_);
lean_ctor_set(v___x_827_, 1, v_type_703_);
lean_ctor_set(v___x_827_, 2, v_val_733_);
lean_ctor_set(v___x_827_, 3, v___x_744_);
lean_ctor_set(v___x_827_, 4, v___x_747_);
lean_ctor_set(v___x_827_, 5, v___y_817_);
lean_ctor_set(v___x_827_, 6, v___x_824_);
lean_ctor_set(v___x_827_, 7, v___x_824_);
lean_ctor_set(v___x_827_, 8, v___x_824_);
lean_ctor_set(v___x_827_, 9, v___x_824_);
lean_ctor_set(v___x_827_, 10, v___x_824_);
lean_ctor_set(v___x_827_, 11, v___x_824_);
lean_ctor_set(v___x_827_, 12, v___x_824_);
lean_ctor_set(v___x_827_, 13, v___x_824_);
lean_ctor_set(v___x_827_, 14, v___x_825_);
lean_ctor_set(v___x_827_, 15, v___x_826_);
lean_ctor_set(v___x_827_, 16, v___x_826_);
v___x_828_ = lean_box(1);
v___x_829_ = 0;
v___x_830_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__18);
v___x_831_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v___x_831_, 0, v___x_827_);
lean_ctor_set(v___x_831_, 1, v___x_824_);
lean_ctor_set(v___x_831_, 2, v___x_824_);
lean_ctor_set(v___x_831_, 3, v___x_750_);
lean_ctor_set(v___x_831_, 4, v___x_741_);
lean_ctor_set(v___x_831_, 5, v___y_816_);
lean_ctor_set(v___x_831_, 6, v___x_824_);
lean_ctor_set(v___x_831_, 7, v___x_824_);
lean_ctor_set(v___x_831_, 8, v___x_825_);
lean_ctor_set(v___x_831_, 9, v___x_814_);
lean_ctor_set(v___x_831_, 10, v___x_814_);
lean_ctor_set(v___x_831_, 11, v___x_828_);
lean_ctor_set(v___x_831_, 12, v___x_738_);
lean_ctor_set(v___x_831_, 13, v___x_825_);
lean_ctor_set(v___x_831_, 14, v___x_830_);
lean_ctor_set(v___x_831_, 15, v___x_814_);
lean_ctor_set(v___x_831_, 16, v___x_824_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*17, v___x_829_);
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*17 + 1, v___x_829_);
v___f_832_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___lam__1), 2, 1);
lean_closure_set(v___f_832_, 0, v___x_831_);
v___x_833_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_834_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_833_, v___f_832_, v___y_818_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_844_; 
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v___x_834_, 0);
lean_dec(v_unused_845_);
v___x_836_ = v___x_834_;
v_isShared_837_ = v_isSharedCheck_844_;
goto v_resetjp_835_;
}
else
{
lean_dec(v___x_834_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_844_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_823_);
v___x_839_ = v___x_735_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_823_);
v___x_839_ = v_reuseFailAlloc_843_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_841_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_839_);
v___x_841_ = v___x_836_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_del_object(v___x_735_);
v_a_846_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_834_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_834_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_type_703_);
v_a_854_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_820_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_820_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1155_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_812_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_812_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1163_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_805_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_805_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref_known(v___x_776_, 2);
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1171_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_795_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_795_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref_known(v___x_776_, 2);
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1179_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_785_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_785_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1187_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_773_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_773_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1195_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_766_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_766_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1203_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_762_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_762_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1211_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_758_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_758_);
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
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_741_);
lean_dec_ref_known(v___x_739_, 2);
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1219_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_754_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_754_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
lean_dec(v_a_729_);
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v___x_1228_ = lean_box(0);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_1228_);
v___x_1230_ = v___x_731_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec_ref(v_arg_720_);
lean_dec_ref(v_semiringInst_705_);
lean_dec_ref(v_base_704_);
lean_dec_ref(v_type_703_);
v_a_1233_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_728_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_728_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___boxed(lean_object* v_type_1241_, lean_object* v_base_1242_, lean_object* v_semiringInst_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f(v_type_1241_, v_base_1242_, v_semiringInst_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec(v_a_1244_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(lean_object* v_type_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1));
v___x_1276_ = lean_unsigned_to_nat(2u);
v___x_1277_ = l_Lean_Expr_isAppOfArity(v_type_1263_, v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; 
v___x_1278_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f(v_type_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
return v___x_1278_;
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1279_ = l_Lean_Expr_appFn_x21(v_type_1263_);
v___x_1280_ = l_Lean_Expr_appArg_x21(v___x_1279_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = l_Lean_Expr_appArg_x21(v_type_1263_);
v___x_1282_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f(v_type_1263_, v___x_1280_, v___x_1281_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___boxed(lean_object* v_type_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec(v_a_1284_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v_ks_1300_; lean_object* v_vs_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1327_; 
v_ks_1300_ = lean_ctor_get(v_x_1296_, 0);
v_vs_1301_ = lean_ctor_get(v_x_1296_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_x_1296_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1303_ = v_x_1296_;
v_isShared_1304_ = v_isSharedCheck_1327_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_vs_1301_);
lean_inc(v_ks_1300_);
lean_dec(v_x_1296_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1327_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = lean_array_get_size(v_ks_1300_);
v___x_1306_ = lean_nat_dec_lt(v_x_1297_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_dec(v_x_1297_);
v___x_1307_ = lean_array_push(v_ks_1300_, v_x_1298_);
v___x_1308_ = lean_array_push(v_vs_1301_, v_x_1299_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 1, v___x_1308_);
lean_ctor_set(v___x_1303_, 0, v___x_1307_);
v___x_1310_ = v___x_1303_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
else
{
lean_object* v_k_x27_1312_; size_t v___x_1313_; size_t v___x_1314_; uint8_t v___x_1315_; 
v_k_x27_1312_ = lean_array_fget_borrowed(v_ks_1300_, v_x_1297_);
v___x_1313_ = lean_ptr_addr(v_x_1298_);
v___x_1314_ = lean_ptr_addr(v_k_x27_1312_);
v___x_1315_ = lean_usize_dec_eq(v___x_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1317_; 
if (v_isShared_1304_ == 0)
{
v___x_1317_ = v___x_1303_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_ks_1300_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_vs_1301_);
v___x_1317_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_unsigned_to_nat(1u);
v___x_1319_ = lean_nat_add(v_x_1297_, v___x_1318_);
lean_dec(v_x_1297_);
v_x_1296_ = v___x_1317_;
v_x_1297_ = v___x_1319_;
goto _start;
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1322_ = lean_array_fset(v_ks_1300_, v_x_1297_, v_x_1298_);
v___x_1323_ = lean_array_fset(v_vs_1301_, v_x_1297_, v_x_1299_);
lean_dec(v_x_1297_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 1, v___x_1323_);
lean_ctor_set(v___x_1303_, 0, v___x_1322_);
v___x_1325_ = v___x_1303_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1323_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1328_, lean_object* v_k_1329_, lean_object* v_v_1330_){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1328_, v___x_1331_, v_k_1329_, v_v_1330_);
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(lean_object* v_x_1334_, size_t v_x_1335_, size_t v_x_1336_, lean_object* v_x_1337_, lean_object* v_x_1338_){
_start:
{
if (lean_obj_tag(v_x_1334_) == 0)
{
lean_object* v_es_1339_; size_t v___x_1340_; size_t v___x_1341_; lean_object* v_j_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_es_1339_ = lean_ctor_get(v_x_1334_, 0);
v___x_1340_ = ((size_t)31ULL);
v___x_1341_ = lean_usize_land(v_x_1335_, v___x_1340_);
v_j_1342_ = lean_usize_to_nat(v___x_1341_);
v___x_1343_ = lean_array_get_size(v_es_1339_);
v___x_1344_ = lean_nat_dec_lt(v_j_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_dec(v_j_1342_);
lean_dec(v_x_1338_);
lean_dec_ref(v_x_1337_);
return v_x_1334_;
}
else
{
lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1385_; 
lean_inc_ref(v_es_1339_);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_x_1334_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; 
v_unused_1386_ = lean_ctor_get(v_x_1334_, 0);
lean_dec(v_unused_1386_);
v___x_1346_ = v_x_1334_;
v_isShared_1347_ = v_isSharedCheck_1385_;
goto v_resetjp_1345_;
}
else
{
lean_dec(v_x_1334_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1385_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_v_1348_; lean_object* v___x_1349_; lean_object* v_xs_x27_1350_; lean_object* v___y_1352_; 
v_v_1348_ = lean_array_fget(v_es_1339_, v_j_1342_);
v___x_1349_ = lean_box(0);
v_xs_x27_1350_ = lean_array_fset(v_es_1339_, v_j_1342_, v___x_1349_);
switch(lean_obj_tag(v_v_1348_))
{
case 0:
{
lean_object* v_key_1357_; lean_object* v_val_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1370_; 
v_key_1357_ = lean_ctor_get(v_v_1348_, 0);
v_val_1358_ = lean_ctor_get(v_v_1348_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_v_1348_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1360_ = v_v_1348_;
v_isShared_1361_ = v_isSharedCheck_1370_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_val_1358_);
lean_inc(v_key_1357_);
lean_dec(v_v_1348_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1370_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
size_t v___x_1362_; size_t v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = lean_ptr_addr(v_x_1337_);
v___x_1363_ = lean_ptr_addr(v_key_1357_);
v___x_1364_ = lean_usize_dec_eq(v___x_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_del_object(v___x_1360_);
v___x_1365_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1357_, v_val_1358_, v_x_1337_, v_x_1338_);
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
v___y_1352_ = v___x_1366_;
goto v___jp_1351_;
}
else
{
lean_object* v___x_1368_; 
lean_dec(v_val_1358_);
lean_dec(v_key_1357_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v_x_1338_);
lean_ctor_set(v___x_1360_, 0, v_x_1337_);
v___x_1368_ = v___x_1360_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_x_1337_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_x_1338_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
v___y_1352_ = v___x_1368_;
goto v___jp_1351_;
}
}
}
}
case 1:
{
lean_object* v_node_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1383_; 
v_node_1371_ = lean_ctor_get(v_v_1348_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_v_1348_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1373_ = v_v_1348_;
v_isShared_1374_ = v_isSharedCheck_1383_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_node_1371_);
lean_dec(v_v_1348_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1383_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
size_t v___x_1375_; size_t v___x_1376_; size_t v___x_1377_; size_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1375_ = ((size_t)5ULL);
v___x_1376_ = lean_usize_shift_right(v_x_1335_, v___x_1375_);
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_add(v_x_1336_, v___x_1377_);
v___x_1379_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_node_1371_, v___x_1376_, v___x_1378_, v_x_1337_, v_x_1338_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1379_);
v___x_1381_ = v___x_1373_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
v___y_1352_ = v___x_1381_;
goto v___jp_1351_;
}
}
}
default: 
{
lean_object* v___x_1384_; 
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_x_1337_);
lean_ctor_set(v___x_1384_, 1, v_x_1338_);
v___y_1352_ = v___x_1384_;
goto v___jp_1351_;
}
}
v___jp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1353_ = lean_array_fset(v_xs_x27_1350_, v_j_1342_, v___y_1352_);
lean_dec(v_j_1342_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1353_);
v___x_1355_ = v___x_1346_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
else
{
lean_object* v_ks_1387_; lean_object* v_vs_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1406_; 
v_ks_1387_ = lean_ctor_get(v_x_1334_, 0);
v_vs_1388_ = lean_ctor_get(v_x_1334_, 1);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_x_1334_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1390_ = v_x_1334_;
v_isShared_1391_ = v_isSharedCheck_1406_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_vs_1388_);
lean_inc(v_ks_1387_);
lean_dec(v_x_1334_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1406_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_ks_1387_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_vs_1388_);
v___x_1393_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v_newNode_1394_; size_t v___x_1395_; uint8_t v___x_1396_; 
v_newNode_1394_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v___x_1393_, v_x_1337_, v_x_1338_);
v___x_1395_ = ((size_t)7ULL);
v___x_1396_ = lean_usize_dec_le(v___x_1395_, v_x_1336_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1397_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1394_);
v___x_1398_ = lean_unsigned_to_nat(4u);
v___x_1399_ = lean_nat_dec_lt(v___x_1397_, v___x_1398_);
lean_dec(v___x_1397_);
if (v___x_1399_ == 0)
{
lean_object* v_ks_1400_; lean_object* v_vs_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_ks_1400_ = lean_ctor_get(v_newNode_1394_, 0);
lean_inc_ref(v_ks_1400_);
v_vs_1401_ = lean_ctor_get(v_newNode_1394_, 1);
lean_inc_ref(v_vs_1401_);
lean_dec_ref(v_newNode_1394_);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___closed__0);
v___x_1404_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_x_1336_, v_ks_1400_, v_vs_1401_, v___x_1402_, v___x_1403_);
lean_dec_ref(v_vs_1401_);
lean_dec_ref(v_ks_1400_);
return v___x_1404_;
}
else
{
return v_newNode_1394_;
}
}
else
{
return v_newNode_1394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_1407_, lean_object* v_keys_1408_, lean_object* v_vals_1409_, lean_object* v_i_1410_, lean_object* v_entries_1411_){
_start:
{
lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1412_ = lean_array_get_size(v_keys_1408_);
v___x_1413_ = lean_nat_dec_lt(v_i_1410_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_dec(v_i_1410_);
return v_entries_1411_;
}
else
{
lean_object* v_k_1414_; lean_object* v_v_1415_; size_t v___x_1416_; size_t v___x_1417_; size_t v___x_1418_; uint64_t v___x_1419_; size_t v_h_1420_; size_t v___x_1421_; lean_object* v___x_1422_; size_t v___x_1423_; size_t v___x_1424_; size_t v___x_1425_; size_t v_h_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_k_1414_ = lean_array_fget_borrowed(v_keys_1408_, v_i_1410_);
v_v_1415_ = lean_array_fget_borrowed(v_vals_1409_, v_i_1410_);
v___x_1416_ = lean_ptr_addr(v_k_1414_);
v___x_1417_ = ((size_t)3ULL);
v___x_1418_ = lean_usize_shift_right(v___x_1416_, v___x_1417_);
v___x_1419_ = lean_usize_to_uint64(v___x_1418_);
v_h_1420_ = lean_uint64_to_usize(v___x_1419_);
v___x_1421_ = ((size_t)5ULL);
v___x_1422_ = lean_unsigned_to_nat(1u);
v___x_1423_ = ((size_t)1ULL);
v___x_1424_ = lean_usize_sub(v_depth_1407_, v___x_1423_);
v___x_1425_ = lean_usize_mul(v___x_1421_, v___x_1424_);
v_h_1426_ = lean_usize_shift_right(v_h_1420_, v___x_1425_);
v___x_1427_ = lean_nat_add(v_i_1410_, v___x_1422_);
lean_dec(v_i_1410_);
lean_inc(v_v_1415_);
lean_inc(v_k_1414_);
v___x_1428_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_entries_1411_, v_h_1426_, v_depth_1407_, v_k_1414_, v_v_1415_);
v_i_1410_ = v___x_1427_;
v_entries_1411_ = v___x_1428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1430_, lean_object* v_keys_1431_, lean_object* v_vals_1432_, lean_object* v_i_1433_, lean_object* v_entries_1434_){
_start:
{
size_t v_depth_boxed_1435_; lean_object* v_res_1436_; 
v_depth_boxed_1435_ = lean_unbox_usize(v_depth_1430_);
lean_dec(v_depth_1430_);
v_res_1436_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1435_, v_keys_1431_, v_vals_1432_, v_i_1433_, v_entries_1434_);
lean_dec_ref(v_vals_1432_);
lean_dec_ref(v_keys_1431_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
size_t v_x_3951__boxed_1442_; size_t v_x_3952__boxed_1443_; lean_object* v_res_1444_; 
v_x_3951__boxed_1442_ = lean_unbox_usize(v_x_1438_);
lean_dec(v_x_1438_);
v_x_3952__boxed_1443_ = lean_unbox_usize(v_x_1439_);
lean_dec(v_x_1439_);
v_res_1444_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_1437_, v_x_3951__boxed_1442_, v_x_3952__boxed_1443_, v_x_1440_, v_x_1441_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
size_t v___x_1448_; size_t v___x_1449_; size_t v___x_1450_; uint64_t v___x_1451_; size_t v___x_1452_; size_t v___x_1453_; lean_object* v___x_1454_; 
v___x_1448_ = lean_ptr_addr(v_x_1446_);
v___x_1449_ = ((size_t)3ULL);
v___x_1450_ = lean_usize_shift_right(v___x_1448_, v___x_1449_);
v___x_1451_ = lean_usize_to_uint64(v___x_1450_);
v___x_1452_ = lean_uint64_to_usize(v___x_1451_);
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_1445_, v___x_1452_, v___x_1453_, v_x_1446_, v_x_1447_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0(lean_object* v_type_1455_, lean_object* v_a_1456_, lean_object* v_s_1457_){
_start:
{
lean_object* v_rings_1458_; lean_object* v_typeIdOf_1459_; lean_object* v_exprToRingId_1460_; lean_object* v_semirings_1461_; lean_object* v_stypeIdOf_1462_; lean_object* v_exprToSemiringId_1463_; lean_object* v_ncRings_1464_; lean_object* v_exprToNCRingId_1465_; lean_object* v_nctypeIdOf_1466_; lean_object* v_ncSemirings_1467_; lean_object* v_exprToNCSemiringId_1468_; lean_object* v_ncstypeIdOf_1469_; lean_object* v_steps_1470_; uint8_t v_reportedMaxDegreeIssue_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1479_; 
v_rings_1458_ = lean_ctor_get(v_s_1457_, 0);
v_typeIdOf_1459_ = lean_ctor_get(v_s_1457_, 1);
v_exprToRingId_1460_ = lean_ctor_get(v_s_1457_, 2);
v_semirings_1461_ = lean_ctor_get(v_s_1457_, 3);
v_stypeIdOf_1462_ = lean_ctor_get(v_s_1457_, 4);
v_exprToSemiringId_1463_ = lean_ctor_get(v_s_1457_, 5);
v_ncRings_1464_ = lean_ctor_get(v_s_1457_, 6);
v_exprToNCRingId_1465_ = lean_ctor_get(v_s_1457_, 7);
v_nctypeIdOf_1466_ = lean_ctor_get(v_s_1457_, 8);
v_ncSemirings_1467_ = lean_ctor_get(v_s_1457_, 9);
v_exprToNCSemiringId_1468_ = lean_ctor_get(v_s_1457_, 10);
v_ncstypeIdOf_1469_ = lean_ctor_get(v_s_1457_, 11);
v_steps_1470_ = lean_ctor_get(v_s_1457_, 12);
v_reportedMaxDegreeIssue_1471_ = lean_ctor_get_uint8(v_s_1457_, sizeof(void*)*13);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_s_1457_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1473_ = v_s_1457_;
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_steps_1470_);
lean_inc(v_ncstypeIdOf_1469_);
lean_inc(v_exprToNCSemiringId_1468_);
lean_inc(v_ncSemirings_1467_);
lean_inc(v_nctypeIdOf_1466_);
lean_inc(v_exprToNCRingId_1465_);
lean_inc(v_ncRings_1464_);
lean_inc(v_exprToSemiringId_1463_);
lean_inc(v_stypeIdOf_1462_);
lean_inc(v_semirings_1461_);
lean_inc(v_exprToRingId_1460_);
lean_inc(v_typeIdOf_1459_);
lean_inc(v_rings_1458_);
lean_dec(v_s_1457_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1475_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_typeIdOf_1459_, v_type_1455_, v_a_1456_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v___x_1475_);
v___x_1477_ = v___x_1473_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_rings_1458_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_exprToRingId_1460_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v_semirings_1461_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v_stypeIdOf_1462_);
lean_ctor_set(v_reuseFailAlloc_1478_, 5, v_exprToSemiringId_1463_);
lean_ctor_set(v_reuseFailAlloc_1478_, 6, v_ncRings_1464_);
lean_ctor_set(v_reuseFailAlloc_1478_, 7, v_exprToNCRingId_1465_);
lean_ctor_set(v_reuseFailAlloc_1478_, 8, v_nctypeIdOf_1466_);
lean_ctor_set(v_reuseFailAlloc_1478_, 9, v_ncSemirings_1467_);
lean_ctor_set(v_reuseFailAlloc_1478_, 10, v_exprToNCSemiringId_1468_);
lean_ctor_set(v_reuseFailAlloc_1478_, 11, v_ncstypeIdOf_1469_);
lean_ctor_set(v_reuseFailAlloc_1478_, 12, v_steps_1470_);
lean_ctor_set_uint8(v_reuseFailAlloc_1478_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1471_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1480_, lean_object* v_vals_1481_, lean_object* v_i_1482_, lean_object* v_k_1483_){
_start:
{
lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1484_ = lean_array_get_size(v_keys_1480_);
v___x_1485_ = lean_nat_dec_lt(v_i_1482_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; 
lean_dec(v_i_1482_);
v___x_1486_ = lean_box(0);
return v___x_1486_;
}
else
{
lean_object* v_k_x27_1487_; size_t v___x_1488_; size_t v___x_1489_; uint8_t v___x_1490_; 
v_k_x27_1487_ = lean_array_fget_borrowed(v_keys_1480_, v_i_1482_);
v___x_1488_ = lean_ptr_addr(v_k_1483_);
v___x_1489_ = lean_ptr_addr(v_k_x27_1487_);
v___x_1490_ = lean_usize_dec_eq(v___x_1488_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_unsigned_to_nat(1u);
v___x_1492_ = lean_nat_add(v_i_1482_, v___x_1491_);
lean_dec(v_i_1482_);
v_i_1482_ = v___x_1492_;
goto _start;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_array_fget_borrowed(v_vals_1481_, v_i_1482_);
lean_dec(v_i_1482_);
lean_inc(v___x_1494_);
v___x_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
return v___x_1495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1496_, lean_object* v_vals_1497_, lean_object* v_i_1498_, lean_object* v_k_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1496_, v_vals_1497_, v_i_1498_, v_k_1499_);
lean_dec_ref(v_k_1499_);
lean_dec_ref(v_vals_1497_);
lean_dec_ref(v_keys_1496_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_1501_, size_t v_x_1502_, lean_object* v_x_1503_){
_start:
{
if (lean_obj_tag(v_x_1501_) == 0)
{
lean_object* v_es_1504_; lean_object* v___x_1505_; size_t v___x_1506_; size_t v___x_1507_; lean_object* v_j_1508_; lean_object* v___x_1509_; 
v_es_1504_ = lean_ctor_get(v_x_1501_, 0);
v___x_1505_ = lean_box(2);
v___x_1506_ = ((size_t)31ULL);
v___x_1507_ = lean_usize_land(v_x_1502_, v___x_1506_);
v_j_1508_ = lean_usize_to_nat(v___x_1507_);
v___x_1509_ = lean_array_get_borrowed(v___x_1505_, v_es_1504_, v_j_1508_);
lean_dec(v_j_1508_);
switch(lean_obj_tag(v___x_1509_))
{
case 0:
{
lean_object* v_key_1510_; lean_object* v_val_1511_; size_t v___x_1512_; size_t v___x_1513_; uint8_t v___x_1514_; 
v_key_1510_ = lean_ctor_get(v___x_1509_, 0);
v_val_1511_ = lean_ctor_get(v___x_1509_, 1);
v___x_1512_ = lean_ptr_addr(v_x_1503_);
v___x_1513_ = lean_ptr_addr(v_key_1510_);
v___x_1514_ = lean_usize_dec_eq(v___x_1512_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_box(0);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; 
lean_inc(v_val_1511_);
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_val_1511_);
return v___x_1516_;
}
}
case 1:
{
lean_object* v_node_1517_; size_t v___x_1518_; size_t v___x_1519_; 
v_node_1517_ = lean_ctor_get(v___x_1509_, 0);
v___x_1518_ = ((size_t)5ULL);
v___x_1519_ = lean_usize_shift_right(v_x_1502_, v___x_1518_);
v_x_1501_ = v_node_1517_;
v_x_1502_ = v___x_1519_;
goto _start;
}
default: 
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_box(0);
return v___x_1521_;
}
}
}
else
{
lean_object* v_ks_1522_; lean_object* v_vs_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_ks_1522_ = lean_ctor_get(v_x_1501_, 0);
v_vs_1523_ = lean_ctor_get(v_x_1501_, 1);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1522_, v_vs_1523_, v___x_1524_, v_x_1503_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_){
_start:
{
size_t v_x_4170__boxed_1529_; lean_object* v_res_1530_; 
v_x_4170__boxed_1529_ = lean_unbox_usize(v_x_1527_);
lean_dec(v_x_1527_);
v_res_1530_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_1526_, v_x_4170__boxed_1529_, v_x_1528_);
lean_dec_ref(v_x_1528_);
lean_dec_ref(v_x_1526_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
size_t v___x_1533_; size_t v___x_1534_; size_t v___x_1535_; uint64_t v___x_1536_; size_t v___x_1537_; lean_object* v___x_1538_; 
v___x_1533_ = lean_ptr_addr(v_x_1532_);
v___x_1534_ = ((size_t)3ULL);
v___x_1535_ = lean_usize_shift_right(v___x_1533_, v___x_1534_);
v___x_1536_ = lean_usize_to_uint64(v___x_1535_);
v___x_1537_ = lean_uint64_to_usize(v___x_1536_);
v___x_1538_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_1531_, v___x_1537_, v_x_1532_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_1539_, lean_object* v_x_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_1539_, v_x_1540_);
lean_dec_ref(v_x_1540_);
lean_dec_ref(v_x_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object* v_type_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1543_, v_a_1551_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1586_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1557_ = v___x_1554_;
v_isShared_1558_ = v_isSharedCheck_1586_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1554_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1586_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v_typeIdOf_1559_; lean_object* v___x_1560_; 
v_typeIdOf_1559_ = lean_ctor_get(v_a_1555_, 1);
lean_inc_ref(v_typeIdOf_1559_);
lean_dec(v_a_1555_);
v___x_1560_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_typeIdOf_1559_, v_type_1542_);
lean_dec_ref(v_typeIdOf_1559_);
if (lean_obj_tag(v___x_1560_) == 1)
{
lean_object* v_val_1561_; lean_object* v___x_1563_; 
lean_dec_ref(v_type_1542_);
v_val_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_val_1561_);
lean_dec_ref_known(v___x_1560_, 1);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v_val_1561_);
v___x_1563_ = v___x_1557_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_val_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
else
{
lean_object* v___x_1565_; 
lean_dec(v___x_1560_);
lean_del_object(v___x_1557_);
lean_inc_ref(v_type_1542_);
v___x_1565_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f(v_type_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc_n(v_a_1566_, 2);
lean_dec_ref_known(v___x_1565_, 1);
v___f_1567_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1567_, 0, v_type_1542_);
lean_closure_set(v___f_1567_, 1, v_a_1566_);
v___x_1568_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1569_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1568_, v___f_1567_, v_a_1543_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v___x_1569_, 0);
lean_dec(v_unused_1577_);
v___x_1571_ = v___x_1569_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_dec(v___x_1569_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v_a_1566_);
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1566_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v_a_1566_);
v_a_1578_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1569_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1569_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_dec_ref(v_type_1542_);
return v___x_1565_;
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v_type_1542_);
v_a_1587_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1554_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1554_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___boxed(lean_object* v_type_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec(v_a_1596_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(lean_object* v_00_u03b2_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_x_1609_, v_x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0(v_00_u03b2_1612_, v_x_1613_, v_x_1614_);
lean_dec_ref(v_x_1614_);
lean_dec_ref(v_x_1613_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1(lean_object* v_00_u03b2_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_x_1617_, v_x_1618_, v_x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1621_, lean_object* v_x_1622_, size_t v_x_1623_, lean_object* v_x_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___redArg(v_x_1622_, v_x_1623_, v_x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_){
_start:
{
size_t v_x_4340__boxed_1630_; lean_object* v_res_1631_; 
v_x_4340__boxed_1630_ = lean_unbox_usize(v_x_1628_);
lean_dec(v_x_1628_);
v_res_1631_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0(v_00_u03b2_1626_, v_x_1627_, v_x_4340__boxed_1630_, v_x_1629_);
lean_dec_ref(v_x_1629_);
lean_dec_ref(v_x_1627_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(lean_object* v_00_u03b2_1632_, lean_object* v_x_1633_, size_t v_x_1634_, size_t v_x_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___redArg(v_x_1633_, v_x_1634_, v_x_1635_, v_x_1636_, v_x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_, lean_object* v_x_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
size_t v_x_4351__boxed_1645_; size_t v_x_4352__boxed_1646_; lean_object* v_res_1647_; 
v_x_4351__boxed_1645_ = lean_unbox_usize(v_x_1641_);
lean_dec(v_x_1641_);
v_x_4352__boxed_1646_ = lean_unbox_usize(v_x_1642_);
lean_dec(v_x_1642_);
v_res_1647_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2(v_00_u03b2_1639_, v_x_1640_, v_x_4351__boxed_1645_, v_x_4352__boxed_1646_, v_x_1643_, v_x_1644_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1648_, lean_object* v_keys_1649_, lean_object* v_vals_1650_, lean_object* v_heq_1651_, lean_object* v_i_1652_, lean_object* v_k_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1649_, v_vals_1650_, v_i_1652_, v_k_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1655_, lean_object* v_keys_1656_, lean_object* v_vals_1657_, lean_object* v_heq_1658_, lean_object* v_i_1659_, lean_object* v_k_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1655_, v_keys_1656_, v_vals_1657_, v_heq_1658_, v_i_1659_, v_k_1660_);
lean_dec_ref(v_k_1660_);
lean_dec_ref(v_vals_1657_);
lean_dec_ref(v_keys_1656_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1662_, lean_object* v_n_1663_, lean_object* v_k_1664_, lean_object* v_v_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4___redArg(v_n_1663_, v_k_1664_, v_v_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1667_, size_t v_depth_1668_, lean_object* v_keys_1669_, lean_object* v_vals_1670_, lean_object* v_heq_1671_, lean_object* v_i_1672_, lean_object* v_entries_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___redArg(v_depth_1668_, v_keys_1669_, v_vals_1670_, v_i_1672_, v_entries_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1675_, lean_object* v_depth_1676_, lean_object* v_keys_1677_, lean_object* v_vals_1678_, lean_object* v_heq_1679_, lean_object* v_i_1680_, lean_object* v_entries_1681_){
_start:
{
size_t v_depth_boxed_1682_; lean_object* v_res_1683_; 
v_depth_boxed_1682_ = lean_unbox_usize(v_depth_1676_);
lean_dec(v_depth_1676_);
v_res_1683_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1675_, v_depth_boxed_1682_, v_keys_1677_, v_vals_1678_, v_heq_1679_, v_i_1680_, v_entries_1681_);
lean_dec_ref(v_vals_1678_);
lean_dec_ref(v_keys_1677_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1684_, lean_object* v_x_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_, lean_object* v_x_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1685_, v_x_1686_, v_x_1687_, v_x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0(lean_object* v___x_1690_, lean_object* v_s_1691_){
_start:
{
lean_object* v_rings_1692_; lean_object* v_typeIdOf_1693_; lean_object* v_exprToRingId_1694_; lean_object* v_semirings_1695_; lean_object* v_stypeIdOf_1696_; lean_object* v_exprToSemiringId_1697_; lean_object* v_ncRings_1698_; lean_object* v_exprToNCRingId_1699_; lean_object* v_nctypeIdOf_1700_; lean_object* v_ncSemirings_1701_; lean_object* v_exprToNCSemiringId_1702_; lean_object* v_ncstypeIdOf_1703_; lean_object* v_steps_1704_; uint8_t v_reportedMaxDegreeIssue_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1713_; 
v_rings_1692_ = lean_ctor_get(v_s_1691_, 0);
v_typeIdOf_1693_ = lean_ctor_get(v_s_1691_, 1);
v_exprToRingId_1694_ = lean_ctor_get(v_s_1691_, 2);
v_semirings_1695_ = lean_ctor_get(v_s_1691_, 3);
v_stypeIdOf_1696_ = lean_ctor_get(v_s_1691_, 4);
v_exprToSemiringId_1697_ = lean_ctor_get(v_s_1691_, 5);
v_ncRings_1698_ = lean_ctor_get(v_s_1691_, 6);
v_exprToNCRingId_1699_ = lean_ctor_get(v_s_1691_, 7);
v_nctypeIdOf_1700_ = lean_ctor_get(v_s_1691_, 8);
v_ncSemirings_1701_ = lean_ctor_get(v_s_1691_, 9);
v_exprToNCSemiringId_1702_ = lean_ctor_get(v_s_1691_, 10);
v_ncstypeIdOf_1703_ = lean_ctor_get(v_s_1691_, 11);
v_steps_1704_ = lean_ctor_get(v_s_1691_, 12);
v_reportedMaxDegreeIssue_1705_ = lean_ctor_get_uint8(v_s_1691_, sizeof(void*)*13);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_s_1691_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1707_ = v_s_1691_;
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_steps_1704_);
lean_inc(v_ncstypeIdOf_1703_);
lean_inc(v_exprToNCSemiringId_1702_);
lean_inc(v_ncSemirings_1701_);
lean_inc(v_nctypeIdOf_1700_);
lean_inc(v_exprToNCRingId_1699_);
lean_inc(v_ncRings_1698_);
lean_inc(v_exprToSemiringId_1697_);
lean_inc(v_stypeIdOf_1696_);
lean_inc(v_semirings_1695_);
lean_inc(v_exprToRingId_1694_);
lean_inc(v_typeIdOf_1693_);
lean_inc(v_rings_1692_);
lean_dec(v_s_1691_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1709_ = lean_array_push(v_ncRings_1698_, v___x_1690_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 6, v___x_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_rings_1692_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_typeIdOf_1693_);
lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_exprToRingId_1694_);
lean_ctor_set(v_reuseFailAlloc_1712_, 3, v_semirings_1695_);
lean_ctor_set(v_reuseFailAlloc_1712_, 4, v_stypeIdOf_1696_);
lean_ctor_set(v_reuseFailAlloc_1712_, 5, v_exprToSemiringId_1697_);
lean_ctor_set(v_reuseFailAlloc_1712_, 6, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1712_, 7, v_exprToNCRingId_1699_);
lean_ctor_set(v_reuseFailAlloc_1712_, 8, v_nctypeIdOf_1700_);
lean_ctor_set(v_reuseFailAlloc_1712_, 9, v_ncSemirings_1701_);
lean_ctor_set(v_reuseFailAlloc_1712_, 10, v_exprToNCSemiringId_1702_);
lean_ctor_set(v_reuseFailAlloc_1712_, 11, v_ncstypeIdOf_1703_);
lean_ctor_set(v_reuseFailAlloc_1712_, 12, v_steps_1704_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1705_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(lean_object* v_type_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v___x_1726_; 
lean_inc_ref(v_type_1714_);
v___x_1726_ = l_Lean_Meta_getDecLevel(v_type_1714_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc_n(v_a_1727_, 2);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__5));
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_a_1727_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
lean_inc_ref(v___x_1730_);
v___x_1731_ = l_Lean_mkConst(v___x_1728_, v___x_1730_);
lean_inc_ref(v_type_1714_);
v___x_1732_ = l_Lean_Expr_app___override(v___x_1731_, v_type_1714_);
v___x_1733_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1732_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1839_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1839_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1839_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
if (lean_obj_tag(v_a_1734_) == 1)
{
lean_object* v_toCold_1738_; lean_object* v_options_1739_; lean_object* v_val_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1834_; 
lean_del_object(v___x_1736_);
v_toCold_1738_ = lean_ctor_get(v_a_1723_, 0);
v_options_1739_ = lean_ctor_get(v_toCold_1738_, 2);
v_val_1740_ = lean_ctor_get(v_a_1734_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_a_1734_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1742_ = v_a_1734_;
v_isShared_1743_ = v_isSharedCheck_1834_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_val_1740_);
lean_dec(v_a_1734_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1834_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v_inheritedTraceOptions_1744_; uint8_t v_hasTrace_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; 
v_inheritedTraceOptions_1744_ = lean_ctor_get(v_toCold_1738_, 11);
v_hasTrace_1745_ = lean_ctor_get_uint8(v_options_1739_, sizeof(void*)*1);
v___x_1746_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__11));
v___x_1747_ = l_Lean_mkConst(v___x_1746_, v___x_1730_);
lean_inc(v_val_1740_);
lean_inc_ref(v_type_1714_);
v___x_1748_ = l_Lean_mkAppB(v___x_1747_, v_type_1714_, v_val_1740_);
if (v_hasTrace_1745_ == 0)
{
v___y_1750_ = v_a_1715_;
v___y_1751_ = v_a_1716_;
v___y_1752_ = v_a_1717_;
v___y_1753_ = v_a_1718_;
v___y_1754_ = v_a_1719_;
v___y_1755_ = v_a_1720_;
v___y_1756_ = v_a_1721_;
v___y_1757_ = v_a_1722_;
v___y_1758_ = v_a_1723_;
v___y_1759_ = v_a_1724_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__6));
v___x_1811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__21);
v___x_1812_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1744_, v_options_1739_, v___x_1811_);
if (v___x_1812_ == 0)
{
v___y_1750_ = v_a_1715_;
v___y_1751_ = v_a_1716_;
v___y_1752_ = v_a_1717_;
v___y_1753_ = v_a_1718_;
v___y_1754_ = v_a_1719_;
v___y_1755_ = v_a_1720_;
v___y_1756_ = v_a_1721_;
v___y_1757_ = v_a_1722_;
v___y_1758_ = v_a_1723_;
v___y_1759_ = v_a_1724_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_Meta_Grind_updateLastTag(v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec_ref_known(v___x_1813_, 1);
v___x_1814_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__29, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__29);
lean_inc_ref(v_type_1714_);
v___x_1815_ = l_Lean_MessageData_ofExpr(v_type_1714_);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1___redArg(v___x_1810_, v___x_1816_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_dec_ref_known(v___x_1817_, 1);
v___y_1750_ = v_a_1715_;
v___y_1751_ = v_a_1716_;
v___y_1752_ = v_a_1717_;
v___y_1753_ = v_a_1718_;
v___y_1754_ = v_a_1719_;
v___y_1755_ = v_a_1720_;
v___y_1756_ = v_a_1721_;
v___y_1757_ = v_a_1722_;
v___y_1758_ = v_a_1723_;
v___y_1759_ = v_a_1724_;
goto v___jp_1749_;
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec_ref(v___x_1748_);
lean_del_object(v___x_1742_);
lean_dec(v_val_1740_);
lean_dec(v_a_1727_);
lean_dec_ref(v_type_1714_);
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v___x_1748_);
lean_del_object(v___x_1742_);
lean_dec(v_val_1740_);
lean_dec(v_a_1727_);
lean_dec_ref(v_type_1714_);
v_a_1826_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1813_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1813_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
v___jp_1749_:
{
lean_object* v___x_1760_; 
lean_inc_ref(v___x_1748_);
lean_inc_ref(v_type_1714_);
lean_inc(v_a_1727_);
v___x_1760_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(v_a_1727_, v_type_1714_, v___x_1748_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1762_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v___x_1762_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v___y_1750_, v___y_1758_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v_ncRings_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___f_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v_ncRings_1764_ = lean_ctor_get(v_a_1763_, 6);
lean_inc_ref(v_ncRings_1764_);
lean_dec(v_a_1763_);
v___x_1765_ = lean_array_get_size(v_ncRings_1764_);
lean_dec_ref(v_ncRings_1764_);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_unsigned_to_nat(32u);
v___x_1768_ = lean_mk_empty_array_with_capacity(v___x_1767_);
lean_dec_ref(v___x_1768_);
v___x_1769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15);
v___x_1770_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__17);
v___x_1771_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1765_);
lean_ctor_set(v___x_1771_, 1, v_type_1714_);
lean_ctor_set(v___x_1771_, 2, v_a_1727_);
lean_ctor_set(v___x_1771_, 3, v_val_1740_);
lean_ctor_set(v___x_1771_, 4, v___x_1748_);
lean_ctor_set(v___x_1771_, 5, v_a_1761_);
lean_ctor_set(v___x_1771_, 6, v___x_1766_);
lean_ctor_set(v___x_1771_, 7, v___x_1766_);
lean_ctor_set(v___x_1771_, 8, v___x_1766_);
lean_ctor_set(v___x_1771_, 9, v___x_1766_);
lean_ctor_set(v___x_1771_, 10, v___x_1766_);
lean_ctor_set(v___x_1771_, 11, v___x_1766_);
lean_ctor_set(v___x_1771_, 12, v___x_1766_);
lean_ctor_set(v___x_1771_, 13, v___x_1766_);
lean_ctor_set(v___x_1771_, 14, v___x_1769_);
lean_ctor_set(v___x_1771_, 15, v___x_1770_);
lean_ctor_set(v___x_1771_, 16, v___x_1770_);
v___f_1772_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1772_, 0, v___x_1771_);
v___x_1773_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1774_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1773_, v___f_1772_, v___y_1750_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1784_; 
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v___x_1774_, 0);
lean_dec(v_unused_1785_);
v___x_1776_ = v___x_1774_;
v_isShared_1777_ = v_isSharedCheck_1784_;
goto v_resetjp_1775_;
}
else
{
lean_dec(v___x_1774_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1784_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1765_);
v___x_1779_ = v___x_1742_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1765_);
v___x_1779_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1779_);
v___x_1781_ = v___x_1776_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_del_object(v___x_1742_);
v_a_1786_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1774_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1774_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec(v_a_1761_);
lean_dec_ref(v___x_1748_);
lean_del_object(v___x_1742_);
lean_dec(v_val_1740_);
lean_dec(v_a_1727_);
lean_dec_ref(v_type_1714_);
v_a_1794_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1762_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1762_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec_ref(v___x_1748_);
lean_del_object(v___x_1742_);
lean_dec(v_val_1740_);
lean_dec(v_a_1727_);
lean_dec_ref(v_type_1714_);
v_a_1802_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1760_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1760_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
lean_dec(v_a_1734_);
lean_dec_ref_known(v___x_1730_, 2);
lean_dec(v_a_1727_);
lean_dec_ref(v_type_1714_);
v___x_1835_ = lean_box(0);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1835_);
v___x_1837_ = v___x_1736_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec_ref_known(v___x_1730_, 2);
lean_dec(v_a_1727_);
lean_dec_ref(v_type_1714_);
v_a_1840_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1733_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1733_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec_ref(v_type_1714_);
v_a_1848_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1726_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1726_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f___boxed(lean_object* v_type_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec(v_a_1857_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0(lean_object* v_type_1869_, lean_object* v_a_1870_, lean_object* v_s_1871_){
_start:
{
lean_object* v_rings_1872_; lean_object* v_typeIdOf_1873_; lean_object* v_exprToRingId_1874_; lean_object* v_semirings_1875_; lean_object* v_stypeIdOf_1876_; lean_object* v_exprToSemiringId_1877_; lean_object* v_ncRings_1878_; lean_object* v_exprToNCRingId_1879_; lean_object* v_nctypeIdOf_1880_; lean_object* v_ncSemirings_1881_; lean_object* v_exprToNCSemiringId_1882_; lean_object* v_ncstypeIdOf_1883_; lean_object* v_steps_1884_; uint8_t v_reportedMaxDegreeIssue_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1893_; 
v_rings_1872_ = lean_ctor_get(v_s_1871_, 0);
v_typeIdOf_1873_ = lean_ctor_get(v_s_1871_, 1);
v_exprToRingId_1874_ = lean_ctor_get(v_s_1871_, 2);
v_semirings_1875_ = lean_ctor_get(v_s_1871_, 3);
v_stypeIdOf_1876_ = lean_ctor_get(v_s_1871_, 4);
v_exprToSemiringId_1877_ = lean_ctor_get(v_s_1871_, 5);
v_ncRings_1878_ = lean_ctor_get(v_s_1871_, 6);
v_exprToNCRingId_1879_ = lean_ctor_get(v_s_1871_, 7);
v_nctypeIdOf_1880_ = lean_ctor_get(v_s_1871_, 8);
v_ncSemirings_1881_ = lean_ctor_get(v_s_1871_, 9);
v_exprToNCSemiringId_1882_ = lean_ctor_get(v_s_1871_, 10);
v_ncstypeIdOf_1883_ = lean_ctor_get(v_s_1871_, 11);
v_steps_1884_ = lean_ctor_get(v_s_1871_, 12);
v_reportedMaxDegreeIssue_1885_ = lean_ctor_get_uint8(v_s_1871_, sizeof(void*)*13);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_s_1871_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1887_ = v_s_1871_;
v_isShared_1888_ = v_isSharedCheck_1893_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_steps_1884_);
lean_inc(v_ncstypeIdOf_1883_);
lean_inc(v_exprToNCSemiringId_1882_);
lean_inc(v_ncSemirings_1881_);
lean_inc(v_nctypeIdOf_1880_);
lean_inc(v_exprToNCRingId_1879_);
lean_inc(v_ncRings_1878_);
lean_inc(v_exprToSemiringId_1877_);
lean_inc(v_stypeIdOf_1876_);
lean_inc(v_semirings_1875_);
lean_inc(v_exprToRingId_1874_);
lean_inc(v_typeIdOf_1873_);
lean_inc(v_rings_1872_);
lean_dec(v_s_1871_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1893_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1889_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_nctypeIdOf_1880_, v_type_1869_, v_a_1870_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 8, v___x_1889_);
v___x_1891_ = v___x_1887_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_rings_1872_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_typeIdOf_1873_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_exprToRingId_1874_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_semirings_1875_);
lean_ctor_set(v_reuseFailAlloc_1892_, 4, v_stypeIdOf_1876_);
lean_ctor_set(v_reuseFailAlloc_1892_, 5, v_exprToSemiringId_1877_);
lean_ctor_set(v_reuseFailAlloc_1892_, 6, v_ncRings_1878_);
lean_ctor_set(v_reuseFailAlloc_1892_, 7, v_exprToNCRingId_1879_);
lean_ctor_set(v_reuseFailAlloc_1892_, 8, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1892_, 9, v_ncSemirings_1881_);
lean_ctor_set(v_reuseFailAlloc_1892_, 10, v_exprToNCSemiringId_1882_);
lean_ctor_set(v_reuseFailAlloc_1892_, 11, v_ncstypeIdOf_1883_);
lean_ctor_set(v_reuseFailAlloc_1892_, 12, v_steps_1884_);
lean_ctor_set_uint8(v_reuseFailAlloc_1892_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1885_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object* v_type_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1895_, v_a_1903_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1938_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1938_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1938_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_nctypeIdOf_1911_; lean_object* v___x_1912_; 
v_nctypeIdOf_1911_ = lean_ctor_get(v_a_1907_, 8);
lean_inc_ref(v_nctypeIdOf_1911_);
lean_dec(v_a_1907_);
v___x_1912_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_nctypeIdOf_1911_, v_type_1894_);
lean_dec_ref(v_nctypeIdOf_1911_);
if (lean_obj_tag(v___x_1912_) == 1)
{
lean_object* v_val_1913_; lean_object* v___x_1915_; 
lean_dec_ref(v_type_1894_);
v_val_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_val_1913_);
lean_dec_ref_known(v___x_1912_, 1);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v_val_1913_);
v___x_1915_ = v___x_1909_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_val_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
else
{
lean_object* v___x_1917_; 
lean_dec(v___x_1912_);
lean_del_object(v___x_1909_);
lean_inc_ref(v_type_1894_);
v___x_1917_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f_go_x3f(v_type_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___f_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc_n(v_a_1918_, 2);
lean_dec_ref_known(v___x_1917_, 1);
v___f_1919_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1919_, 0, v_type_1894_);
lean_closure_set(v___f_1919_, 1, v_a_1918_);
v___x_1920_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1921_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1920_, v___f_1919_, v_a_1895_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; 
v_unused_1929_ = lean_ctor_get(v___x_1921_, 0);
lean_dec(v_unused_1929_);
v___x_1923_ = v___x_1921_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_dec(v___x_1921_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v_a_1918_);
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1918_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_a_1918_);
v_a_1930_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1921_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1921_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_dec_ref(v_type_1894_);
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v_type_1894_);
v_a_1939_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1906_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1906_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___boxed(lean_object* v_type_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_type_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec(v_a_1948_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0(lean_object* v_semiringId_1960_, lean_object* v_s_1961_){
_start:
{
lean_object* v_toRing_1962_; lean_object* v_invFn_x3f_1963_; lean_object* v_commSemiringInst_1964_; lean_object* v_commRingInst_1965_; lean_object* v_noZeroDivInst_x3f_1966_; lean_object* v_fieldInst_x3f_1967_; lean_object* v_powIdentityInst_x3f_1968_; lean_object* v_denoteEntries_1969_; lean_object* v_nextId_1970_; lean_object* v_steps_1971_; lean_object* v_queue_1972_; lean_object* v_basis_1973_; lean_object* v_diseqs_1974_; uint8_t v_recheck_1975_; lean_object* v_invSet_1976_; lean_object* v_powIdentityVarCount_1977_; lean_object* v_numEq0_x3f_1978_; uint8_t v_numEq0Updated_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1987_; 
v_toRing_1962_ = lean_ctor_get(v_s_1961_, 0);
v_invFn_x3f_1963_ = lean_ctor_get(v_s_1961_, 1);
v_commSemiringInst_1964_ = lean_ctor_get(v_s_1961_, 3);
v_commRingInst_1965_ = lean_ctor_get(v_s_1961_, 4);
v_noZeroDivInst_x3f_1966_ = lean_ctor_get(v_s_1961_, 5);
v_fieldInst_x3f_1967_ = lean_ctor_get(v_s_1961_, 6);
v_powIdentityInst_x3f_1968_ = lean_ctor_get(v_s_1961_, 7);
v_denoteEntries_1969_ = lean_ctor_get(v_s_1961_, 8);
v_nextId_1970_ = lean_ctor_get(v_s_1961_, 9);
v_steps_1971_ = lean_ctor_get(v_s_1961_, 10);
v_queue_1972_ = lean_ctor_get(v_s_1961_, 11);
v_basis_1973_ = lean_ctor_get(v_s_1961_, 12);
v_diseqs_1974_ = lean_ctor_get(v_s_1961_, 13);
v_recheck_1975_ = lean_ctor_get_uint8(v_s_1961_, sizeof(void*)*17);
v_invSet_1976_ = lean_ctor_get(v_s_1961_, 14);
v_powIdentityVarCount_1977_ = lean_ctor_get(v_s_1961_, 15);
v_numEq0_x3f_1978_ = lean_ctor_get(v_s_1961_, 16);
v_numEq0Updated_1979_ = lean_ctor_get_uint8(v_s_1961_, sizeof(void*)*17 + 1);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_s_1961_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v_s_1961_, 2);
lean_dec(v_unused_1988_);
v___x_1981_ = v_s_1961_;
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_numEq0_x3f_1978_);
lean_inc(v_powIdentityVarCount_1977_);
lean_inc(v_invSet_1976_);
lean_inc(v_diseqs_1974_);
lean_inc(v_basis_1973_);
lean_inc(v_queue_1972_);
lean_inc(v_steps_1971_);
lean_inc(v_nextId_1970_);
lean_inc(v_denoteEntries_1969_);
lean_inc(v_powIdentityInst_x3f_1968_);
lean_inc(v_fieldInst_x3f_1967_);
lean_inc(v_noZeroDivInst_x3f_1966_);
lean_inc(v_commRingInst_1965_);
lean_inc(v_commSemiringInst_1964_);
lean_inc(v_invFn_x3f_1963_);
lean_inc(v_toRing_1962_);
lean_dec(v_s_1961_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_semiringId_1960_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 2, v___x_1983_);
v___x_1985_ = v___x_1981_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_toRing_1962_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_invFn_x3f_1963_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_commSemiringInst_1964_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_commRingInst_1965_);
lean_ctor_set(v_reuseFailAlloc_1986_, 5, v_noZeroDivInst_x3f_1966_);
lean_ctor_set(v_reuseFailAlloc_1986_, 6, v_fieldInst_x3f_1967_);
lean_ctor_set(v_reuseFailAlloc_1986_, 7, v_powIdentityInst_x3f_1968_);
lean_ctor_set(v_reuseFailAlloc_1986_, 8, v_denoteEntries_1969_);
lean_ctor_set(v_reuseFailAlloc_1986_, 9, v_nextId_1970_);
lean_ctor_set(v_reuseFailAlloc_1986_, 10, v_steps_1971_);
lean_ctor_set(v_reuseFailAlloc_1986_, 11, v_queue_1972_);
lean_ctor_set(v_reuseFailAlloc_1986_, 12, v_basis_1973_);
lean_ctor_set(v_reuseFailAlloc_1986_, 13, v_diseqs_1974_);
lean_ctor_set(v_reuseFailAlloc_1986_, 14, v_invSet_1976_);
lean_ctor_set(v_reuseFailAlloc_1986_, 15, v_powIdentityVarCount_1977_);
lean_ctor_set(v_reuseFailAlloc_1986_, 16, v_numEq0_x3f_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*17, v_recheck_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*17 + 1, v_numEq0Updated_1979_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(lean_object* v_ringId_1989_, lean_object* v_semiringId_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v___f_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___f_1993_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1993_, 0, v_semiringId_1990_);
v___x_1994_ = 0;
v___x_1995_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1995_, 0, v_ringId_1989_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*1, v___x_1994_);
v___x_1996_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1993_, v___x_1995_, v_a_1991_);
lean_dec_ref_known(v___x_1995_, 1);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg___boxed(lean_object* v_ringId_1997_, lean_object* v_semiringId_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_1997_, v_semiringId_1998_, v_a_1999_);
lean_dec(v_a_1999_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(lean_object* v_ringId_2002_, lean_object* v_semiringId_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_ringId_2002_, v_semiringId_2003_, v_a_2004_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___boxed(lean_object* v_ringId_2016_, lean_object* v_semiringId_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId(v_ringId_2016_, v_semiringId_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
lean_dec(v_a_2025_);
lean_dec_ref(v_a_2024_);
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
lean_dec(v_a_2018_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0(lean_object* v___x_2030_, lean_object* v_s_2031_){
_start:
{
lean_object* v_rings_2032_; lean_object* v_typeIdOf_2033_; lean_object* v_exprToRingId_2034_; lean_object* v_semirings_2035_; lean_object* v_stypeIdOf_2036_; lean_object* v_exprToSemiringId_2037_; lean_object* v_ncRings_2038_; lean_object* v_exprToNCRingId_2039_; lean_object* v_nctypeIdOf_2040_; lean_object* v_ncSemirings_2041_; lean_object* v_exprToNCSemiringId_2042_; lean_object* v_ncstypeIdOf_2043_; lean_object* v_steps_2044_; uint8_t v_reportedMaxDegreeIssue_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2053_; 
v_rings_2032_ = lean_ctor_get(v_s_2031_, 0);
v_typeIdOf_2033_ = lean_ctor_get(v_s_2031_, 1);
v_exprToRingId_2034_ = lean_ctor_get(v_s_2031_, 2);
v_semirings_2035_ = lean_ctor_get(v_s_2031_, 3);
v_stypeIdOf_2036_ = lean_ctor_get(v_s_2031_, 4);
v_exprToSemiringId_2037_ = lean_ctor_get(v_s_2031_, 5);
v_ncRings_2038_ = lean_ctor_get(v_s_2031_, 6);
v_exprToNCRingId_2039_ = lean_ctor_get(v_s_2031_, 7);
v_nctypeIdOf_2040_ = lean_ctor_get(v_s_2031_, 8);
v_ncSemirings_2041_ = lean_ctor_get(v_s_2031_, 9);
v_exprToNCSemiringId_2042_ = lean_ctor_get(v_s_2031_, 10);
v_ncstypeIdOf_2043_ = lean_ctor_get(v_s_2031_, 11);
v_steps_2044_ = lean_ctor_get(v_s_2031_, 12);
v_reportedMaxDegreeIssue_2045_ = lean_ctor_get_uint8(v_s_2031_, sizeof(void*)*13);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_s_2031_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2047_ = v_s_2031_;
v_isShared_2048_ = v_isSharedCheck_2053_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_steps_2044_);
lean_inc(v_ncstypeIdOf_2043_);
lean_inc(v_exprToNCSemiringId_2042_);
lean_inc(v_ncSemirings_2041_);
lean_inc(v_nctypeIdOf_2040_);
lean_inc(v_exprToNCRingId_2039_);
lean_inc(v_ncRings_2038_);
lean_inc(v_exprToSemiringId_2037_);
lean_inc(v_stypeIdOf_2036_);
lean_inc(v_semirings_2035_);
lean_inc(v_exprToRingId_2034_);
lean_inc(v_typeIdOf_2033_);
lean_inc(v_rings_2032_);
lean_dec(v_s_2031_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2053_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2049_ = lean_array_push(v_semirings_2035_, v___x_2030_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 3, v___x_2049_);
v___x_2051_ = v___x_2047_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_rings_2032_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_typeIdOf_2033_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_exprToRingId_2034_);
lean_ctor_set(v_reuseFailAlloc_2052_, 3, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2052_, 4, v_stypeIdOf_2036_);
lean_ctor_set(v_reuseFailAlloc_2052_, 5, v_exprToSemiringId_2037_);
lean_ctor_set(v_reuseFailAlloc_2052_, 6, v_ncRings_2038_);
lean_ctor_set(v_reuseFailAlloc_2052_, 7, v_exprToNCRingId_2039_);
lean_ctor_set(v_reuseFailAlloc_2052_, 8, v_nctypeIdOf_2040_);
lean_ctor_set(v_reuseFailAlloc_2052_, 9, v_ncSemirings_2041_);
lean_ctor_set(v_reuseFailAlloc_2052_, 10, v_exprToNCSemiringId_2042_);
lean_ctor_set(v_reuseFailAlloc_2052_, 11, v_ncstypeIdOf_2043_);
lean_ctor_set(v_reuseFailAlloc_2052_, 12, v_steps_2044_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2045_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(lean_object* v_msg_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_ref_2060_; lean_object* v___x_2061_; lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2070_; 
v_ref_2060_ = lean_ctor_get(v___y_2057_, 2);
v___x_2061_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f_spec__1_spec__1(v_msg_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2070_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2070_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
lean_inc(v_ref_2060_);
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v_ref_2060_);
lean_ctor_set(v___x_2066_, 1, v_a_2062_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set_tag(v___x_2064_, 1);
lean_ctor_set(v___x_2064_, 0, v___x_2066_);
v___x_2068_ = v___x_2064_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg___boxed(lean_object* v_msg_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
return v_res_2077_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0(void){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2078_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__0);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__2));
v___x_2083_ = l_Lean_stringToMessageData(v___x_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(lean_object* v_type_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v___x_2096_; 
lean_inc_ref(v_type_2084_);
v___x_2096_ = l_Lean_Meta_getDecLevel(v_type_2084_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc_n(v_a_2097_, 2);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__8));
v___x_2099_ = lean_box(0);
v___x_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2100_, 0, v_a_2097_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
lean_inc_ref(v___x_2100_);
v___x_2101_ = l_Lean_mkConst(v___x_2098_, v___x_2100_);
lean_inc_ref(v_type_2084_);
v___x_2102_ = l_Lean_Expr_app___override(v___x_2101_, v_type_2084_);
v___x_2103_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2102_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2198_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2198_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2198_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
if (lean_obj_tag(v_a_2104_) == 1)
{
lean_object* v_val_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_del_object(v___x_2106_);
v_val_2108_ = lean_ctor_get(v_a_2104_, 0);
lean_inc_n(v_val_2108_, 2);
lean_dec_ref_known(v_a_2104_, 1);
v___x_2109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__1));
lean_inc_ref(v___x_2100_);
v___x_2110_ = l_Lean_mkConst(v___x_2109_, v___x_2100_);
lean_inc_ref_n(v_type_2084_, 2);
v___x_2111_ = l_Lean_mkAppB(v___x_2110_, v_type_2084_, v_val_2108_);
v___x_2112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_go_x3f___closed__1));
v___x_2113_ = l_Lean_mkConst(v___x_2112_, v___x_2100_);
lean_inc_ref(v___x_2111_);
v___x_2114_ = l_Lean_mkAppB(v___x_2113_, v_type_2084_, v___x_2111_);
v___x_2115_ = l_Lean_Meta_Sym_canon(v___x_2114_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2115_, 1);
v___x_2117_ = l_Lean_Meta_Sym_shareCommon(v_a_2116_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2119_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc_n(v_a_2118_, 2);
lean_dec_ref_known(v___x_2117_, 1);
v___x_2119_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_a_2118_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
if (lean_obj_tag(v_a_2120_) == 1)
{
lean_object* v_val_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v_a_2118_);
v_val_2121_ = lean_ctor_get(v_a_2120_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_a_2120_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2123_ = v_a_2120_;
v_isShared_2124_ = v_isSharedCheck_2173_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_val_2121_);
lean_dec(v_a_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2173_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2085_, v_a_2093_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v_semirings_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___f_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v_semirings_2127_ = lean_ctor_get(v_a_2126_, 3);
lean_inc_ref(v_semirings_2127_);
lean_dec(v_a_2126_);
v___x_2128_ = lean_array_get_size(v_semirings_2127_);
lean_dec_ref(v_semirings_2127_);
v___x_2129_ = lean_box(0);
v___x_2130_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1);
v___x_2131_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15);
v___x_2132_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2128_);
lean_ctor_set(v___x_2132_, 1, v_type_2084_);
lean_ctor_set(v___x_2132_, 2, v_a_2097_);
lean_ctor_set(v___x_2132_, 3, v___x_2111_);
lean_ctor_set(v___x_2132_, 4, v___x_2129_);
lean_ctor_set(v___x_2132_, 5, v___x_2129_);
lean_ctor_set(v___x_2132_, 6, v___x_2129_);
lean_ctor_set(v___x_2132_, 7, v___x_2129_);
lean_ctor_set(v___x_2132_, 8, v___x_2130_);
lean_ctor_set(v___x_2132_, 9, v___x_2131_);
lean_ctor_set(v___x_2132_, 10, v___x_2130_);
lean_inc(v_val_2121_);
v___x_2133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v_val_2121_);
lean_ctor_set(v___x_2133_, 2, v_val_2108_);
lean_ctor_set(v___x_2133_, 3, v___x_2129_);
lean_ctor_set(v___x_2133_, 4, v___x_2129_);
v___f_2134_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___lam__0), 2, 1);
lean_closure_set(v___f_2134_, 0, v___x_2133_);
v___x_2135_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2136_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2135_, v___f_2134_, v_a_2085_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v___x_2137_; 
lean_dec_ref_known(v___x_2136_, 1);
v___x_2137_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_setCommSemiringId___redArg(v_val_2121_, v___x_2128_, v_a_2085_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2147_; 
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; 
v_unused_2148_ = lean_ctor_get(v___x_2137_, 0);
lean_dec(v_unused_2148_);
v___x_2139_ = v___x_2137_;
v_isShared_2140_ = v_isSharedCheck_2147_;
goto v_resetjp_2138_;
}
else
{
lean_dec(v___x_2137_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2147_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2128_);
v___x_2142_ = v___x_2123_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2128_);
v___x_2142_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2144_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2142_);
v___x_2144_ = v___x_2139_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
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
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_del_object(v___x_2123_);
v_a_2149_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2137_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2137_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_del_object(v___x_2123_);
lean_dec(v_val_2121_);
v_a_2157_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2136_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2136_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_del_object(v___x_2123_);
lean_dec(v_val_2121_);
lean_dec_ref(v___x_2111_);
lean_dec(v_val_2108_);
lean_dec(v_a_2097_);
lean_dec_ref(v_type_2084_);
v_a_2165_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2125_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2125_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_dec(v_a_2120_);
lean_dec_ref(v___x_2111_);
lean_dec(v_val_2108_);
lean_dec(v_a_2097_);
lean_dec_ref(v_type_2084_);
v___x_2174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__3);
v___x_2175_ = l_Lean_indentExpr(v_a_2118_);
v___x_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v___x_2176_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
return v___x_2177_;
}
}
else
{
lean_dec(v_a_2118_);
lean_dec_ref(v___x_2111_);
lean_dec(v_val_2108_);
lean_dec(v_a_2097_);
lean_dec_ref(v_type_2084_);
return v___x_2119_;
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec_ref(v___x_2111_);
lean_dec(v_val_2108_);
lean_dec(v_a_2097_);
lean_dec_ref(v_type_2084_);
v_a_2178_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2117_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2117_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec_ref(v___x_2111_);
lean_dec(v_val_2108_);
lean_dec(v_a_2097_);
lean_dec_ref(v_type_2084_);
v_a_2186_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2115_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2115_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
lean_dec(v_a_2104_);
lean_dec_ref_known(v___x_2100_, 2);
lean_dec(v_a_2097_);
lean_dec_ref(v_type_2084_);
v___x_2194_ = lean_box(0);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2194_);
v___x_2196_ = v___x_2106_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref_known(v___x_2100_, 2);
lean_dec(v_a_2097_);
lean_dec_ref(v_type_2084_);
v_a_2199_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2103_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2103_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec_ref(v_type_2084_);
v_a_2207_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2096_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2096_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___boxed(lean_object* v_type_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(lean_object* v_00_u03b1_2228_, lean_object* v_msg_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___redArg(v_msg_2229_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0___boxed(lean_object* v_00_u03b1_2242_, lean_object* v_msg_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f_spec__0(v_00_u03b1_2242_, v_msg_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec(v___y_2244_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0(lean_object* v_type_2256_, lean_object* v_a_2257_, lean_object* v_s_2258_){
_start:
{
lean_object* v_rings_2259_; lean_object* v_typeIdOf_2260_; lean_object* v_exprToRingId_2261_; lean_object* v_semirings_2262_; lean_object* v_stypeIdOf_2263_; lean_object* v_exprToSemiringId_2264_; lean_object* v_ncRings_2265_; lean_object* v_exprToNCRingId_2266_; lean_object* v_nctypeIdOf_2267_; lean_object* v_ncSemirings_2268_; lean_object* v_exprToNCSemiringId_2269_; lean_object* v_ncstypeIdOf_2270_; lean_object* v_steps_2271_; uint8_t v_reportedMaxDegreeIssue_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2280_; 
v_rings_2259_ = lean_ctor_get(v_s_2258_, 0);
v_typeIdOf_2260_ = lean_ctor_get(v_s_2258_, 1);
v_exprToRingId_2261_ = lean_ctor_get(v_s_2258_, 2);
v_semirings_2262_ = lean_ctor_get(v_s_2258_, 3);
v_stypeIdOf_2263_ = lean_ctor_get(v_s_2258_, 4);
v_exprToSemiringId_2264_ = lean_ctor_get(v_s_2258_, 5);
v_ncRings_2265_ = lean_ctor_get(v_s_2258_, 6);
v_exprToNCRingId_2266_ = lean_ctor_get(v_s_2258_, 7);
v_nctypeIdOf_2267_ = lean_ctor_get(v_s_2258_, 8);
v_ncSemirings_2268_ = lean_ctor_get(v_s_2258_, 9);
v_exprToNCSemiringId_2269_ = lean_ctor_get(v_s_2258_, 10);
v_ncstypeIdOf_2270_ = lean_ctor_get(v_s_2258_, 11);
v_steps_2271_ = lean_ctor_get(v_s_2258_, 12);
v_reportedMaxDegreeIssue_2272_ = lean_ctor_get_uint8(v_s_2258_, sizeof(void*)*13);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_s_2258_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2274_ = v_s_2258_;
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_steps_2271_);
lean_inc(v_ncstypeIdOf_2270_);
lean_inc(v_exprToNCSemiringId_2269_);
lean_inc(v_ncSemirings_2268_);
lean_inc(v_nctypeIdOf_2267_);
lean_inc(v_exprToNCRingId_2266_);
lean_inc(v_ncRings_2265_);
lean_inc(v_exprToSemiringId_2264_);
lean_inc(v_stypeIdOf_2263_);
lean_inc(v_semirings_2262_);
lean_inc(v_exprToRingId_2261_);
lean_inc(v_typeIdOf_2260_);
lean_inc(v_rings_2259_);
lean_dec(v_s_2258_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2276_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_stypeIdOf_2263_, v_type_2256_, v_a_2257_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v___x_2276_);
v___x_2278_ = v___x_2274_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_rings_2259_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_typeIdOf_2260_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_exprToRingId_2261_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v_semirings_2262_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2279_, 5, v_exprToSemiringId_2264_);
lean_ctor_set(v_reuseFailAlloc_2279_, 6, v_ncRings_2265_);
lean_ctor_set(v_reuseFailAlloc_2279_, 7, v_exprToNCRingId_2266_);
lean_ctor_set(v_reuseFailAlloc_2279_, 8, v_nctypeIdOf_2267_);
lean_ctor_set(v_reuseFailAlloc_2279_, 9, v_ncSemirings_2268_);
lean_ctor_set(v_reuseFailAlloc_2279_, 10, v_exprToNCSemiringId_2269_);
lean_ctor_set(v_reuseFailAlloc_2279_, 11, v_ncstypeIdOf_2270_);
lean_ctor_set(v_reuseFailAlloc_2279_, 12, v_steps_2271_);
lean_ctor_set_uint8(v_reuseFailAlloc_2279_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2272_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object* v_type_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2282_, v_a_2290_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2325_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2325_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2325_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v_stypeIdOf_2298_; lean_object* v___x_2299_; 
v_stypeIdOf_2298_ = lean_ctor_get(v_a_2294_, 4);
lean_inc_ref(v_stypeIdOf_2298_);
lean_dec(v_a_2294_);
v___x_2299_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_stypeIdOf_2298_, v_type_2281_);
lean_dec_ref(v_stypeIdOf_2298_);
if (lean_obj_tag(v___x_2299_) == 1)
{
lean_object* v_val_2300_; lean_object* v___x_2302_; 
lean_dec_ref(v_type_2281_);
v_val_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_val_2300_);
lean_dec_ref_known(v___x_2299_, 1);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_val_2300_);
v___x_2302_ = v___x_2296_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_val_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
else
{
lean_object* v___x_2304_; 
lean_dec(v___x_2299_);
lean_del_object(v___x_2296_);
lean_inc_ref(v_type_2281_);
v___x_2304_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f(v_type_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___f_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc_n(v_a_2305_, 2);
lean_dec_ref_known(v___x_2304_, 1);
v___f_2306_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2306_, 0, v_type_2281_);
lean_closure_set(v___f_2306_, 1, v_a_2305_);
v___x_2307_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2308_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2307_, v___f_2306_, v_a_2282_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; 
v_unused_2316_ = lean_ctor_get(v___x_2308_, 0);
lean_dec(v_unused_2316_);
v___x_2310_ = v___x_2308_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_dec(v___x_2308_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v_a_2305_);
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2305_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v_a_2305_);
v_a_2317_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2308_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2308_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
else
{
lean_dec_ref(v_type_2281_);
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v_type_2281_);
v_a_2326_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2293_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2293_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___boxed(lean_object* v_type_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_type_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec(v_a_2336_);
lean_dec(v_a_2335_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0(lean_object* v___x_2347_, lean_object* v_s_2348_){
_start:
{
lean_object* v_rings_2349_; lean_object* v_typeIdOf_2350_; lean_object* v_exprToRingId_2351_; lean_object* v_semirings_2352_; lean_object* v_stypeIdOf_2353_; lean_object* v_exprToSemiringId_2354_; lean_object* v_ncRings_2355_; lean_object* v_exprToNCRingId_2356_; lean_object* v_nctypeIdOf_2357_; lean_object* v_ncSemirings_2358_; lean_object* v_exprToNCSemiringId_2359_; lean_object* v_ncstypeIdOf_2360_; lean_object* v_steps_2361_; uint8_t v_reportedMaxDegreeIssue_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2370_; 
v_rings_2349_ = lean_ctor_get(v_s_2348_, 0);
v_typeIdOf_2350_ = lean_ctor_get(v_s_2348_, 1);
v_exprToRingId_2351_ = lean_ctor_get(v_s_2348_, 2);
v_semirings_2352_ = lean_ctor_get(v_s_2348_, 3);
v_stypeIdOf_2353_ = lean_ctor_get(v_s_2348_, 4);
v_exprToSemiringId_2354_ = lean_ctor_get(v_s_2348_, 5);
v_ncRings_2355_ = lean_ctor_get(v_s_2348_, 6);
v_exprToNCRingId_2356_ = lean_ctor_get(v_s_2348_, 7);
v_nctypeIdOf_2357_ = lean_ctor_get(v_s_2348_, 8);
v_ncSemirings_2358_ = lean_ctor_get(v_s_2348_, 9);
v_exprToNCSemiringId_2359_ = lean_ctor_get(v_s_2348_, 10);
v_ncstypeIdOf_2360_ = lean_ctor_get(v_s_2348_, 11);
v_steps_2361_ = lean_ctor_get(v_s_2348_, 12);
v_reportedMaxDegreeIssue_2362_ = lean_ctor_get_uint8(v_s_2348_, sizeof(void*)*13);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_s_2348_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2364_ = v_s_2348_;
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_steps_2361_);
lean_inc(v_ncstypeIdOf_2360_);
lean_inc(v_exprToNCSemiringId_2359_);
lean_inc(v_ncSemirings_2358_);
lean_inc(v_nctypeIdOf_2357_);
lean_inc(v_exprToNCRingId_2356_);
lean_inc(v_ncRings_2355_);
lean_inc(v_exprToSemiringId_2354_);
lean_inc(v_stypeIdOf_2353_);
lean_inc(v_semirings_2352_);
lean_inc(v_exprToRingId_2351_);
lean_inc(v_typeIdOf_2350_);
lean_inc(v_rings_2349_);
lean_dec(v_s_2348_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2366_ = lean_array_push(v_ncSemirings_2358_, v___x_2347_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 9, v___x_2366_);
v___x_2368_ = v___x_2364_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_rings_2349_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_typeIdOf_2350_);
lean_ctor_set(v_reuseFailAlloc_2369_, 2, v_exprToRingId_2351_);
lean_ctor_set(v_reuseFailAlloc_2369_, 3, v_semirings_2352_);
lean_ctor_set(v_reuseFailAlloc_2369_, 4, v_stypeIdOf_2353_);
lean_ctor_set(v_reuseFailAlloc_2369_, 5, v_exprToSemiringId_2354_);
lean_ctor_set(v_reuseFailAlloc_2369_, 6, v_ncRings_2355_);
lean_ctor_set(v_reuseFailAlloc_2369_, 7, v_exprToNCRingId_2356_);
lean_ctor_set(v_reuseFailAlloc_2369_, 8, v_nctypeIdOf_2357_);
lean_ctor_set(v_reuseFailAlloc_2369_, 9, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2369_, 10, v_exprToNCSemiringId_2359_);
lean_ctor_set(v_reuseFailAlloc_2369_, 11, v_ncstypeIdOf_2360_);
lean_ctor_set(v_reuseFailAlloc_2369_, 12, v_steps_2361_);
lean_ctor_set_uint8(v_reuseFailAlloc_2369_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2362_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(lean_object* v_type_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2379_; 
lean_inc_ref(v_type_2371_);
v___x_2379_ = l_Lean_Meta_getDecLevel(v_type_2371_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc_n(v_a_2380_, 2);
lean_dec_ref_known(v___x_2379_, 1);
v___x_2381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goQ_x3f___closed__7));
v___x_2382_ = lean_box(0);
v___x_2383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2383_, 0, v_a_2380_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = l_Lean_mkConst(v___x_2381_, v___x_2383_);
lean_inc_ref(v_type_2371_);
v___x_2385_ = l_Lean_Expr_app___override(v___x_2384_, v_type_2371_);
v___x_2386_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2385_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2440_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2440_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2440_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
if (lean_obj_tag(v_a_2387_) == 1)
{
lean_object* v_val_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2435_; 
lean_del_object(v___x_2389_);
v_val_2391_ = lean_ctor_get(v_a_2387_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_a_2387_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2393_ = v_a_2387_;
v_isShared_2394_ = v_isSharedCheck_2435_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_val_2391_);
lean_dec(v_a_2387_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2435_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2372_, v_a_2376_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v_ncSemirings_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___f_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
v_ncSemirings_2397_ = lean_ctor_get(v_a_2396_, 9);
lean_inc_ref(v_ncSemirings_2397_);
lean_dec(v_a_2396_);
v___x_2398_ = lean_array_get_size(v_ncSemirings_2397_);
lean_dec_ref(v_ncSemirings_2397_);
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f_go_x3f___closed__1);
v___x_2401_ = lean_unsigned_to_nat(32u);
v___x_2402_ = lean_mk_empty_array_with_capacity(v___x_2401_);
lean_dec_ref(v___x_2402_);
v___x_2403_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_goCore_x3f___closed__15);
v___x_2404_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2398_);
lean_ctor_set(v___x_2404_, 1, v_type_2371_);
lean_ctor_set(v___x_2404_, 2, v_a_2380_);
lean_ctor_set(v___x_2404_, 3, v_val_2391_);
lean_ctor_set(v___x_2404_, 4, v___x_2399_);
lean_ctor_set(v___x_2404_, 5, v___x_2399_);
lean_ctor_set(v___x_2404_, 6, v___x_2399_);
lean_ctor_set(v___x_2404_, 7, v___x_2399_);
lean_ctor_set(v___x_2404_, 8, v___x_2400_);
lean_ctor_set(v___x_2404_, 9, v___x_2403_);
lean_ctor_set(v___x_2404_, 10, v___x_2400_);
v___f_2405_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2405_, 0, v___x_2404_);
v___x_2406_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2407_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2406_, v___f_2405_, v_a_2372_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2417_; 
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; 
v_unused_2418_ = lean_ctor_get(v___x_2407_, 0);
lean_dec(v_unused_2418_);
v___x_2409_ = v___x_2407_;
v_isShared_2410_ = v_isSharedCheck_2417_;
goto v_resetjp_2408_;
}
else
{
lean_dec(v___x_2407_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2417_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2398_);
v___x_2412_ = v___x_2393_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2398_);
v___x_2412_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2414_; 
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v___x_2412_);
v___x_2414_ = v___x_2409_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_del_object(v___x_2393_);
v_a_2419_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2407_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2407_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_del_object(v___x_2393_);
lean_dec(v_val_2391_);
lean_dec(v_a_2380_);
lean_dec_ref(v_type_2371_);
v_a_2427_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2395_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2395_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
else
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
lean_dec(v_a_2387_);
lean_dec(v_a_2380_);
lean_dec_ref(v_type_2371_);
v___x_2436_ = lean_box(0);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2436_);
v___x_2438_ = v___x_2389_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec(v_a_2380_);
lean_dec_ref(v_type_2371_);
v_a_2441_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2386_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2386_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec_ref(v_type_2371_);
v_a_2449_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2379_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2379_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg___boxed(lean_object* v_type_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec(v_a_2458_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(lean_object* v_type_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_2466_, v_a_2467_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___boxed(lean_object* v_type_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f(v_type_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec(v_a_2480_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0(lean_object* v_type_2492_, lean_object* v_a_2493_, lean_object* v_s_2494_){
_start:
{
lean_object* v_rings_2495_; lean_object* v_typeIdOf_2496_; lean_object* v_exprToRingId_2497_; lean_object* v_semirings_2498_; lean_object* v_stypeIdOf_2499_; lean_object* v_exprToSemiringId_2500_; lean_object* v_ncRings_2501_; lean_object* v_exprToNCRingId_2502_; lean_object* v_nctypeIdOf_2503_; lean_object* v_ncSemirings_2504_; lean_object* v_exprToNCSemiringId_2505_; lean_object* v_ncstypeIdOf_2506_; lean_object* v_steps_2507_; uint8_t v_reportedMaxDegreeIssue_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2516_; 
v_rings_2495_ = lean_ctor_get(v_s_2494_, 0);
v_typeIdOf_2496_ = lean_ctor_get(v_s_2494_, 1);
v_exprToRingId_2497_ = lean_ctor_get(v_s_2494_, 2);
v_semirings_2498_ = lean_ctor_get(v_s_2494_, 3);
v_stypeIdOf_2499_ = lean_ctor_get(v_s_2494_, 4);
v_exprToSemiringId_2500_ = lean_ctor_get(v_s_2494_, 5);
v_ncRings_2501_ = lean_ctor_get(v_s_2494_, 6);
v_exprToNCRingId_2502_ = lean_ctor_get(v_s_2494_, 7);
v_nctypeIdOf_2503_ = lean_ctor_get(v_s_2494_, 8);
v_ncSemirings_2504_ = lean_ctor_get(v_s_2494_, 9);
v_exprToNCSemiringId_2505_ = lean_ctor_get(v_s_2494_, 10);
v_ncstypeIdOf_2506_ = lean_ctor_get(v_s_2494_, 11);
v_steps_2507_ = lean_ctor_get(v_s_2494_, 12);
v_reportedMaxDegreeIssue_2508_ = lean_ctor_get_uint8(v_s_2494_, sizeof(void*)*13);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_s_2494_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2510_ = v_s_2494_;
v_isShared_2511_ = v_isSharedCheck_2516_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_steps_2507_);
lean_inc(v_ncstypeIdOf_2506_);
lean_inc(v_exprToNCSemiringId_2505_);
lean_inc(v_ncSemirings_2504_);
lean_inc(v_nctypeIdOf_2503_);
lean_inc(v_exprToNCRingId_2502_);
lean_inc(v_ncRings_2501_);
lean_inc(v_exprToSemiringId_2500_);
lean_inc(v_stypeIdOf_2499_);
lean_inc(v_semirings_2498_);
lean_inc(v_exprToRingId_2497_);
lean_inc(v_typeIdOf_2496_);
lean_inc(v_rings_2495_);
lean_dec(v_s_2494_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2516_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2512_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__1___redArg(v_ncstypeIdOf_2506_, v_type_2492_, v_a_2493_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 11, v___x_2512_);
v___x_2514_ = v___x_2510_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_rings_2495_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_typeIdOf_2496_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_exprToRingId_2497_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_semirings_2498_);
lean_ctor_set(v_reuseFailAlloc_2515_, 4, v_stypeIdOf_2499_);
lean_ctor_set(v_reuseFailAlloc_2515_, 5, v_exprToSemiringId_2500_);
lean_ctor_set(v_reuseFailAlloc_2515_, 6, v_ncRings_2501_);
lean_ctor_set(v_reuseFailAlloc_2515_, 7, v_exprToNCRingId_2502_);
lean_ctor_set(v_reuseFailAlloc_2515_, 8, v_nctypeIdOf_2503_);
lean_ctor_set(v_reuseFailAlloc_2515_, 9, v_ncSemirings_2504_);
lean_ctor_set(v_reuseFailAlloc_2515_, 10, v_exprToNCSemiringId_2505_);
lean_ctor_set(v_reuseFailAlloc_2515_, 11, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2515_, 12, v_steps_2507_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2508_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object* v_type_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2518_, v_a_2522_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2557_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2557_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2557_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v_ncstypeIdOf_2530_; lean_object* v___x_2531_; 
v_ncstypeIdOf_2530_ = lean_ctor_get(v_a_2526_, 11);
lean_inc_ref(v_ncstypeIdOf_2530_);
lean_dec(v_a_2526_);
v___x_2531_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f_spec__0___redArg(v_ncstypeIdOf_2530_, v_type_2517_);
lean_dec_ref(v_ncstypeIdOf_2530_);
if (lean_obj_tag(v___x_2531_) == 1)
{
lean_object* v_val_2532_; lean_object* v___x_2534_; 
lean_dec_ref(v_type_2517_);
v_val_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_val_2532_);
lean_dec_ref_known(v___x_2531_, 1);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v_val_2532_);
v___x_2534_ = v___x_2528_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_val_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
else
{
lean_object* v___x_2536_; 
lean_dec(v___x_2531_);
lean_del_object(v___x_2528_);
lean_inc_ref(v_type_2517_);
v___x_2536_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId_0__Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f_go_x3f___redArg(v_type_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___f_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc_n(v_a_2537_, 2);
lean_dec_ref_known(v___x_2536_, 1);
v___f_2538_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2538_, 0, v_type_2517_);
lean_closure_set(v___f_2538_, 1, v_a_2537_);
v___x_2539_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2540_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2539_, v___f_2538_, v_a_2518_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; 
v_unused_2548_ = lean_ctor_get(v___x_2540_, 0);
lean_dec(v_unused_2548_);
v___x_2542_ = v___x_2540_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_dec(v___x_2540_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v_a_2537_);
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2537_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_a_2537_);
v_a_2549_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2540_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2540_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
else
{
lean_dec_ref(v_type_2517_);
return v___x_2536_;
}
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec_ref(v_type_2517_);
v_a_2558_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2525_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2525_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg___boxed(lean_object* v_type_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_a_2568_);
lean_dec(v_a_2567_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(lean_object* v_type_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_2575_, v_a_2576_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___boxed(lean_object* v_type_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f(v_type_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec(v_a_2589_);
return v_res_2600_;
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
