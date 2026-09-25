// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Classify
// Imports: public import Lean.Meta.Sym.Arith.Insts import Lean.Meta.Sym.SynthInstance import Lean.Meta.Sym.Canon import Lean.Meta.DecLevel import Init.Grind.Ring
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Arith_arithExt;
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default;
extern lean_object* l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
extern lean_object* l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default;
extern lean_object* l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "OfCommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ofCommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(219, 56, 247, 159, 186, 83, 86, 251)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(36, 61, 219, 203, 190, 113, 236, 200)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toCommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(134, 95, 181, 253, 18, 104, 213, 131)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NatModule"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 171, 186, 15, 174, 251, 179)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "toNatModule"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(156, 107, 255, 119, 73, 35, 26, 237)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__23_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__29_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__31 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__31_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__33 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__33_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__35 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__35_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__37 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__37_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__37_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__39 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__39_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__39_value),LEAN_SCALAR_PTR_LITERAL(8, 241, 181, 204, 215, 46, 40, 252)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__41 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__41_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__41_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__43 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__43_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__43_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__45 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__45_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__48 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__48_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__48_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__50 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__50_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__50_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__52 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__52_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__52_value),LEAN_SCALAR_PTR_LITERAL(84, 97, 73, 37, 143, 22, 233, 204)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__54 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__54_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__54_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__56 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__56_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__56_value),LEAN_SCALAR_PTR_LITERAL(1, 189, 244, 99, 68, 50, 19, 202)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__58 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__58_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__59 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__59_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__58_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__59_value),LEAN_SCALAR_PTR_LITERAL(17, 56, 209, 254, 185, 203, 153, 57)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "PowIdentity available: false"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "NoNatZeroDivisors available: "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "instNoNatZeroDivisorsQOfAddRightCancel"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__69 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__69_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__69_value),LEAN_SCALAR_PTR_LITERAL(221, 130, 167, 21, 145, 237, 132, 218)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__71 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__71_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__71_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__73 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__73_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__73_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "instIsCharPQOfAddRightCancel"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__75 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__75_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__75_value),LEAN_SCALAR_PTR_LITERAL(194, 21, 126, 159, 192, 171, 59, 180)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "new ring: "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "PowIdentity available: "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 238, 182, 216, 107, 45, 243, 168)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(134, 3, 13, 60, 96, 160, 201, 59)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "unexpected failure initializing ring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OrderedRing"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 123, 155, 51, 122, 17, 247, 247)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0(lean_object* v___x_1_, lean_object* v_s_2_){
_start:
{
lean_object* v_exp_3_; lean_object* v_rings_4_; lean_object* v_semirings_5_; lean_object* v_ncRings_6_; lean_object* v_ncSemirings_7_; lean_object* v_typeClassify_8_; lean_object* v_orders_9_; lean_object* v_typeOrderClassify_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_18_; 
v_exp_3_ = lean_ctor_get(v_s_2_, 0);
v_rings_4_ = lean_ctor_get(v_s_2_, 1);
v_semirings_5_ = lean_ctor_get(v_s_2_, 2);
v_ncRings_6_ = lean_ctor_get(v_s_2_, 3);
v_ncSemirings_7_ = lean_ctor_get(v_s_2_, 4);
v_typeClassify_8_ = lean_ctor_get(v_s_2_, 5);
v_orders_9_ = lean_ctor_get(v_s_2_, 6);
v_typeOrderClassify_10_ = lean_ctor_get(v_s_2_, 7);
v_isSharedCheck_18_ = !lean_is_exclusive(v_s_2_);
if (v_isSharedCheck_18_ == 0)
{
v___x_12_ = v_s_2_;
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_typeOrderClassify_10_);
lean_inc(v_orders_9_);
lean_inc(v_typeClassify_8_);
lean_inc(v_ncSemirings_7_);
lean_inc(v_ncRings_6_);
lean_inc(v_semirings_5_);
lean_inc(v_rings_4_);
lean_inc(v_exp_3_);
lean_dec(v_s_2_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_16_; 
v___x_14_ = lean_array_push(v_rings_4_, v___x_1_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 1, v___x_14_);
v___x_16_ = v___x_12_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_exp_3_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_17_, 2, v_semirings_5_);
lean_ctor_set(v_reuseFailAlloc_17_, 3, v_ncRings_6_);
lean_ctor_set(v_reuseFailAlloc_17_, 4, v_ncSemirings_7_);
lean_ctor_set(v_reuseFailAlloc_17_, 5, v_typeClassify_8_);
lean_ctor_set(v_reuseFailAlloc_17_, 6, v_orders_9_);
lean_ctor_set(v_reuseFailAlloc_17_, 7, v_typeOrderClassify_10_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(lean_object* v___x_22_, lean_object* v_____do__lift_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_toCold_31_; lean_object* v_options_32_; uint8_t v_hasTrace_33_; 
v_toCold_31_ = lean_ctor_get(v___y_28_, 0);
v_options_32_ = lean_ctor_get(v_toCold_31_, 2);
v_hasTrace_33_ = lean_ctor_get_uint8(v_options_32_, sizeof(void*)*1);
if (v_hasTrace_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v___x_22_);
v___x_34_ = lean_box(v_hasTrace_33_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_36_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1));
v___x_37_ = l_Lean_Name_append(v___x_36_, v___x_22_);
v___x_38_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_23_, v_options_32_, v___x_37_);
lean_dec(v___x_37_);
v___x_39_ = lean_box(v___x_38_);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___boxed(lean_object* v___x_41_, lean_object* v_____do__lift_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_41_, v_____do__lift_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec_ref(v_____do__lift_42_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(lean_object* v_msgData_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; lean_object* v_env_58_; lean_object* v___x_59_; lean_object* v_toCold_60_; lean_object* v_mctx_61_; lean_object* v_lctx_62_; lean_object* v_options_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_57_ = lean_st_ref_get(v___y_55_);
v_env_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc_ref(v_env_58_);
lean_dec(v___x_57_);
v___x_59_ = lean_st_ref_get(v___y_53_);
v_toCold_60_ = lean_ctor_get(v___y_54_, 0);
v_mctx_61_ = lean_ctor_get(v___x_59_, 0);
lean_inc_ref(v_mctx_61_);
lean_dec(v___x_59_);
v_lctx_62_ = lean_ctor_get(v___y_52_, 2);
v_options_63_ = lean_ctor_get(v_toCold_60_, 2);
lean_inc_ref(v_options_63_);
lean_inc_ref(v_lctx_62_);
v___x_64_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_64_, 0, v_env_58_);
lean_ctor_set(v___x_64_, 1, v_mctx_61_);
lean_ctor_set(v___x_64_, 2, v_lctx_62_);
lean_ctor_set(v___x_64_, 3, v_options_63_);
v___x_65_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v_msgData_51_);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(v_msgData_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
return v_res_73_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_74_; double v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = lean_float_of_nat(v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(lean_object* v_cls_79_, lean_object* v_msg_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_ref_86_; lean_object* v___x_87_; lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_133_; 
v_ref_86_ = lean_ctor_get(v___y_83_, 2);
v___x_87_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(v_msg_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_133_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_133_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_133_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v_traceState_93_; lean_object* v_env_94_; lean_object* v_nextMacroScope_95_; lean_object* v_ngen_96_; lean_object* v_auxDeclNGen_97_; lean_object* v_cache_98_; lean_object* v_recordedDeps_99_; lean_object* v_messages_100_; lean_object* v_infoState_101_; lean_object* v_snapshotTasks_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_132_; 
v___x_92_ = lean_st_ref_take(v___y_84_);
v_traceState_93_ = lean_ctor_get(v___x_92_, 4);
v_env_94_ = lean_ctor_get(v___x_92_, 0);
v_nextMacroScope_95_ = lean_ctor_get(v___x_92_, 1);
v_ngen_96_ = lean_ctor_get(v___x_92_, 2);
v_auxDeclNGen_97_ = lean_ctor_get(v___x_92_, 3);
v_cache_98_ = lean_ctor_get(v___x_92_, 5);
v_recordedDeps_99_ = lean_ctor_get(v___x_92_, 6);
v_messages_100_ = lean_ctor_get(v___x_92_, 7);
v_infoState_101_ = lean_ctor_get(v___x_92_, 8);
v_snapshotTasks_102_ = lean_ctor_get(v___x_92_, 9);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_132_ == 0)
{
v___x_104_ = v___x_92_;
v_isShared_105_ = v_isSharedCheck_132_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_snapshotTasks_102_);
lean_inc(v_infoState_101_);
lean_inc(v_messages_100_);
lean_inc(v_recordedDeps_99_);
lean_inc(v_cache_98_);
lean_inc(v_traceState_93_);
lean_inc(v_auxDeclNGen_97_);
lean_inc(v_ngen_96_);
lean_inc(v_nextMacroScope_95_);
lean_inc(v_env_94_);
lean_dec(v___x_92_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_132_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
uint64_t v_tid_106_; lean_object* v_traces_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_131_; 
v_tid_106_ = lean_ctor_get_uint64(v_traceState_93_, sizeof(void*)*1);
v_traces_107_ = lean_ctor_get(v_traceState_93_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v_traceState_93_);
if (v_isSharedCheck_131_ == 0)
{
v___x_109_ = v_traceState_93_;
v_isShared_110_ = v_isSharedCheck_131_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_traces_107_);
lean_dec(v_traceState_93_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_131_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; double v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_111_ = lean_box(0);
v___x_112_ = lean_box(0);
v___x_113_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0);
v___x_114_ = 0;
v___x_115_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1));
v___x_116_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_116_, 0, v_cls_79_);
lean_ctor_set(v___x_116_, 1, v___x_112_);
lean_ctor_set(v___x_116_, 2, v___x_115_);
lean_ctor_set_float(v___x_116_, sizeof(void*)*3, v___x_113_);
lean_ctor_set_float(v___x_116_, sizeof(void*)*3 + 8, v___x_113_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*3 + 16, v___x_114_);
v___x_117_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2));
v___x_118_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set(v___x_118_, 1, v_a_88_);
lean_ctor_set(v___x_118_, 2, v___x_117_);
lean_inc(v_ref_86_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_ref_86_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = l_Lean_PersistentArray_push___redArg(v_traces_107_, v___x_119_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_120_);
v___x_122_ = v___x_109_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_120_);
lean_ctor_set_uint64(v_reuseFailAlloc_130_, sizeof(void*)*1, v_tid_106_);
v___x_122_ = v_reuseFailAlloc_130_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_124_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 4, v___x_122_);
v___x_124_ = v___x_104_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_env_94_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_nextMacroScope_95_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v_ngen_96_);
lean_ctor_set(v_reuseFailAlloc_129_, 3, v_auxDeclNGen_97_);
lean_ctor_set(v_reuseFailAlloc_129_, 4, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_129_, 5, v_cache_98_);
lean_ctor_set(v_reuseFailAlloc_129_, 6, v_recordedDeps_99_);
lean_ctor_set(v_reuseFailAlloc_129_, 7, v_messages_100_);
lean_ctor_set(v_reuseFailAlloc_129_, 8, v_infoState_101_);
lean_ctor_set(v_reuseFailAlloc_129_, 9, v_snapshotTasks_102_);
v___x_124_ = v_reuseFailAlloc_129_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_st_ref_put(v___y_84_, v___x_124_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_111_);
v___x_127_ = v___x_90_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_111_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___boxed(lean_object* v_cls_134_, lean_object* v_msg_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v_cls_134_, v_msg_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = l_Lean_Level_ofNat(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1));
v___x_282_ = l_Lean_Name_append(v___x_281_, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62));
v___x_285_ = l_Lean_stringToMessageData(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64));
v___x_288_ = l_Lean_stringToMessageData(v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77));
v___x_316_ = l_Lean_stringToMessageData(v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(lean_object* v_type_317_, lean_object* v_base_318_, lean_object* v_semiringInst_319_, lean_object* v_commSemiringInst_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; 
lean_inc_ref(v_base_318_);
v___x_328_ = l_Lean_Meta_getDecLevel_x3f(v_base_318_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_773_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_773_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_773_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_773_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
if (lean_obj_tag(v_a_329_) == 1)
{
lean_object* v_val_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_768_; 
lean_del_object(v___x_331_);
v_val_333_ = lean_ctor_get(v_a_329_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v_a_329_);
if (v_isSharedCheck_768_ == 0)
{
v___x_335_ = v_a_329_;
v_isShared_336_ = v_isSharedCheck_768_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_val_333_);
lean_dec(v_a_329_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_768_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5));
v___x_338_ = lean_box(0);
lean_inc(v_val_333_);
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v_val_333_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
lean_inc_ref_n(v___x_339_, 5);
v___x_340_ = l_Lean_mkConst(v___x_337_, v___x_339_);
lean_inc_ref(v_base_318_);
v___x_341_ = l_Lean_mkAppB(v___x_340_, v_base_318_, v_commSemiringInst_320_);
v___x_342_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7));
v___x_343_ = l_Lean_mkConst(v___x_342_, v___x_339_);
lean_inc_ref_n(v___x_341_, 2);
lean_inc_ref_n(v_type_317_, 4);
v___x_344_ = l_Lean_mkAppB(v___x_343_, v_type_317_, v___x_341_);
v___x_345_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10));
v___x_346_ = l_Lean_mkConst(v___x_345_, v___x_339_);
lean_inc_ref(v___x_344_);
v___x_347_ = l_Lean_mkAppB(v___x_346_, v_type_317_, v___x_344_);
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12));
v___x_349_ = l_Lean_mkConst(v___x_348_, v___x_339_);
lean_inc_ref(v___x_347_);
v___x_350_ = l_Lean_mkAppB(v___x_349_, v_type_317_, v___x_347_);
v___x_393_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13));
v___x_394_ = l_Lean_mkConst(v___x_393_, v___x_339_);
v___x_395_ = l_Lean_Expr_app___override(v___x_394_, v_type_317_);
v___x_396_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_395_, v___x_341_, v_a_322_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec_ref_known(v___x_396_, 1);
v___x_397_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14));
lean_inc_ref(v___x_339_);
v___x_398_ = l_Lean_mkConst(v___x_397_, v___x_339_);
lean_inc_ref(v_type_317_);
v___x_399_ = l_Lean_Expr_app___override(v___x_398_, v_type_317_);
lean_inc_ref(v___x_344_);
v___x_400_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_399_, v___x_344_, v_a_322_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref_known(v___x_400_, 1);
v___x_401_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16));
lean_inc_ref(v___x_339_);
v___x_402_ = l_Lean_mkConst(v___x_401_, v___x_339_);
lean_inc_ref(v_type_317_);
v___x_403_ = l_Lean_Expr_app___override(v___x_402_, v_type_317_);
lean_inc_ref(v___x_347_);
v___x_404_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_403_, v___x_347_, v_a_322_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec_ref_known(v___x_404_, 1);
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18));
lean_inc_ref(v___x_339_);
v___x_406_ = l_Lean_mkConst(v___x_405_, v___x_339_);
lean_inc_ref(v_type_317_);
v___x_407_ = l_Lean_Expr_app___override(v___x_406_, v_type_317_);
lean_inc_ref(v___x_350_);
v___x_408_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_407_, v___x_350_, v_a_322_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref_known(v___x_408_, 1);
v___x_409_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20));
lean_inc_ref_n(v___x_339_, 2);
v___x_410_ = l_Lean_mkConst(v___x_409_, v___x_339_);
lean_inc_ref_n(v_type_317_, 2);
v___x_411_ = l_Lean_Expr_app___override(v___x_410_, v_type_317_);
v___x_412_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22));
v___x_413_ = l_Lean_mkConst(v___x_412_, v___x_339_);
lean_inc_ref(v___x_347_);
v___x_414_ = l_Lean_mkAppB(v___x_413_, v_type_317_, v___x_347_);
v___x_415_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_411_, v___x_414_, v_a_322_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec_ref_known(v___x_415_, 1);
v___x_416_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24));
lean_inc_ref_n(v___x_339_, 3);
lean_inc_n(v_val_333_, 2);
v___x_417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_417_, 0, v_val_333_);
lean_ctor_set(v___x_417_, 1, v___x_339_);
v___x_418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_418_, 0, v_val_333_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
lean_inc_ref(v___x_418_);
v___x_419_ = l_Lean_mkConst(v___x_416_, v___x_418_);
lean_inc_ref_n(v_type_317_, 5);
v___x_420_ = l_Lean_mkApp3(v___x_419_, v_type_317_, v_type_317_, v_type_317_);
v___x_421_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26));
v___x_422_ = l_Lean_mkConst(v___x_421_, v___x_339_);
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28));
v___x_424_ = l_Lean_mkConst(v___x_423_, v___x_339_);
lean_inc_ref(v___x_347_);
v___x_425_ = l_Lean_mkAppB(v___x_424_, v_type_317_, v___x_347_);
v___x_426_ = l_Lean_mkAppB(v___x_422_, v_type_317_, v___x_425_);
v___x_427_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_420_, v___x_426_, v_a_322_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec_ref_known(v___x_427_, 1);
v___x_428_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30));
lean_inc_ref(v___x_418_);
v___x_429_ = l_Lean_mkConst(v___x_428_, v___x_418_);
lean_inc_ref_n(v_type_317_, 5);
v___x_430_ = l_Lean_mkApp3(v___x_429_, v_type_317_, v_type_317_, v_type_317_);
v___x_431_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32));
lean_inc_ref_n(v___x_339_, 2);
v___x_432_ = l_Lean_mkConst(v___x_431_, v___x_339_);
v___x_433_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34));
v___x_434_ = l_Lean_mkConst(v___x_433_, v___x_339_);
lean_inc_ref(v___x_347_);
v___x_435_ = l_Lean_mkAppB(v___x_434_, v_type_317_, v___x_347_);
v___x_436_ = l_Lean_mkAppB(v___x_432_, v_type_317_, v___x_435_);
v___x_437_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_430_, v___x_436_, v_a_322_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec_ref_known(v___x_437_, 1);
v___x_438_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36));
v___x_439_ = l_Lean_mkConst(v___x_438_, v___x_418_);
lean_inc_ref_n(v_type_317_, 5);
v___x_440_ = l_Lean_mkApp3(v___x_439_, v_type_317_, v_type_317_, v_type_317_);
v___x_441_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38));
lean_inc_ref_n(v___x_339_, 2);
v___x_442_ = l_Lean_mkConst(v___x_441_, v___x_339_);
v___x_443_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40));
v___x_444_ = l_Lean_mkConst(v___x_443_, v___x_339_);
lean_inc_ref(v___x_344_);
v___x_445_ = l_Lean_mkAppB(v___x_444_, v_type_317_, v___x_344_);
v___x_446_ = l_Lean_mkAppB(v___x_442_, v_type_317_, v___x_445_);
v___x_447_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_440_, v___x_446_, v_a_322_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec_ref_known(v___x_447_, 1);
v___x_448_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42));
lean_inc_ref_n(v___x_339_, 2);
v___x_449_ = l_Lean_mkConst(v___x_448_, v___x_339_);
lean_inc_ref_n(v_type_317_, 2);
v___x_450_ = l_Lean_Expr_app___override(v___x_449_, v_type_317_);
v___x_451_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44));
v___x_452_ = l_Lean_mkConst(v___x_451_, v___x_339_);
lean_inc_ref(v___x_344_);
v___x_453_ = l_Lean_mkAppB(v___x_452_, v_type_317_, v___x_344_);
v___x_454_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_450_, v___x_453_, v_a_322_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec_ref_known(v___x_454_, 1);
v___x_455_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46));
v___x_456_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47);
lean_inc_ref_n(v___x_339_, 2);
v___x_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_339_);
lean_inc(v_val_333_);
v___x_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_458_, 0, v_val_333_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = l_Lean_mkConst(v___x_455_, v___x_458_);
v___x_460_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_317_, 3);
v___x_461_ = l_Lean_mkApp3(v___x_459_, v_type_317_, v___x_460_, v_type_317_);
v___x_462_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49));
v___x_463_ = l_Lean_mkConst(v___x_462_, v___x_339_);
lean_inc_ref(v___x_347_);
v___x_464_ = l_Lean_mkAppB(v___x_463_, v_type_317_, v___x_347_);
v___x_465_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_461_, v___x_464_, v_a_322_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec_ref_known(v___x_465_, 1);
v___x_466_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51));
lean_inc_ref_n(v___x_339_, 2);
v___x_467_ = l_Lean_mkConst(v___x_466_, v___x_339_);
lean_inc_ref_n(v_type_317_, 2);
v___x_468_ = l_Lean_Expr_app___override(v___x_467_, v_type_317_);
v___x_469_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53));
v___x_470_ = l_Lean_mkConst(v___x_469_, v___x_339_);
lean_inc_ref(v___x_347_);
v___x_471_ = l_Lean_mkAppB(v___x_470_, v_type_317_, v___x_347_);
v___x_472_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_468_, v___x_471_, v_a_322_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec_ref_known(v___x_472_, 1);
v___x_473_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55));
lean_inc_ref_n(v___x_339_, 2);
v___x_474_ = l_Lean_mkConst(v___x_473_, v___x_339_);
lean_inc_ref_n(v_type_317_, 2);
v___x_475_ = l_Lean_Expr_app___override(v___x_474_, v_type_317_);
v___x_476_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57));
v___x_477_ = l_Lean_mkConst(v___x_476_, v___x_339_);
lean_inc_ref(v___x_344_);
v___x_478_ = l_Lean_mkAppB(v___x_477_, v_type_317_, v___x_344_);
v___x_479_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_475_, v___x_478_, v_a_322_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_toCold_480_; lean_object* v_inheritedTraceOptions_481_; lean_object* v___x_482_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v_options_490_; lean_object* v_inheritedTraceOptions_491_; lean_object* v___y_492_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_532_; lean_object* v_noZeroDivInst_x3f_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v_val_550_; lean_object* v_charInst_x3f_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___x_657_; lean_object* v_a_658_; uint8_t v___x_659_; 
lean_dec_ref_known(v___x_479_, 1);
v_toCold_480_ = lean_ctor_get(v_a_325_, 0);
v_inheritedTraceOptions_481_ = lean_ctor_get(v_toCold_480_, 11);
v___x_482_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_657_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_482_, v_inheritedTraceOptions_481_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref(v___x_657_);
v___x_659_ = lean_unbox(v_a_658_);
lean_dec(v_a_658_);
if (v___x_659_ == 0)
{
v___y_589_ = v_a_321_;
v___y_590_ = v_a_322_;
v___y_591_ = v_a_323_;
v___y_592_ = v_a_324_;
v___y_593_ = v_a_325_;
v___y_594_ = v_a_326_;
goto v___jp_588_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_660_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78);
lean_inc_ref(v_type_317_);
v___x_661_ = l_Lean_MessageData_ofExpr(v_type_317_);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_482_, v___x_662_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_dec_ref_known(v___x_663_, 1);
v___y_589_ = v_a_321_;
v___y_590_ = v_a_322_;
v___y_591_ = v_a_323_;
v___y_592_ = v_a_324_;
v___y_593_ = v_a_325_;
v___y_594_ = v_a_326_;
goto v___jp_588_;
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
v___jp_483_:
{
uint8_t v_hasTrace_493_; 
v_hasTrace_493_ = lean_ctor_get_uint8(v_options_490_, sizeof(void*)*1);
if (v_hasTrace_493_ == 0)
{
v___y_352_ = v___y_484_;
v___y_353_ = v___y_485_;
v___y_354_ = v___y_486_;
v___y_355_ = v___y_489_;
goto v___jp_351_;
}
else
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61);
v___x_495_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_491_, v_options_490_, v___x_494_);
if (v___x_495_ == 0)
{
v___y_352_ = v___y_484_;
v___y_353_ = v___y_485_;
v___y_354_ = v___y_486_;
v___y_355_ = v___y_489_;
goto v___jp_351_;
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63);
v___x_497_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_482_, v___x_496_, v___y_487_, v___y_488_, v___y_489_, v___y_492_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_dec_ref_known(v___x_497_, 1);
v___y_352_ = v___y_484_;
v___y_353_ = v___y_485_;
v___y_354_ = v___y_486_;
v___y_355_ = v___y_489_;
goto v___jp_351_;
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_type_317_);
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
}
v___jp_506_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
lean_inc_ref(v___y_515_);
v___x_516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_516_, 0, v___y_515_);
v___x_517_ = l_Lean_MessageData_ofFormat(v___x_516_);
lean_inc_ref(v___y_514_);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___y_514_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_482_, v___x_518_, v___y_511_, v___y_507_, v___y_508_, v___y_510_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_toCold_520_; lean_object* v_options_521_; lean_object* v_inheritedTraceOptions_522_; 
lean_dec_ref_known(v___x_519_, 1);
v_toCold_520_ = lean_ctor_get(v___y_508_, 0);
v_options_521_ = lean_ctor_get(v_toCold_520_, 2);
v_inheritedTraceOptions_522_ = lean_ctor_get(v_toCold_520_, 11);
v___y_484_ = v___y_509_;
v___y_485_ = v___y_512_;
v___y_486_ = v___y_513_;
v___y_487_ = v___y_511_;
v___y_488_ = v___y_507_;
v___y_489_ = v___y_508_;
v_options_490_ = v_options_521_;
v_inheritedTraceOptions_491_ = v_inheritedTraceOptions_522_;
v___y_492_ = v___y_510_;
goto v___jp_483_;
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v___y_512_);
lean_dec(v___y_509_);
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_type_317_);
v_a_523_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_519_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_519_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
v___jp_531_:
{
lean_object* v_toCold_540_; lean_object* v_options_541_; lean_object* v_inheritedTraceOptions_542_; lean_object* v___x_543_; lean_object* v_a_544_; uint8_t v___x_545_; 
v_toCold_540_ = lean_ctor_get(v___y_538_, 0);
v_options_541_ = lean_ctor_get(v_toCold_540_, 2);
v_inheritedTraceOptions_542_ = lean_ctor_get(v_toCold_540_, 11);
v___x_543_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_482_, v_inheritedTraceOptions_542_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref(v___x_543_);
v___x_545_ = lean_unbox(v_a_544_);
lean_dec(v_a_544_);
if (v___x_545_ == 0)
{
v___y_484_ = v_noZeroDivInst_x3f_533_;
v___y_485_ = v___y_532_;
v___y_486_ = v___y_535_;
v___y_487_ = v___y_536_;
v___y_488_ = v___y_537_;
v___y_489_ = v___y_538_;
v_options_490_ = v_options_541_;
v_inheritedTraceOptions_491_ = v_inheritedTraceOptions_542_;
v___y_492_ = v___y_539_;
goto v___jp_483_;
}
else
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65);
if (lean_obj_tag(v_noZeroDivInst_x3f_533_) == 0)
{
lean_object* v___x_547_; 
v___x_547_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66));
v___y_507_ = v___y_537_;
v___y_508_ = v___y_538_;
v___y_509_ = v_noZeroDivInst_x3f_533_;
v___y_510_ = v___y_539_;
v___y_511_ = v___y_536_;
v___y_512_ = v___y_532_;
v___y_513_ = v___y_535_;
v___y_514_ = v___x_546_;
v___y_515_ = v___x_547_;
goto v___jp_506_;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67));
v___y_507_ = v___y_537_;
v___y_508_ = v___y_538_;
v___y_509_ = v_noZeroDivInst_x3f_533_;
v___y_510_ = v___y_539_;
v___y_511_ = v___y_536_;
v___y_512_ = v___y_532_;
v___y_513_ = v___y_535_;
v___y_514_ = v___x_546_;
v___y_515_ = v___x_548_;
goto v___jp_506_;
}
}
}
v___jp_549_:
{
lean_object* v___x_558_; 
lean_inc_ref(v_base_318_);
lean_inc(v_val_333_);
v___x_558_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_val_333_, v_base_318_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
if (lean_obj_tag(v_a_559_) == 1)
{
lean_object* v_val_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_570_; 
v_val_560_ = lean_ctor_get(v_a_559_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v_a_559_);
if (v_isSharedCheck_570_ == 0)
{
v___x_562_ = v_a_559_;
v_isShared_563_ = v_isSharedCheck_570_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_val_560_);
lean_dec(v_a_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_570_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_564_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70));
v___x_565_ = l_Lean_mkConst(v___x_564_, v___x_339_);
v___x_566_ = l_Lean_mkApp4(v___x_565_, v_base_318_, v_semiringInst_319_, v_val_550_, v_val_560_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_566_);
v___x_568_ = v___x_562_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
v___y_532_ = v_charInst_x3f_551_;
v_noZeroDivInst_x3f_533_ = v___x_568_;
v___y_534_ = v___y_552_;
v___y_535_ = v___y_553_;
v___y_536_ = v___y_554_;
v___y_537_ = v___y_555_;
v___y_538_ = v___y_556_;
v___y_539_ = v___y_557_;
goto v___jp_531_;
}
}
}
else
{
lean_object* v___x_571_; 
lean_dec(v_a_559_);
lean_dec_ref(v_val_550_);
lean_dec_ref_known(v___x_339_, 2);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
v___x_571_ = lean_box(0);
v___y_532_ = v_charInst_x3f_551_;
v_noZeroDivInst_x3f_533_ = v___x_571_;
v___y_534_ = v___y_552_;
v___y_535_ = v___y_553_;
v___y_536_ = v___y_554_;
v___y_537_ = v___y_555_;
v___y_538_ = v___y_556_;
v___y_539_ = v___y_557_;
goto v___jp_531_;
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_dec(v_charInst_x3f_551_);
lean_dec_ref(v_val_550_);
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_572_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_558_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_558_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
v___jp_580_:
{
lean_object* v___x_587_; 
v___x_587_ = lean_box(0);
v___y_532_ = v___x_587_;
v_noZeroDivInst_x3f_533_ = v___x_587_;
v___y_534_ = v___y_581_;
v___y_535_ = v___y_582_;
v___y_536_ = v___y_583_;
v___y_537_ = v___y_584_;
v___y_538_ = v___y_585_;
v___y_539_ = v___y_586_;
goto v___jp_531_;
}
v___jp_588_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_595_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72));
lean_inc_ref(v___x_339_);
v___x_596_ = l_Lean_mkConst(v___x_595_, v___x_339_);
lean_inc_ref(v_base_318_);
v___x_597_ = l_Lean_Expr_app___override(v___x_596_, v_base_318_);
v___x_598_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_597_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
if (lean_obj_tag(v_a_599_) == 1)
{
lean_object* v_val_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_val_600_ = lean_ctor_get(v_a_599_, 0);
lean_inc(v_val_600_);
lean_dec_ref_known(v_a_599_, 1);
v___x_601_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74));
lean_inc_ref(v___x_339_);
v___x_602_ = l_Lean_mkConst(v___x_601_, v___x_339_);
lean_inc_ref(v_base_318_);
v___x_603_ = l_Lean_mkAppB(v___x_602_, v_base_318_, v_val_600_);
v___x_604_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_603_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
if (lean_obj_tag(v_a_605_) == 1)
{
lean_object* v_val_606_; lean_object* v___x_607_; 
v_val_606_ = lean_ctor_get(v_a_605_, 0);
lean_inc(v_val_606_);
lean_dec_ref_known(v_a_605_, 1);
lean_inc_ref(v_semiringInst_319_);
lean_inc_ref(v_base_318_);
lean_inc(v_val_333_);
v___x_607_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_val_333_, v_base_318_, v_semiringInst_319_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
if (lean_obj_tag(v_a_608_) == 1)
{
lean_object* v_val_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_629_; 
v_val_609_ = lean_ctor_get(v_a_608_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_a_608_);
if (v_isSharedCheck_629_ == 0)
{
v___x_611_ = v_a_608_;
v_isShared_612_ = v_isSharedCheck_629_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_val_609_);
lean_dec(v_a_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_629_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v_fst_613_; lean_object* v_snd_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_628_; 
v_fst_613_ = lean_ctor_get(v_val_609_, 0);
v_snd_614_ = lean_ctor_get(v_val_609_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_val_609_);
if (v_isSharedCheck_628_ == 0)
{
v___x_616_ = v_val_609_;
v_isShared_617_ = v_isSharedCheck_628_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_snd_614_);
lean_inc(v_fst_613_);
lean_dec(v_val_609_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_628_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_618_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76));
lean_inc_ref(v___x_339_);
v___x_619_ = l_Lean_mkConst(v___x_618_, v___x_339_);
lean_inc(v_snd_614_);
v___x_620_ = l_Lean_mkRawNatLit(v_snd_614_);
lean_inc(v_val_606_);
lean_inc_ref(v_semiringInst_319_);
lean_inc_ref(v_base_318_);
v___x_621_ = l_Lean_mkApp5(v___x_619_, v_base_318_, v___x_620_, v_semiringInst_319_, v_val_606_, v_fst_613_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_621_);
v___x_623_ = v___x_616_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_snd_614_);
v___x_623_ = v_reuseFailAlloc_627_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_625_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_623_);
v___x_625_ = v___x_611_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
v_val_550_ = v_val_606_;
v_charInst_x3f_551_ = v___x_625_;
v___y_552_ = v___y_589_;
v___y_553_ = v___y_590_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_593_;
v___y_557_ = v___y_594_;
goto v___jp_549_;
}
}
}
}
}
else
{
lean_object* v___x_630_; 
lean_dec(v_a_608_);
v___x_630_ = lean_box(0);
v_val_550_ = v_val_606_;
v_charInst_x3f_551_ = v___x_630_;
v___y_552_ = v___y_589_;
v___y_553_ = v___y_590_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_593_;
v___y_557_ = v___y_594_;
goto v___jp_549_;
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_val_606_);
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_631_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_607_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_607_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
if (lean_obj_tag(v_a_605_) == 1)
{
lean_object* v_val_639_; lean_object* v___x_640_; 
v_val_639_ = lean_ctor_get(v_a_605_, 0);
lean_inc(v_val_639_);
lean_dec_ref_known(v_a_605_, 1);
v___x_640_ = lean_box(0);
v_val_550_ = v_val_639_;
v_charInst_x3f_551_ = v___x_640_;
v___y_552_ = v___y_589_;
v___y_553_ = v___y_590_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_593_;
v___y_557_ = v___y_594_;
goto v___jp_549_;
}
else
{
lean_dec(v_a_605_);
lean_dec_ref_known(v___x_339_, 2);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
v___y_581_ = v___y_589_;
v___y_582_ = v___y_590_;
v___y_583_ = v___y_591_;
v___y_584_ = v___y_592_;
v___y_585_ = v___y_593_;
v___y_586_ = v___y_594_;
goto v___jp_580_;
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_641_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_604_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_604_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
else
{
lean_dec(v_a_599_);
lean_dec_ref_known(v___x_339_, 2);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
v___y_581_ = v___y_589_;
v___y_582_ = v___y_590_;
v___y_583_ = v___y_591_;
v___y_584_ = v___y_592_;
v___y_585_ = v___y_593_;
v___y_586_ = v___y_594_;
goto v___jp_580_;
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_649_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_598_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_598_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_672_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_479_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_479_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_680_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_472_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_472_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_688_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_465_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_465_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
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
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_696_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_454_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_454_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_704_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_447_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_447_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref_known(v___x_418_, 2);
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_712_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_437_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_437_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref_known(v___x_418_, 2);
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_720_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_427_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_427_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_728_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_415_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_415_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_736_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_408_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_408_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_744_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_404_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_404_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_752_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_400_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_400_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_dec_ref_known(v___x_339_, 2);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_760_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_396_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_396_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
v___jp_351_:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_354_, v___y_355_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v_rings_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___f_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_356_, 1);
v_rings_358_ = lean_ctor_get(v_a_357_, 1);
lean_inc_ref(v_rings_358_);
lean_dec(v_a_357_);
v___x_359_ = lean_array_get_size(v_rings_358_);
lean_dec_ref(v_rings_358_);
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v_type_317_);
lean_ctor_set(v___x_361_, 2, v_val_333_);
lean_ctor_set(v___x_361_, 3, v___x_344_);
lean_ctor_set(v___x_361_, 4, v___x_347_);
lean_ctor_set(v___x_361_, 5, v___y_353_);
lean_ctor_set(v___x_361_, 6, v___x_360_);
lean_ctor_set(v___x_361_, 7, v___x_360_);
lean_ctor_set(v___x_361_, 8, v___x_360_);
lean_ctor_set(v___x_361_, 9, v___x_360_);
lean_ctor_set(v___x_361_, 10, v___x_360_);
lean_ctor_set(v___x_361_, 11, v___x_360_);
lean_ctor_set(v___x_361_, 12, v___x_360_);
lean_ctor_set(v___x_361_, 13, v___x_360_);
lean_ctor_set(v___x_361_, 14, v___x_360_);
lean_ctor_set(v___x_361_, 15, v___x_360_);
v___x_362_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v___x_360_);
lean_ctor_set(v___x_362_, 2, v___x_360_);
lean_ctor_set(v___x_362_, 3, v___x_360_);
lean_ctor_set(v___x_362_, 4, v___x_350_);
lean_ctor_set(v___x_362_, 5, v___x_341_);
lean_ctor_set(v___x_362_, 6, v___y_352_);
lean_ctor_set(v___x_362_, 7, v___x_360_);
lean_ctor_set(v___x_362_, 8, v___x_360_);
v___f_363_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0), 2, 1);
lean_closure_set(v___f_363_, 0, v___x_362_);
v___x_364_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_365_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_364_, v___f_363_, v___y_354_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_375_; 
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v___x_365_, 0);
lean_dec(v_unused_376_);
v___x_367_ = v___x_365_;
v_isShared_368_ = v_isSharedCheck_375_;
goto v_resetjp_366_;
}
else
{
lean_dec(v___x_365_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_375_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_359_);
v___x_370_ = v___x_335_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_359_);
v___x_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_372_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_370_);
v___x_372_ = v___x_367_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_del_object(v___x_335_);
v_a_377_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_365_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_365_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___x_350_);
lean_dec_ref(v___x_347_);
lean_dec_ref(v___x_344_);
lean_dec_ref(v___x_341_);
lean_del_object(v___x_335_);
lean_dec(v_val_333_);
lean_dec_ref(v_type_317_);
v_a_385_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_356_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_356_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
}
else
{
lean_object* v___x_769_; lean_object* v___x_771_; 
lean_dec(v_a_329_);
lean_dec_ref(v_commSemiringInst_320_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v___x_769_ = lean_box(0);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_769_);
v___x_771_ = v___x_331_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v_commSemiringInst_320_);
lean_dec_ref(v_semiringInst_319_);
lean_dec_ref(v_base_318_);
lean_dec_ref(v_type_317_);
v_a_774_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_328_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_328_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___boxed(lean_object* v_type_782_, lean_object* v_base_783_, lean_object* v_semiringInst_784_, lean_object* v_commSemiringInst_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(v_type_782_, v_base_783_, v_semiringInst_784_, v_commSemiringInst_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0(lean_object* v_cls_794_, lean_object* v_msg_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v_cls_794_, v_msg_795_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___boxed(lean_object* v_cls_804_, lean_object* v_msg_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0(v_cls_804_, v_msg_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
return v_res_813_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2));
v___x_821_ = l_Lean_stringToMessageData(v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(lean_object* v_type_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___x_830_; 
lean_inc_ref(v_type_822_);
v___x_830_ = l_Lean_Meta_getDecLevel(v_type_822_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc_n(v_a_831_, 2);
lean_dec_ref_known(v___x_830_, 1);
v___x_832_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13));
v___x_833_ = lean_box(0);
v___x_834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_834_, 0, v_a_831_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
lean_inc_ref(v___x_834_);
v___x_835_ = l_Lean_mkConst(v___x_832_, v___x_834_);
lean_inc_ref(v_type_822_);
v___x_836_ = l_Lean_Expr_app___override(v___x_835_, v_type_822_);
v___x_837_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_836_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_1046_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_1046_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_1046_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
if (lean_obj_tag(v_a_838_) == 1)
{
lean_object* v_val_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_1041_; 
lean_del_object(v___x_840_);
v_val_842_ = lean_ctor_get(v_a_838_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_a_838_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_844_ = v_a_838_;
v_isShared_845_ = v_isSharedCheck_1041_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_val_842_);
lean_dec(v_a_838_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_1041_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_toCold_849_; lean_object* v_inheritedTraceOptions_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___x_901_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___x_1026_; lean_object* v_a_1027_; uint8_t v___x_1028_; 
v___x_846_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7));
lean_inc_ref_n(v___x_834_, 3);
v___x_847_ = l_Lean_mkConst(v___x_846_, v___x_834_);
lean_inc(v_val_842_);
lean_inc_ref_n(v_type_822_, 3);
v___x_848_ = l_Lean_mkAppB(v___x_847_, v_type_822_, v_val_842_);
v_toCold_849_ = lean_ctor_get(v_a_827_, 0);
v_inheritedTraceOptions_850_ = lean_ctor_get(v_toCold_849_, 11);
v___x_851_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10));
v___x_852_ = l_Lean_mkConst(v___x_851_, v___x_834_);
lean_inc_ref(v___x_848_);
v___x_853_ = l_Lean_mkAppB(v___x_852_, v_type_822_, v___x_848_);
v___x_854_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12));
v___x_855_ = l_Lean_mkConst(v___x_854_, v___x_834_);
lean_inc_ref(v___x_853_);
v___x_856_ = l_Lean_mkAppB(v___x_855_, v_type_822_, v___x_853_);
v___x_901_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_1026_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_901_, v_inheritedTraceOptions_850_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = lean_unbox(v_a_1027_);
lean_dec(v_a_1027_);
if (v___x_1028_ == 0)
{
v___y_992_ = v_a_823_;
v___y_993_ = v_a_824_;
v___y_994_ = v_a_825_;
v___y_995_ = v_a_826_;
v___y_996_ = v_a_827_;
v___y_997_ = v_a_828_;
goto v___jp_991_;
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1029_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78);
lean_inc_ref(v_type_822_);
v___x_1030_ = l_Lean_MessageData_ofExpr(v_type_822_);
v___x_1031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_901_, v___x_1031_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_dec_ref_known(v___x_1032_, 1);
v___y_992_ = v_a_823_;
v___y_993_ = v_a_824_;
v___y_994_ = v_a_825_;
v___y_995_ = v_a_826_;
v___y_996_ = v_a_827_;
v___y_997_ = v_a_828_;
goto v___jp_991_;
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref(v___x_856_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_848_);
lean_del_object(v___x_844_);
lean_dec(v_val_842_);
lean_dec_ref_known(v___x_834_, 2);
lean_dec(v_a_831_);
lean_dec_ref(v_type_822_);
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
v___jp_857_:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_box(0);
v___x_865_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_862_, v___y_863_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v_rings_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___f_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_865_, 1);
v_rings_867_ = lean_ctor_get(v_a_866_, 1);
lean_inc_ref(v_rings_867_);
lean_dec(v_a_866_);
v___x_868_ = lean_array_get_size(v_rings_867_);
lean_dec_ref(v_rings_867_);
v___x_869_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v_type_822_);
lean_ctor_set(v___x_869_, 2, v_a_831_);
lean_ctor_set(v___x_869_, 3, v___x_848_);
lean_ctor_set(v___x_869_, 4, v___x_853_);
lean_ctor_set(v___x_869_, 5, v___y_860_);
lean_ctor_set(v___x_869_, 6, v___x_864_);
lean_ctor_set(v___x_869_, 7, v___x_864_);
lean_ctor_set(v___x_869_, 8, v___x_864_);
lean_ctor_set(v___x_869_, 9, v___x_864_);
lean_ctor_set(v___x_869_, 10, v___x_864_);
lean_ctor_set(v___x_869_, 11, v___x_864_);
lean_ctor_set(v___x_869_, 12, v___x_864_);
lean_ctor_set(v___x_869_, 13, v___x_864_);
lean_ctor_set(v___x_869_, 14, v___x_864_);
lean_ctor_set(v___x_869_, 15, v___x_864_);
v___x_870_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_864_);
lean_ctor_set(v___x_870_, 2, v___x_864_);
lean_ctor_set(v___x_870_, 3, v___x_864_);
lean_ctor_set(v___x_870_, 4, v___x_856_);
lean_ctor_set(v___x_870_, 5, v_val_842_);
lean_ctor_set(v___x_870_, 6, v___y_861_);
lean_ctor_set(v___x_870_, 7, v___y_859_);
lean_ctor_set(v___x_870_, 8, v___y_858_);
v___f_871_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0), 2, 1);
lean_closure_set(v___f_871_, 0, v___x_870_);
v___x_872_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_873_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_872_, v___f_871_, v___y_862_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_883_; 
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; 
v_unused_884_ = lean_ctor_get(v___x_873_, 0);
lean_dec(v_unused_884_);
v___x_875_ = v___x_873_;
v_isShared_876_ = v_isSharedCheck_883_;
goto v_resetjp_874_;
}
else
{
lean_dec(v___x_873_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_883_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_868_);
v___x_878_ = v___x_844_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_868_);
v___x_878_ = v_reuseFailAlloc_882_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_878_);
v___x_880_ = v___x_875_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
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
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_del_object(v___x_844_);
v_a_885_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_873_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_873_);
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
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec(v___y_861_);
lean_dec(v___y_860_);
lean_dec(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___x_856_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_848_);
lean_del_object(v___x_844_);
lean_dec(v_val_842_);
lean_dec(v_a_831_);
lean_dec_ref(v_type_822_);
v_a_893_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_865_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_865_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
v___jp_902_:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_inc_ref(v___y_913_);
v___x_914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_914_, 0, v___y_913_);
v___x_915_ = l_Lean_MessageData_ofFormat(v___x_914_);
lean_inc_ref(v___y_905_);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___y_905_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_901_, v___x_916_, v___y_908_, v___y_912_, v___y_911_, v___y_910_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_dec_ref_known(v___x_917_, 1);
v___y_858_ = v___y_903_;
v___y_859_ = v___y_904_;
v___y_860_ = v___y_906_;
v___y_861_ = v___y_909_;
v___y_862_ = v___y_907_;
v___y_863_ = v___y_911_;
goto v___jp_857_;
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v___y_909_);
lean_dec(v___y_906_);
lean_dec(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___x_856_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_848_);
lean_del_object(v___x_844_);
lean_dec(v_val_842_);
lean_dec(v_a_831_);
lean_dec_ref(v_type_822_);
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
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
v___jp_926_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_935_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1));
v___x_936_ = l_Lean_mkConst(v___x_935_, v___x_834_);
lean_inc_ref(v_type_822_);
v___x_937_ = l_Lean_Expr_app___override(v___x_936_, v_type_822_);
v___x_938_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_937_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_940_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 1);
lean_inc_ref(v_type_822_);
lean_inc(v_a_831_);
v___x_940_ = l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(v_a_831_, v_type_822_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_toCold_941_; lean_object* v_options_942_; uint8_t v_hasTrace_943_; 
v_toCold_941_ = lean_ctor_get(v___y_933_, 0);
v_options_942_ = lean_ctor_get(v_toCold_941_, 2);
v_hasTrace_943_ = lean_ctor_get_uint8(v_options_942_, sizeof(void*)*1);
if (v_hasTrace_943_ == 0)
{
lean_object* v_a_944_; 
v_a_944_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v___x_940_, 1);
v___y_858_ = v_a_944_;
v___y_859_ = v_a_939_;
v___y_860_ = v___y_927_;
v___y_861_ = v___y_928_;
v___y_862_ = v___y_930_;
v___y_863_ = v___y_933_;
goto v___jp_857_;
}
else
{
lean_object* v_a_945_; lean_object* v_inheritedTraceOptions_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_a_945_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_940_, 1);
v_inheritedTraceOptions_946_ = lean_ctor_get(v_toCold_941_, 11);
v___x_947_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61);
v___x_948_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_946_, v_options_942_, v___x_947_);
if (v___x_948_ == 0)
{
v___y_858_ = v_a_945_;
v___y_859_ = v_a_939_;
v___y_860_ = v___y_927_;
v___y_861_ = v___y_928_;
v___y_862_ = v___y_930_;
v___y_863_ = v___y_933_;
goto v___jp_857_;
}
else
{
lean_object* v___x_949_; 
v___x_949_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3);
if (lean_obj_tag(v_a_945_) == 0)
{
lean_object* v___x_950_; 
v___x_950_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66));
v___y_903_ = v_a_945_;
v___y_904_ = v_a_939_;
v___y_905_ = v___x_949_;
v___y_906_ = v___y_927_;
v___y_907_ = v___y_930_;
v___y_908_ = v___y_931_;
v___y_909_ = v___y_928_;
v___y_910_ = v___y_934_;
v___y_911_ = v___y_933_;
v___y_912_ = v___y_932_;
v___y_913_ = v___x_950_;
goto v___jp_902_;
}
else
{
lean_object* v___x_951_; 
v___x_951_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67));
v___y_903_ = v_a_945_;
v___y_904_ = v_a_939_;
v___y_905_ = v___x_949_;
v___y_906_ = v___y_927_;
v___y_907_ = v___y_930_;
v___y_908_ = v___y_931_;
v___y_909_ = v___y_928_;
v___y_910_ = v___y_934_;
v___y_911_ = v___y_933_;
v___y_912_ = v___y_932_;
v___y_913_ = v___x_951_;
goto v___jp_902_;
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v_a_939_);
lean_dec(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___x_856_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_848_);
lean_del_object(v___x_844_);
lean_dec(v_val_842_);
lean_dec(v_a_831_);
lean_dec_ref(v_type_822_);
v_a_952_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_940_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_940_);
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
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___x_856_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_848_);
lean_del_object(v___x_844_);
lean_dec(v_val_842_);
lean_dec(v_a_831_);
lean_dec_ref(v_type_822_);
v_a_960_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_938_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_938_);
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
v___jp_968_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
lean_inc_ref(v___y_978_);
v___x_979_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_979_, 0, v___y_978_);
v___x_980_ = l_Lean_MessageData_ofFormat(v___x_979_);
lean_inc_ref(v___y_974_);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___y_974_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_901_, v___x_981_, v___y_972_, v___y_969_, v___y_971_, v___y_977_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_dec_ref_known(v___x_982_, 1);
v___y_927_ = v___y_973_;
v___y_928_ = v___y_975_;
v___y_929_ = v___y_976_;
v___y_930_ = v___y_970_;
v___y_931_ = v___y_972_;
v___y_932_ = v___y_969_;
v___y_933_ = v___y_971_;
v___y_934_ = v___y_977_;
goto v___jp_926_;
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v___y_975_);
lean_dec(v___y_973_);
lean_dec_ref(v___x_856_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_848_);
lean_del_object(v___x_844_);
lean_dec(v_val_842_);
lean_dec_ref_known(v___x_834_, 2);
lean_dec(v_a_831_);
lean_dec_ref(v_type_822_);
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
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
v___jp_991_:
{
lean_object* v___x_998_; 
lean_inc_ref(v___x_853_);
lean_inc_ref(v_type_822_);
lean_inc(v_a_831_);
v___x_998_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_a_831_, v_type_822_, v___x_853_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
lean_inc_ref(v_type_822_);
lean_inc(v_a_831_);
v___x_1000_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_a_831_, v_type_822_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_toCold_1001_; lean_object* v_a_1002_; lean_object* v_inheritedTraceOptions_1003_; lean_object* v___x_1004_; lean_object* v_a_1005_; uint8_t v___x_1006_; 
v_toCold_1001_ = lean_ctor_get(v___y_996_, 0);
v_a_1002_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1000_, 1);
v_inheritedTraceOptions_1003_ = lean_ctor_get(v_toCold_1001_, 11);
v___x_1004_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_901_, v_inheritedTraceOptions_1003_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = lean_unbox(v_a_1005_);
lean_dec(v_a_1005_);
if (v___x_1006_ == 0)
{
v___y_927_ = v_a_999_;
v___y_928_ = v_a_1002_;
v___y_929_ = v___y_992_;
v___y_930_ = v___y_993_;
v___y_931_ = v___y_994_;
v___y_932_ = v___y_995_;
v___y_933_ = v___y_996_;
v___y_934_ = v___y_997_;
goto v___jp_926_;
}
else
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65);
if (lean_obj_tag(v_a_1002_) == 0)
{
lean_object* v___x_1008_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66));
v___y_969_ = v___y_995_;
v___y_970_ = v___y_993_;
v___y_971_ = v___y_996_;
v___y_972_ = v___y_994_;
v___y_973_ = v_a_999_;
v___y_974_ = v___x_1007_;
v___y_975_ = v_a_1002_;
v___y_976_ = v___y_992_;
v___y_977_ = v___y_997_;
v___y_978_ = v___x_1008_;
goto v___jp_968_;
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67));
v___y_969_ = v___y_995_;
v___y_970_ = v___y_993_;
v___y_971_ = v___y_996_;
v___y_972_ = v___y_994_;
v___y_973_ = v_a_999_;
v___y_974_ = v___x_1007_;
v___y_975_ = v_a_1002_;
v___y_976_ = v___y_992_;
v___y_977_ = v___y_997_;
v___y_978_ = v___x_1009_;
goto v___jp_968_;
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_a_999_);
lean_dec_ref(v___x_856_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_848_);
lean_del_object(v___x_844_);
lean_dec(v_val_842_);
lean_dec_ref_known(v___x_834_, 2);
lean_dec(v_a_831_);
lean_dec_ref(v_type_822_);
v_a_1010_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1000_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1000_);
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
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v___x_856_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_848_);
lean_del_object(v___x_844_);
lean_dec(v_val_842_);
lean_dec_ref_known(v___x_834_, 2);
lean_dec(v_a_831_);
lean_dec_ref(v_type_822_);
v_a_1018_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_998_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_998_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_dec(v_a_838_);
lean_dec_ref_known(v___x_834_, 2);
lean_dec(v_a_831_);
lean_dec_ref(v_type_822_);
v___x_1042_ = lean_box(0);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_1042_);
v___x_1044_ = v___x_840_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref_known(v___x_834_, 2);
lean_dec(v_a_831_);
lean_dec_ref(v_type_822_);
v_a_1047_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_837_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_837_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v_type_822_);
v_a_1055_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_830_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_830_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___boxed(lean_object* v_type_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(lean_object* v_type_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
lean_inc_ref(v_type_1084_);
v___x_1092_ = l_Lean_Expr_cleanupAnnotations(v_type_1084_);
v___x_1093_ = l_Lean_Expr_isApp(v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_dec_ref(v___x_1092_);
v___x_1094_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1094_;
}
else
{
lean_object* v_arg_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_arg_1095_ = lean_ctor_get(v___x_1092_, 1);
lean_inc_ref(v_arg_1095_);
v___x_1096_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1092_);
v___x_1097_ = l_Lean_Expr_isApp(v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_dec_ref(v___x_1096_);
lean_dec_ref(v_arg_1095_);
v___x_1098_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1098_;
}
else
{
lean_object* v_arg_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_arg_1099_ = lean_ctor_get(v___x_1096_, 1);
lean_inc_ref(v_arg_1099_);
v___x_1100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1096_);
v___x_1101_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1));
v___x_1102_ = l_Lean_Expr_isConstOf(v___x_1100_, v___x_1101_);
lean_dec_ref(v___x_1100_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; 
lean_dec_ref(v_arg_1099_);
lean_dec_ref(v_arg_1095_);
v___x_1103_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1103_;
}
else
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
lean_inc_ref(v_arg_1095_);
v___x_1104_ = l_Lean_Expr_cleanupAnnotations(v_arg_1095_);
v___x_1105_ = l_Lean_Expr_isApp(v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
lean_dec_ref(v___x_1104_);
lean_dec_ref(v_arg_1099_);
lean_dec_ref(v_arg_1095_);
v___x_1106_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1106_;
}
else
{
lean_object* v_arg_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v_arg_1107_ = lean_ctor_get(v___x_1104_, 1);
lean_inc_ref(v_arg_1107_);
v___x_1108_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1104_);
v___x_1109_ = l_Lean_Expr_isApp(v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec_ref(v___x_1108_);
lean_dec_ref(v_arg_1107_);
lean_dec_ref(v_arg_1099_);
lean_dec_ref(v_arg_1095_);
v___x_1110_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1111_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1108_);
v___x_1112_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2));
v___x_1113_ = l_Lean_Expr_isConstOf(v___x_1111_, v___x_1112_);
lean_dec_ref(v___x_1111_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
lean_dec_ref(v_arg_1107_);
lean_dec_ref(v_arg_1099_);
lean_dec_ref(v_arg_1095_);
v___x_1114_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; 
v___x_1115_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(v_type_1084_, v_arg_1099_, v_arg_1095_, v_arg_1107_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1115_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___boxed(lean_object* v_type_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0(lean_object* v___x_1125_, lean_object* v_s_1126_){
_start:
{
lean_object* v_exp_1127_; lean_object* v_rings_1128_; lean_object* v_semirings_1129_; lean_object* v_ncRings_1130_; lean_object* v_ncSemirings_1131_; lean_object* v_typeClassify_1132_; lean_object* v_orders_1133_; lean_object* v_typeOrderClassify_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1142_; 
v_exp_1127_ = lean_ctor_get(v_s_1126_, 0);
v_rings_1128_ = lean_ctor_get(v_s_1126_, 1);
v_semirings_1129_ = lean_ctor_get(v_s_1126_, 2);
v_ncRings_1130_ = lean_ctor_get(v_s_1126_, 3);
v_ncSemirings_1131_ = lean_ctor_get(v_s_1126_, 4);
v_typeClassify_1132_ = lean_ctor_get(v_s_1126_, 5);
v_orders_1133_ = lean_ctor_get(v_s_1126_, 6);
v_typeOrderClassify_1134_ = lean_ctor_get(v_s_1126_, 7);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_s_1126_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1136_ = v_s_1126_;
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_typeOrderClassify_1134_);
lean_inc(v_orders_1133_);
lean_inc(v_typeClassify_1132_);
lean_inc(v_ncSemirings_1131_);
lean_inc(v_ncRings_1130_);
lean_inc(v_semirings_1129_);
lean_inc(v_rings_1128_);
lean_inc(v_exp_1127_);
lean_dec(v_s_1126_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_array_push(v_ncRings_1130_, v___x_1125_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 3, v___x_1138_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_exp_1127_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_rings_1128_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_semirings_1129_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_ncSemirings_1131_);
lean_ctor_set(v_reuseFailAlloc_1141_, 5, v_typeClassify_1132_);
lean_ctor_set(v_reuseFailAlloc_1141_, 6, v_orders_1133_);
lean_ctor_set(v_reuseFailAlloc_1141_, 7, v_typeOrderClassify_1134_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(lean_object* v_type_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v___x_1151_; 
lean_inc_ref(v_type_1143_);
v___x_1151_ = l_Lean_Meta_getDecLevel(v_type_1143_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc_n(v_a_1152_, 2);
lean_dec_ref_known(v___x_1151_, 1);
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14));
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1155_, 0, v_a_1152_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
lean_inc_ref(v___x_1155_);
v___x_1156_ = l_Lean_mkConst(v___x_1153_, v___x_1155_);
lean_inc_ref(v_type_1143_);
v___x_1157_ = l_Lean_Expr_app___override(v___x_1156_, v_type_1143_);
v___x_1158_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1157_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1247_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1247_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1247_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
if (lean_obj_tag(v_a_1159_) == 1)
{
lean_object* v_toCold_1163_; lean_object* v_options_1164_; lean_object* v_val_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1242_; 
lean_del_object(v___x_1161_);
v_toCold_1163_ = lean_ctor_get(v_a_1148_, 0);
v_options_1164_ = lean_ctor_get(v_toCold_1163_, 2);
v_val_1165_ = lean_ctor_get(v_a_1159_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_a_1159_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1167_ = v_a_1159_;
v_isShared_1168_ = v_isSharedCheck_1242_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_val_1165_);
lean_dec(v_a_1159_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1242_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_inheritedTraceOptions_1169_; uint8_t v_hasTrace_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; 
v_inheritedTraceOptions_1169_ = lean_ctor_get(v_toCold_1163_, 11);
v_hasTrace_1170_ = lean_ctor_get_uint8(v_options_1164_, sizeof(void*)*1);
v___x_1171_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10));
v___x_1172_ = l_Lean_mkConst(v___x_1171_, v___x_1155_);
lean_inc(v_val_1165_);
lean_inc_ref(v_type_1143_);
v___x_1173_ = l_Lean_mkAppB(v___x_1172_, v_type_1143_, v_val_1165_);
if (v_hasTrace_1170_ == 0)
{
v___y_1175_ = v_a_1144_;
v___y_1176_ = v_a_1145_;
v___y_1177_ = v_a_1146_;
v___y_1178_ = v_a_1147_;
v___y_1179_ = v_a_1148_;
v___y_1180_ = v_a_1149_;
goto v___jp_1174_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1227_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_1228_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61);
v___x_1229_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1169_, v_options_1164_, v___x_1228_);
if (v___x_1229_ == 0)
{
v___y_1175_ = v_a_1144_;
v___y_1176_ = v_a_1145_;
v___y_1177_ = v_a_1146_;
v___y_1178_ = v_a_1147_;
v___y_1179_ = v_a_1148_;
v___y_1180_ = v_a_1149_;
goto v___jp_1174_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1230_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78);
lean_inc_ref(v_type_1143_);
v___x_1231_ = l_Lean_MessageData_ofExpr(v_type_1143_);
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_1227_, v___x_1232_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_dec_ref_known(v___x_1233_, 1);
v___y_1175_ = v_a_1144_;
v___y_1176_ = v_a_1145_;
v___y_1177_ = v_a_1146_;
v___y_1178_ = v_a_1147_;
v___y_1179_ = v_a_1148_;
v___y_1180_ = v_a_1149_;
goto v___jp_1174_;
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref(v___x_1173_);
lean_del_object(v___x_1167_);
lean_dec(v_val_1165_);
lean_dec(v_a_1152_);
lean_dec_ref(v_type_1143_);
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
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
}
v___jp_1174_:
{
lean_object* v___x_1181_; 
lean_inc_ref(v___x_1173_);
lean_inc_ref(v_type_1143_);
lean_inc(v_a_1152_);
v___x_1181_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_a_1152_, v_type_1143_, v___x_1173_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_1176_, v___y_1179_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v_ncRings_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v_ncRings_1185_ = lean_ctor_get(v_a_1184_, 3);
lean_inc_ref(v_ncRings_1185_);
lean_dec(v_a_1184_);
v___x_1186_ = lean_array_get_size(v_ncRings_1185_);
lean_dec_ref(v_ncRings_1185_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v_type_1143_);
lean_ctor_set(v___x_1188_, 2, v_a_1152_);
lean_ctor_set(v___x_1188_, 3, v_val_1165_);
lean_ctor_set(v___x_1188_, 4, v___x_1173_);
lean_ctor_set(v___x_1188_, 5, v_a_1182_);
lean_ctor_set(v___x_1188_, 6, v___x_1187_);
lean_ctor_set(v___x_1188_, 7, v___x_1187_);
lean_ctor_set(v___x_1188_, 8, v___x_1187_);
lean_ctor_set(v___x_1188_, 9, v___x_1187_);
lean_ctor_set(v___x_1188_, 10, v___x_1187_);
lean_ctor_set(v___x_1188_, 11, v___x_1187_);
lean_ctor_set(v___x_1188_, 12, v___x_1187_);
lean_ctor_set(v___x_1188_, 13, v___x_1187_);
lean_ctor_set(v___x_1188_, 14, v___x_1187_);
lean_ctor_set(v___x_1188_, 15, v___x_1187_);
v___f_1189_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1189_, 0, v___x_1188_);
v___x_1190_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1191_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1190_, v___f_1189_, v___y_1176_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1201_; 
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v___x_1191_, 0);
lean_dec(v_unused_1202_);
v___x_1193_ = v___x_1191_;
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
else
{
lean_dec(v___x_1191_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1186_);
v___x_1196_ = v___x_1167_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1186_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1196_);
v___x_1198_ = v___x_1193_;
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
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_del_object(v___x_1167_);
v_a_1203_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1191_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1191_);
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
lean_dec(v_a_1182_);
lean_dec_ref(v___x_1173_);
lean_del_object(v___x_1167_);
lean_dec(v_val_1165_);
lean_dec(v_a_1152_);
lean_dec_ref(v_type_1143_);
v_a_1211_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1183_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1183_);
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
lean_dec_ref(v___x_1173_);
lean_del_object(v___x_1167_);
lean_dec(v_val_1165_);
lean_dec(v_a_1152_);
lean_dec_ref(v_type_1143_);
v_a_1219_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1181_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1181_);
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
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
lean_dec(v_a_1159_);
lean_dec_ref_known(v___x_1155_, 2);
lean_dec(v_a_1152_);
lean_dec_ref(v_type_1143_);
v___x_1243_ = lean_box(0);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1243_);
v___x_1245_ = v___x_1161_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref_known(v___x_1155_, 2);
lean_dec(v_a_1152_);
lean_dec_ref(v_type_1143_);
v_a_1248_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1158_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1158_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v_type_1143_);
v_a_1256_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1151_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1151_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___boxed(lean_object* v_type_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(v_type_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v_ks_1277_; lean_object* v_vs_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1304_; 
v_ks_1277_ = lean_ctor_get(v_x_1273_, 0);
v_vs_1278_ = lean_ctor_get(v_x_1273_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_x_1273_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1280_ = v_x_1273_;
v_isShared_1281_ = v_isSharedCheck_1304_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_vs_1278_);
lean_inc(v_ks_1277_);
lean_dec(v_x_1273_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1304_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = lean_array_get_size(v_ks_1277_);
v___x_1283_ = lean_nat_dec_lt(v_x_1274_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
lean_dec(v_x_1274_);
v___x_1284_ = lean_array_push(v_ks_1277_, v_x_1275_);
v___x_1285_ = lean_array_push(v_vs_1278_, v_x_1276_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1285_);
lean_ctor_set(v___x_1280_, 0, v___x_1284_);
v___x_1287_ = v___x_1280_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
else
{
lean_object* v_k_x27_1289_; size_t v___x_1290_; size_t v___x_1291_; uint8_t v___x_1292_; 
v_k_x27_1289_ = lean_array_fget_borrowed(v_ks_1277_, v_x_1274_);
v___x_1290_ = lean_ptr_addr(v_x_1275_);
v___x_1291_ = lean_ptr_addr(v_k_x27_1289_);
v___x_1292_ = lean_usize_dec_eq(v___x_1290_, v___x_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1294_; 
if (v_isShared_1281_ == 0)
{
v___x_1294_ = v___x_1280_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_ks_1277_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_vs_1278_);
v___x_1294_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_nat_add(v_x_1274_, v___x_1295_);
lean_dec(v_x_1274_);
v_x_1273_ = v___x_1294_;
v_x_1274_ = v___x_1296_;
goto _start;
}
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1299_ = lean_array_fset(v_ks_1277_, v_x_1274_, v_x_1275_);
v___x_1300_ = lean_array_fset(v_vs_1278_, v_x_1274_, v_x_1276_);
lean_dec(v_x_1274_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1300_);
lean_ctor_set(v___x_1280_, 0, v___x_1299_);
v___x_1302_ = v___x_1280_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1305_, lean_object* v_k_1306_, lean_object* v_v_1307_){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1305_, v___x_1308_, v_k_1306_, v_v_1307_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(lean_object* v_x_1311_, size_t v_x_1312_, size_t v_x_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_){
_start:
{
if (lean_obj_tag(v_x_1311_) == 0)
{
lean_object* v_es_1316_; size_t v___x_1317_; size_t v___x_1318_; lean_object* v_j_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_es_1316_ = lean_ctor_get(v_x_1311_, 0);
v___x_1317_ = ((size_t)31ULL);
v___x_1318_ = lean_usize_land(v_x_1312_, v___x_1317_);
v_j_1319_ = lean_usize_to_nat(v___x_1318_);
v___x_1320_ = lean_array_get_size(v_es_1316_);
v___x_1321_ = lean_nat_dec_lt(v_j_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_dec(v_j_1319_);
lean_dec(v_x_1315_);
lean_dec_ref(v_x_1314_);
return v_x_1311_;
}
else
{
lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1362_; 
lean_inc_ref(v_es_1316_);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_x_1311_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; 
v_unused_1363_ = lean_ctor_get(v_x_1311_, 0);
lean_dec(v_unused_1363_);
v___x_1323_ = v_x_1311_;
v_isShared_1324_ = v_isSharedCheck_1362_;
goto v_resetjp_1322_;
}
else
{
lean_dec(v_x_1311_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1362_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_v_1325_; lean_object* v___x_1326_; lean_object* v_xs_x27_1327_; lean_object* v___y_1329_; 
v_v_1325_ = lean_array_fget(v_es_1316_, v_j_1319_);
v___x_1326_ = lean_box(0);
v_xs_x27_1327_ = lean_array_fset(v_es_1316_, v_j_1319_, v___x_1326_);
switch(lean_obj_tag(v_v_1325_))
{
case 0:
{
lean_object* v_key_1334_; lean_object* v_val_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1347_; 
v_key_1334_ = lean_ctor_get(v_v_1325_, 0);
v_val_1335_ = lean_ctor_get(v_v_1325_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_v_1325_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1337_ = v_v_1325_;
v_isShared_1338_ = v_isSharedCheck_1347_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_val_1335_);
lean_inc(v_key_1334_);
lean_dec(v_v_1325_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1347_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
size_t v___x_1339_; size_t v___x_1340_; uint8_t v___x_1341_; 
v___x_1339_ = lean_ptr_addr(v_x_1314_);
v___x_1340_ = lean_ptr_addr(v_key_1334_);
v___x_1341_ = lean_usize_dec_eq(v___x_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_del_object(v___x_1337_);
v___x_1342_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1334_, v_val_1335_, v_x_1314_, v_x_1315_);
v___x_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
v___y_1329_ = v___x_1343_;
goto v___jp_1328_;
}
else
{
lean_object* v___x_1345_; 
lean_dec(v_val_1335_);
lean_dec(v_key_1334_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v_x_1315_);
lean_ctor_set(v___x_1337_, 0, v_x_1314_);
v___x_1345_ = v___x_1337_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_x_1314_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_x_1315_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
v___y_1329_ = v___x_1345_;
goto v___jp_1328_;
}
}
}
}
case 1:
{
lean_object* v_node_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1360_; 
v_node_1348_ = lean_ctor_get(v_v_1325_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_v_1325_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1350_ = v_v_1325_;
v_isShared_1351_ = v_isSharedCheck_1360_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_node_1348_);
lean_dec(v_v_1325_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1360_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
size_t v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; size_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1352_ = ((size_t)5ULL);
v___x_1353_ = lean_usize_shift_right(v_x_1312_, v___x_1352_);
v___x_1354_ = ((size_t)1ULL);
v___x_1355_ = lean_usize_add(v_x_1313_, v___x_1354_);
v___x_1356_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_node_1348_, v___x_1353_, v___x_1355_, v_x_1314_, v_x_1315_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1356_);
v___x_1358_ = v___x_1350_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
v___y_1329_ = v___x_1358_;
goto v___jp_1328_;
}
}
}
default: 
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_x_1314_);
lean_ctor_set(v___x_1361_, 1, v_x_1315_);
v___y_1329_ = v___x_1361_;
goto v___jp_1328_;
}
}
v___jp_1328_:
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1330_ = lean_array_fset(v_xs_x27_1327_, v_j_1319_, v___y_1329_);
lean_dec(v_j_1319_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1330_);
v___x_1332_ = v___x_1323_;
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
}
else
{
lean_object* v_ks_1364_; lean_object* v_vs_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1383_; 
v_ks_1364_ = lean_ctor_get(v_x_1311_, 0);
v_vs_1365_ = lean_ctor_get(v_x_1311_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_x_1311_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1367_ = v_x_1311_;
v_isShared_1368_ = v_isSharedCheck_1383_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_vs_1365_);
lean_inc(v_ks_1364_);
lean_dec(v_x_1311_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1383_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_ks_1364_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_vs_1365_);
v___x_1370_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v_newNode_1371_; size_t v___x_1372_; uint8_t v___x_1373_; 
v_newNode_1371_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v___x_1370_, v_x_1314_, v_x_1315_);
v___x_1372_ = ((size_t)7ULL);
v___x_1373_ = lean_usize_dec_le(v___x_1372_, v_x_1313_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1374_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1371_);
v___x_1375_ = lean_unsigned_to_nat(4u);
v___x_1376_ = lean_nat_dec_lt(v___x_1374_, v___x_1375_);
lean_dec(v___x_1374_);
if (v___x_1376_ == 0)
{
lean_object* v_ks_1377_; lean_object* v_vs_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_ks_1377_ = lean_ctor_get(v_newNode_1371_, 0);
lean_inc_ref(v_ks_1377_);
v_vs_1378_ = lean_ctor_get(v_newNode_1371_, 1);
lean_inc_ref(v_vs_1378_);
lean_dec_ref(v_newNode_1371_);
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0);
v___x_1381_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_x_1313_, v_ks_1377_, v_vs_1378_, v___x_1379_, v___x_1380_);
lean_dec_ref(v_vs_1378_);
lean_dec_ref(v_ks_1377_);
return v___x_1381_;
}
else
{
return v_newNode_1371_;
}
}
else
{
return v_newNode_1371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_1384_, lean_object* v_keys_1385_, lean_object* v_vals_1386_, lean_object* v_i_1387_, lean_object* v_entries_1388_){
_start:
{
lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = lean_array_get_size(v_keys_1385_);
v___x_1390_ = lean_nat_dec_lt(v_i_1387_, v___x_1389_);
if (v___x_1390_ == 0)
{
lean_dec(v_i_1387_);
return v_entries_1388_;
}
else
{
lean_object* v_k_1391_; lean_object* v_v_1392_; size_t v___x_1393_; size_t v___x_1394_; size_t v___x_1395_; uint64_t v___x_1396_; size_t v_h_1397_; size_t v___x_1398_; lean_object* v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; size_t v_h_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_k_1391_ = lean_array_fget_borrowed(v_keys_1385_, v_i_1387_);
v_v_1392_ = lean_array_fget_borrowed(v_vals_1386_, v_i_1387_);
v___x_1393_ = lean_ptr_addr(v_k_1391_);
v___x_1394_ = ((size_t)3ULL);
v___x_1395_ = lean_usize_shift_right(v___x_1393_, v___x_1394_);
v___x_1396_ = lean_usize_to_uint64(v___x_1395_);
v_h_1397_ = lean_uint64_to_usize(v___x_1396_);
v___x_1398_ = ((size_t)5ULL);
v___x_1399_ = lean_unsigned_to_nat(1u);
v___x_1400_ = ((size_t)1ULL);
v___x_1401_ = lean_usize_sub(v_depth_1384_, v___x_1400_);
v___x_1402_ = lean_usize_mul(v___x_1398_, v___x_1401_);
v_h_1403_ = lean_usize_shift_right(v_h_1397_, v___x_1402_);
v___x_1404_ = lean_nat_add(v_i_1387_, v___x_1399_);
lean_dec(v_i_1387_);
lean_inc(v_v_1392_);
lean_inc(v_k_1391_);
v___x_1405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_entries_1388_, v_h_1403_, v_depth_1384_, v_k_1391_, v_v_1392_);
v_i_1387_ = v___x_1404_;
v_entries_1388_ = v___x_1405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1407_, lean_object* v_keys_1408_, lean_object* v_vals_1409_, lean_object* v_i_1410_, lean_object* v_entries_1411_){
_start:
{
size_t v_depth_boxed_1412_; lean_object* v_res_1413_; 
v_depth_boxed_1412_ = lean_unbox_usize(v_depth_1407_);
lean_dec(v_depth_1407_);
v_res_1413_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1412_, v_keys_1408_, v_vals_1409_, v_i_1410_, v_entries_1411_);
lean_dec_ref(v_vals_1409_);
lean_dec_ref(v_keys_1408_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_1414_, lean_object* v_x_1415_, lean_object* v_x_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_){
_start:
{
size_t v_x_2146__boxed_1419_; size_t v_x_2147__boxed_1420_; lean_object* v_res_1421_; 
v_x_2146__boxed_1419_ = lean_unbox_usize(v_x_1415_);
lean_dec(v_x_1415_);
v_x_2147__boxed_1420_ = lean_unbox_usize(v_x_1416_);
lean_dec(v_x_1416_);
v_res_1421_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_1414_, v_x_2146__boxed_1419_, v_x_2147__boxed_1420_, v_x_1417_, v_x_1418_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(lean_object* v_x_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
size_t v___x_1425_; size_t v___x_1426_; size_t v___x_1427_; uint64_t v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; 
v___x_1425_ = lean_ptr_addr(v_x_1423_);
v___x_1426_ = ((size_t)3ULL);
v___x_1427_ = lean_usize_shift_right(v___x_1425_, v___x_1426_);
v___x_1428_ = lean_usize_to_uint64(v___x_1427_);
v___x_1429_ = lean_uint64_to_usize(v___x_1428_);
v___x_1430_ = ((size_t)1ULL);
v___x_1431_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_1422_, v___x_1429_, v___x_1430_, v_x_1423_, v_x_1424_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0(lean_object* v_type_1432_, lean_object* v___y_1433_, lean_object* v_s_1434_){
_start:
{
lean_object* v_exp_1435_; lean_object* v_rings_1436_; lean_object* v_semirings_1437_; lean_object* v_ncRings_1438_; lean_object* v_ncSemirings_1439_; lean_object* v_typeClassify_1440_; lean_object* v_orders_1441_; lean_object* v_typeOrderClassify_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1450_; 
v_exp_1435_ = lean_ctor_get(v_s_1434_, 0);
v_rings_1436_ = lean_ctor_get(v_s_1434_, 1);
v_semirings_1437_ = lean_ctor_get(v_s_1434_, 2);
v_ncRings_1438_ = lean_ctor_get(v_s_1434_, 3);
v_ncSemirings_1439_ = lean_ctor_get(v_s_1434_, 4);
v_typeClassify_1440_ = lean_ctor_get(v_s_1434_, 5);
v_orders_1441_ = lean_ctor_get(v_s_1434_, 6);
v_typeOrderClassify_1442_ = lean_ctor_get(v_s_1434_, 7);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_s_1434_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1444_ = v_s_1434_;
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_typeOrderClassify_1442_);
lean_inc(v_orders_1441_);
lean_inc(v_typeClassify_1440_);
lean_inc(v_ncSemirings_1439_);
lean_inc(v_ncRings_1438_);
lean_inc(v_semirings_1437_);
lean_inc(v_rings_1436_);
lean_inc(v_exp_1435_);
lean_dec(v_s_1434_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1446_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_1440_, v_type_1432_, v___y_1433_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 5, v___x_1446_);
v___x_1448_ = v___x_1444_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_exp_1435_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_rings_1436_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v_semirings_1437_);
lean_ctor_set(v_reuseFailAlloc_1449_, 3, v_ncRings_1438_);
lean_ctor_set(v_reuseFailAlloc_1449_, 4, v_ncSemirings_1439_);
lean_ctor_set(v_reuseFailAlloc_1449_, 5, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1449_, 6, v_orders_1441_);
lean_ctor_set(v_reuseFailAlloc_1449_, 7, v_typeOrderClassify_1442_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1451_, lean_object* v_vals_1452_, lean_object* v_i_1453_, lean_object* v_k_1454_){
_start:
{
lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = lean_array_get_size(v_keys_1451_);
v___x_1456_ = lean_nat_dec_lt(v_i_1453_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_dec(v_i_1453_);
v___x_1457_ = lean_box(0);
return v___x_1457_;
}
else
{
lean_object* v_k_x27_1458_; size_t v___x_1459_; size_t v___x_1460_; uint8_t v___x_1461_; 
v_k_x27_1458_ = lean_array_fget_borrowed(v_keys_1451_, v_i_1453_);
v___x_1459_ = lean_ptr_addr(v_k_1454_);
v___x_1460_ = lean_ptr_addr(v_k_x27_1458_);
v___x_1461_ = lean_usize_dec_eq(v___x_1459_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_add(v_i_1453_, v___x_1462_);
lean_dec(v_i_1453_);
v_i_1453_ = v___x_1463_;
goto _start;
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_array_fget_borrowed(v_vals_1452_, v_i_1453_);
lean_dec(v_i_1453_);
lean_inc(v___x_1465_);
v___x_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1467_, lean_object* v_vals_1468_, lean_object* v_i_1469_, lean_object* v_k_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1467_, v_vals_1468_, v_i_1469_, v_k_1470_);
lean_dec_ref(v_k_1470_);
lean_dec_ref(v_vals_1468_);
lean_dec_ref(v_keys_1467_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(lean_object* v_x_1472_, size_t v_x_1473_, lean_object* v_x_1474_){
_start:
{
if (lean_obj_tag(v_x_1472_) == 0)
{
lean_object* v_es_1475_; lean_object* v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; lean_object* v_j_1479_; lean_object* v___x_1480_; 
v_es_1475_ = lean_ctor_get(v_x_1472_, 0);
v___x_1476_ = lean_box(2);
v___x_1477_ = ((size_t)31ULL);
v___x_1478_ = lean_usize_land(v_x_1473_, v___x_1477_);
v_j_1479_ = lean_usize_to_nat(v___x_1478_);
v___x_1480_ = lean_array_get_borrowed(v___x_1476_, v_es_1475_, v_j_1479_);
lean_dec(v_j_1479_);
switch(lean_obj_tag(v___x_1480_))
{
case 0:
{
lean_object* v_key_1481_; lean_object* v_val_1482_; size_t v___x_1483_; size_t v___x_1484_; uint8_t v___x_1485_; 
v_key_1481_ = lean_ctor_get(v___x_1480_, 0);
v_val_1482_ = lean_ctor_get(v___x_1480_, 1);
v___x_1483_ = lean_ptr_addr(v_x_1474_);
v___x_1484_ = lean_ptr_addr(v_key_1481_);
v___x_1485_ = lean_usize_dec_eq(v___x_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_box(0);
return v___x_1486_;
}
else
{
lean_object* v___x_1487_; 
lean_inc(v_val_1482_);
v___x_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1487_, 0, v_val_1482_);
return v___x_1487_;
}
}
case 1:
{
lean_object* v_node_1488_; size_t v___x_1489_; size_t v___x_1490_; 
v_node_1488_ = lean_ctor_get(v___x_1480_, 0);
v___x_1489_ = ((size_t)5ULL);
v___x_1490_ = lean_usize_shift_right(v_x_1473_, v___x_1489_);
v_x_1472_ = v_node_1488_;
v_x_1473_ = v___x_1490_;
goto _start;
}
default: 
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_box(0);
return v___x_1492_;
}
}
}
else
{
lean_object* v_ks_1493_; lean_object* v_vs_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_ks_1493_ = lean_ctor_get(v_x_1472_, 0);
v_vs_1494_ = lean_ctor_get(v_x_1472_, 1);
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1493_, v_vs_1494_, v___x_1495_, v_x_1474_);
return v___x_1496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_){
_start:
{
size_t v_x_2365__boxed_1500_; lean_object* v_res_1501_; 
v_x_2365__boxed_1500_ = lean_unbox_usize(v_x_1498_);
lean_dec(v_x_1498_);
v_res_1501_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_1497_, v_x_2365__boxed_1500_, v_x_1499_);
lean_dec_ref(v_x_1499_);
lean_dec_ref(v_x_1497_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(lean_object* v_x_1502_, lean_object* v_x_1503_){
_start:
{
size_t v___x_1504_; size_t v___x_1505_; size_t v___x_1506_; uint64_t v___x_1507_; size_t v___x_1508_; lean_object* v___x_1509_; 
v___x_1504_ = lean_ptr_addr(v_x_1503_);
v___x_1505_ = ((size_t)3ULL);
v___x_1506_ = lean_usize_shift_right(v___x_1504_, v___x_1505_);
v___x_1507_ = lean_usize_to_uint64(v___x_1506_);
v___x_1508_ = lean_uint64_to_usize(v___x_1507_);
v___x_1509_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_1502_, v___x_1508_, v_x_1503_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg___boxed(lean_object* v_x_1510_, lean_object* v_x_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_1510_, v_x_1511_);
lean_dec_ref(v_x_1511_);
lean_dec_ref(v_x_1510_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(lean_object* v_type_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1515_, v_a_1518_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1576_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1576_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1576_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v_typeClassify_1526_; lean_object* v___x_1527_; 
v_typeClassify_1526_ = lean_ctor_get(v_a_1522_, 5);
lean_inc_ref(v_typeClassify_1526_);
lean_dec(v_a_1522_);
v___x_1527_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_1526_, v_type_1513_);
lean_dec_ref(v_typeClassify_1526_);
if (lean_obj_tag(v___x_1527_) == 1)
{
lean_object* v_val_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref(v_type_1513_);
v_val_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1543_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_val_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1543_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
if (lean_obj_tag(v_val_1528_) == 0)
{
lean_object* v_id_1532_; lean_object* v___x_1534_; 
v_id_1532_ = lean_ctor_get(v_val_1528_, 0);
lean_inc(v_id_1532_);
lean_dec_ref_known(v_val_1528_, 1);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v_id_1532_);
v___x_1534_ = v___x_1530_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_id_1532_);
v___x_1534_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1534_);
v___x_1536_ = v___x_1524_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
lean_del_object(v___x_1530_);
lean_dec(v_val_1528_);
v___x_1539_ = lean_box(0);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1539_);
v___x_1541_ = v___x_1524_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
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
else
{
lean_object* v___x_1544_; 
lean_dec(v___x_1527_);
lean_del_object(v___x_1524_);
lean_inc_ref(v_type_1513_);
v___x_1544_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1575_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1575_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1575_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___y_1550_; 
if (lean_obj_tag(v_a_1545_) == 0)
{
lean_object* v___x_1570_; 
lean_del_object(v___x_1547_);
v___x_1570_ = lean_box(4);
v___y_1550_ = v___x_1570_;
goto v___jp_1549_;
}
else
{
lean_object* v_val_1571_; lean_object* v___x_1573_; 
v_val_1571_ = lean_ctor_get(v_a_1545_, 0);
lean_inc(v_val_1571_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v_val_1571_);
v___x_1573_ = v___x_1547_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_val_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
v___y_1550_ = v___x_1573_;
goto v___jp_1549_;
}
}
v___jp_1549_:
{
lean_object* v___f_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___f_1551_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1551_, 0, v_type_1513_);
lean_closure_set(v___f_1551_, 1, v___y_1550_);
v___x_1552_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1553_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1552_, v___f_1551_, v_a_1515_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v___x_1553_, 0);
lean_dec(v_unused_1561_);
v___x_1555_ = v___x_1553_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_dec(v___x_1553_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v_a_1545_);
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1545_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_a_1545_);
v_a_1562_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1553_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1553_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_type_1513_);
return v___x_1544_;
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v_type_1513_);
v_a_1577_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1521_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1521_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___boxed(lean_object* v_type_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(v_type_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(lean_object* v_00_u03b2_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_1595_, v_x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___boxed(lean_object* v_00_u03b2_1598_, lean_object* v_x_1599_, lean_object* v_x_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(v_00_u03b2_1598_, v_x_1599_, v_x_1600_);
lean_dec_ref(v_x_1600_);
lean_dec_ref(v_x_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1(lean_object* v_00_u03b2_1602_, lean_object* v_x_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_x_1603_, v_x_1604_, v_x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1607_, lean_object* v_x_1608_, size_t v_x_1609_, lean_object* v_x_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_1608_, v_x_1609_, v_x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
size_t v_x_2581__boxed_1616_; lean_object* v_res_1617_; 
v_x_2581__boxed_1616_ = lean_unbox_usize(v_x_1614_);
lean_dec(v_x_1614_);
v_res_1617_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(v_00_u03b2_1612_, v_x_1613_, v_x_2581__boxed_1616_, v_x_1615_);
lean_dec_ref(v_x_1615_);
lean_dec_ref(v_x_1613_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(lean_object* v_00_u03b2_1618_, lean_object* v_x_1619_, size_t v_x_1620_, size_t v_x_1621_, lean_object* v_x_1622_, lean_object* v_x_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_1619_, v_x_1620_, v_x_1621_, v_x_1622_, v_x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_){
_start:
{
size_t v_x_2592__boxed_1631_; size_t v_x_2593__boxed_1632_; lean_object* v_res_1633_; 
v_x_2592__boxed_1631_ = lean_unbox_usize(v_x_1627_);
lean_dec(v_x_1627_);
v_x_2593__boxed_1632_ = lean_unbox_usize(v_x_1628_);
lean_dec(v_x_1628_);
v_res_1633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(v_00_u03b2_1625_, v_x_1626_, v_x_2592__boxed_1631_, v_x_2593__boxed_1632_, v_x_1629_, v_x_1630_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1634_, lean_object* v_keys_1635_, lean_object* v_vals_1636_, lean_object* v_heq_1637_, lean_object* v_i_1638_, lean_object* v_k_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1635_, v_vals_1636_, v_i_1638_, v_k_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1641_, lean_object* v_keys_1642_, lean_object* v_vals_1643_, lean_object* v_heq_1644_, lean_object* v_i_1645_, lean_object* v_k_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1641_, v_keys_1642_, v_vals_1643_, v_heq_1644_, v_i_1645_, v_k_1646_);
lean_dec_ref(v_k_1646_);
lean_dec_ref(v_vals_1643_);
lean_dec_ref(v_keys_1642_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1648_, lean_object* v_n_1649_, lean_object* v_k_1650_, lean_object* v_v_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v_n_1649_, v_k_1650_, v_v_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1653_, size_t v_depth_1654_, lean_object* v_keys_1655_, lean_object* v_vals_1656_, lean_object* v_heq_1657_, lean_object* v_i_1658_, lean_object* v_entries_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_1654_, v_keys_1655_, v_vals_1656_, v_i_1658_, v_entries_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1661_, lean_object* v_depth_1662_, lean_object* v_keys_1663_, lean_object* v_vals_1664_, lean_object* v_heq_1665_, lean_object* v_i_1666_, lean_object* v_entries_1667_){
_start:
{
size_t v_depth_boxed_1668_; lean_object* v_res_1669_; 
v_depth_boxed_1668_ = lean_unbox_usize(v_depth_1662_);
lean_dec(v_depth_1662_);
v_res_1669_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1661_, v_depth_boxed_1668_, v_keys_1663_, v_vals_1664_, v_heq_1665_, v_i_1666_, v_entries_1667_);
lean_dec_ref(v_vals_1664_);
lean_dec_ref(v_keys_1663_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_, lean_object* v_x_1673_, lean_object* v_x_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1671_, v_x_1672_, v_x_1673_, v_x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(lean_object* v_val_1676_, lean_object* v___x_1677_, lean_object* v_s_1678_){
_start:
{
lean_object* v_exp_1679_; lean_object* v_rings_1680_; lean_object* v_semirings_1681_; lean_object* v_ncRings_1682_; lean_object* v_ncSemirings_1683_; lean_object* v_typeClassify_1684_; lean_object* v_orders_1685_; lean_object* v_typeOrderClassify_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_exp_1679_ = lean_ctor_get(v_s_1678_, 0);
v_rings_1680_ = lean_ctor_get(v_s_1678_, 1);
v_semirings_1681_ = lean_ctor_get(v_s_1678_, 2);
v_ncRings_1682_ = lean_ctor_get(v_s_1678_, 3);
v_ncSemirings_1683_ = lean_ctor_get(v_s_1678_, 4);
v_typeClassify_1684_ = lean_ctor_get(v_s_1678_, 5);
v_orders_1685_ = lean_ctor_get(v_s_1678_, 6);
v_typeOrderClassify_1686_ = lean_ctor_get(v_s_1678_, 7);
v___x_1687_ = lean_array_get_size(v_rings_1680_);
v___x_1688_ = lean_nat_dec_lt(v_val_1676_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_dec(v___x_1677_);
return v_s_1678_;
}
else
{
lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1716_; 
lean_inc_ref(v_typeOrderClassify_1686_);
lean_inc_ref(v_orders_1685_);
lean_inc_ref(v_typeClassify_1684_);
lean_inc_ref(v_ncSemirings_1683_);
lean_inc_ref(v_ncRings_1682_);
lean_inc_ref(v_semirings_1681_);
lean_inc_ref(v_rings_1680_);
lean_inc(v_exp_1679_);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_s_1678_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; lean_object* v_unused_1718_; lean_object* v_unused_1719_; lean_object* v_unused_1720_; lean_object* v_unused_1721_; lean_object* v_unused_1722_; lean_object* v_unused_1723_; lean_object* v_unused_1724_; 
v_unused_1717_ = lean_ctor_get(v_s_1678_, 7);
lean_dec(v_unused_1717_);
v_unused_1718_ = lean_ctor_get(v_s_1678_, 6);
lean_dec(v_unused_1718_);
v_unused_1719_ = lean_ctor_get(v_s_1678_, 5);
lean_dec(v_unused_1719_);
v_unused_1720_ = lean_ctor_get(v_s_1678_, 4);
lean_dec(v_unused_1720_);
v_unused_1721_ = lean_ctor_get(v_s_1678_, 3);
lean_dec(v_unused_1721_);
v_unused_1722_ = lean_ctor_get(v_s_1678_, 2);
lean_dec(v_unused_1722_);
v_unused_1723_ = lean_ctor_get(v_s_1678_, 1);
lean_dec(v_unused_1723_);
v_unused_1724_ = lean_ctor_get(v_s_1678_, 0);
lean_dec(v_unused_1724_);
v___x_1690_ = v_s_1678_;
v_isShared_1691_ = v_isSharedCheck_1716_;
goto v_resetjp_1689_;
}
else
{
lean_dec(v_s_1678_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1716_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v_v_1692_; lean_object* v_toRing_1693_; lean_object* v_invFn_x3f_1694_; lean_object* v_divFn_x3f_1695_; lean_object* v_commSemiringInst_1696_; lean_object* v_commRingInst_1697_; lean_object* v_noZeroDivInst_x3f_1698_; lean_object* v_fieldInst_x3f_1699_; lean_object* v_powIdentityInst_x3f_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1714_; 
v_v_1692_ = lean_array_fget(v_rings_1680_, v_val_1676_);
v_toRing_1693_ = lean_ctor_get(v_v_1692_, 0);
v_invFn_x3f_1694_ = lean_ctor_get(v_v_1692_, 1);
v_divFn_x3f_1695_ = lean_ctor_get(v_v_1692_, 2);
v_commSemiringInst_1696_ = lean_ctor_get(v_v_1692_, 4);
v_commRingInst_1697_ = lean_ctor_get(v_v_1692_, 5);
v_noZeroDivInst_x3f_1698_ = lean_ctor_get(v_v_1692_, 6);
v_fieldInst_x3f_1699_ = lean_ctor_get(v_v_1692_, 7);
v_powIdentityInst_x3f_1700_ = lean_ctor_get(v_v_1692_, 8);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_v_1692_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v_v_1692_, 3);
lean_dec(v_unused_1715_);
v___x_1702_ = v_v_1692_;
v_isShared_1703_ = v_isSharedCheck_1714_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1700_);
lean_inc(v_fieldInst_x3f_1699_);
lean_inc(v_noZeroDivInst_x3f_1698_);
lean_inc(v_commRingInst_1697_);
lean_inc(v_commSemiringInst_1696_);
lean_inc(v_divFn_x3f_1695_);
lean_inc(v_invFn_x3f_1694_);
lean_inc(v_toRing_1693_);
lean_dec(v_v_1692_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1714_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v_xs_x27_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1704_ = lean_box(0);
v_xs_x27_1705_ = lean_array_fset(v_rings_1680_, v_val_1676_, v___x_1704_);
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1677_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 3, v___x_1706_);
v___x_1708_ = v___x_1702_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_toRing_1693_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_invFn_x3f_1694_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_divFn_x3f_1695_);
lean_ctor_set(v_reuseFailAlloc_1713_, 3, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1713_, 4, v_commSemiringInst_1696_);
lean_ctor_set(v_reuseFailAlloc_1713_, 5, v_commRingInst_1697_);
lean_ctor_set(v_reuseFailAlloc_1713_, 6, v_noZeroDivInst_x3f_1698_);
lean_ctor_set(v_reuseFailAlloc_1713_, 7, v_fieldInst_x3f_1699_);
lean_ctor_set(v_reuseFailAlloc_1713_, 8, v_powIdentityInst_x3f_1700_);
v___x_1708_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1709_ = lean_array_fset(v_xs_x27_1705_, v_val_1676_, v___x_1708_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 1, v___x_1709_);
v___x_1711_ = v___x_1690_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_exp_1679_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_semirings_1681_);
lean_ctor_set(v_reuseFailAlloc_1712_, 3, v_ncRings_1682_);
lean_ctor_set(v_reuseFailAlloc_1712_, 4, v_ncSemirings_1683_);
lean_ctor_set(v_reuseFailAlloc_1712_, 5, v_typeClassify_1684_);
lean_ctor_set(v_reuseFailAlloc_1712_, 6, v_orders_1685_);
lean_ctor_set(v_reuseFailAlloc_1712_, 7, v_typeOrderClassify_1686_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0___boxed(lean_object* v_val_1725_, lean_object* v___x_1726_, lean_object* v_s_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(v_val_1725_, v___x_1726_, v_s_1727_);
lean_dec(v_val_1725_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(lean_object* v___x_1729_, lean_object* v_s_1730_){
_start:
{
lean_object* v_exp_1731_; lean_object* v_rings_1732_; lean_object* v_semirings_1733_; lean_object* v_ncRings_1734_; lean_object* v_ncSemirings_1735_; lean_object* v_typeClassify_1736_; lean_object* v_orders_1737_; lean_object* v_typeOrderClassify_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1746_; 
v_exp_1731_ = lean_ctor_get(v_s_1730_, 0);
v_rings_1732_ = lean_ctor_get(v_s_1730_, 1);
v_semirings_1733_ = lean_ctor_get(v_s_1730_, 2);
v_ncRings_1734_ = lean_ctor_get(v_s_1730_, 3);
v_ncSemirings_1735_ = lean_ctor_get(v_s_1730_, 4);
v_typeClassify_1736_ = lean_ctor_get(v_s_1730_, 5);
v_orders_1737_ = lean_ctor_get(v_s_1730_, 6);
v_typeOrderClassify_1738_ = lean_ctor_get(v_s_1730_, 7);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_s_1730_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1740_ = v_s_1730_;
v_isShared_1741_ = v_isSharedCheck_1746_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_typeOrderClassify_1738_);
lean_inc(v_orders_1737_);
lean_inc(v_typeClassify_1736_);
lean_inc(v_ncSemirings_1735_);
lean_inc(v_ncRings_1734_);
lean_inc(v_semirings_1733_);
lean_inc(v_rings_1732_);
lean_inc(v_exp_1731_);
lean_dec(v_s_1730_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1746_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1742_ = lean_array_push(v_semirings_1733_, v___x_1729_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 2, v___x_1742_);
v___x_1744_ = v___x_1740_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_exp_1731_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_rings_1732_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_ncRings_1734_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v_ncSemirings_1735_);
lean_ctor_set(v_reuseFailAlloc_1745_, 5, v_typeClassify_1736_);
lean_ctor_set(v_reuseFailAlloc_1745_, 6, v_orders_1737_);
lean_ctor_set(v_reuseFailAlloc_1745_, 7, v_typeOrderClassify_1738_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0));
v___x_1749_ = l_Lean_stringToMessageData(v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(lean_object* v_type_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v___x_1761_; 
lean_inc_ref(v_type_1750_);
v___x_1761_ = l_Lean_Meta_getDecLevel(v_type_1750_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc_n(v_a_1762_, 2);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1763_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18));
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_a_1762_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
lean_inc_ref(v___x_1765_);
v___x_1766_ = l_Lean_mkConst(v___x_1763_, v___x_1765_);
lean_inc_ref(v_type_1750_);
v___x_1767_ = l_Lean_Expr_app___override(v___x_1766_, v_type_1750_);
v___x_1768_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1767_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1881_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1881_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1881_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
if (lean_obj_tag(v_a_1769_) == 1)
{
lean_object* v_val_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_del_object(v___x_1771_);
v_val_1773_ = lean_ctor_get(v_a_1769_, 0);
lean_inc_n(v_val_1773_, 2);
lean_dec_ref_known(v_a_1769_, 1);
v___x_1774_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2));
lean_inc_ref(v___x_1765_);
v___x_1775_ = l_Lean_mkConst(v___x_1774_, v___x_1765_);
lean_inc_ref_n(v_type_1750_, 2);
v___x_1776_ = l_Lean_mkAppB(v___x_1775_, v_type_1750_, v_val_1773_);
v___x_1777_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1));
v___x_1778_ = l_Lean_mkConst(v___x_1777_, v___x_1765_);
lean_inc_ref(v___x_1776_);
v___x_1779_ = l_Lean_mkAppB(v___x_1778_, v_type_1750_, v___x_1776_);
v___x_1780_ = l_Lean_Meta_Sym_canon(v___x_1779_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1782_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v___x_1782_ = l_Lean_Meta_Sym_shareCommon(v_a_1781_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc_n(v_a_1783_, 2);
lean_dec_ref_known(v___x_1782_, 1);
v___x_1784_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(v_a_1783_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
if (lean_obj_tag(v_a_1785_) == 1)
{
lean_object* v_val_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1837_; 
lean_dec(v_a_1783_);
v_val_1786_ = lean_ctor_get(v_a_1785_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_a_1785_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1788_ = v_a_1785_;
v_isShared_1789_ = v_isSharedCheck_1837_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_val_1786_);
lean_dec(v_a_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1837_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1752_, v_a_1755_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v_semirings_1792_; lean_object* v___x_1793_; lean_object* v___f_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___f_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v_semirings_1792_ = lean_ctor_get(v_a_1791_, 2);
lean_inc_ref(v_semirings_1792_);
lean_dec(v_a_1791_);
v___x_1793_ = lean_array_get_size(v_semirings_1792_);
lean_dec_ref(v_semirings_1792_);
lean_inc(v_val_1786_);
v___f_1794_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1794_, 0, v_val_1786_);
lean_closure_set(v___f_1794_, 1, v___x_1793_);
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1793_);
lean_ctor_set(v___x_1796_, 1, v_type_1750_);
lean_ctor_set(v___x_1796_, 2, v_a_1762_);
lean_ctor_set(v___x_1796_, 3, v___x_1776_);
lean_ctor_set(v___x_1796_, 4, v___x_1795_);
lean_ctor_set(v___x_1796_, 5, v___x_1795_);
lean_ctor_set(v___x_1796_, 6, v___x_1795_);
lean_ctor_set(v___x_1796_, 7, v___x_1795_);
lean_ctor_set(v___x_1796_, 8, v___x_1795_);
v___x_1797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v_val_1786_);
lean_ctor_set(v___x_1797_, 2, v_val_1773_);
lean_ctor_set(v___x_1797_, 3, v___x_1795_);
lean_ctor_set(v___x_1797_, 4, v___x_1795_);
v___f_1798_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1), 2, 1);
lean_closure_set(v___f_1798_, 0, v___x_1797_);
v___x_1799_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1800_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1799_, v___f_1798_, v_a_1752_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v___x_1801_; 
lean_dec_ref_known(v___x_1800_, 1);
v___x_1801_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1799_, v___f_1794_, v_a_1752_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1811_; 
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1811_ == 0)
{
lean_object* v_unused_1812_; 
v_unused_1812_ = lean_ctor_get(v___x_1801_, 0);
lean_dec(v_unused_1812_);
v___x_1803_ = v___x_1801_;
v_isShared_1804_ = v_isSharedCheck_1811_;
goto v_resetjp_1802_;
}
else
{
lean_dec(v___x_1801_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1811_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1793_);
v___x_1806_ = v___x_1788_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1793_);
v___x_1806_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1808_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1806_);
v___x_1808_ = v___x_1803_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_del_object(v___x_1788_);
v_a_1813_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1801_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1801_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec_ref(v___f_1794_);
lean_del_object(v___x_1788_);
v_a_1821_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1800_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1800_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_del_object(v___x_1788_);
lean_dec(v_val_1786_);
lean_dec_ref(v___x_1776_);
lean_dec(v_val_1773_);
lean_dec(v_a_1762_);
lean_dec_ref(v_type_1750_);
v_a_1829_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1790_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1790_);
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
}
else
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec(v_a_1785_);
lean_dec_ref(v___x_1776_);
lean_dec(v_val_1773_);
lean_dec(v_a_1762_);
lean_dec_ref(v_type_1750_);
v___x_1838_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1);
v___x_1839_ = l_Lean_indentExpr(v_a_1783_);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1751_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; uint8_t v_verbose_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v_verbose_1843_ = lean_ctor_get_uint8(v_a_1842_, 0);
lean_dec(v_a_1842_);
if (v_verbose_1843_ == 0)
{
lean_dec_ref_known(v___x_1840_, 2);
goto v___jp_1758_;
}
else
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_Meta_Sym_reportIssue(v___x_1840_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_dec_ref_known(v___x_1844_, 1);
goto v___jp_1758_;
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1844_);
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
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref_known(v___x_1840_, 2);
v_a_1853_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1841_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1841_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
else
{
lean_dec(v_a_1783_);
lean_dec_ref(v___x_1776_);
lean_dec(v_val_1773_);
lean_dec(v_a_1762_);
lean_dec_ref(v_type_1750_);
return v___x_1784_;
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v___x_1776_);
lean_dec(v_val_1773_);
lean_dec(v_a_1762_);
lean_dec_ref(v_type_1750_);
v_a_1861_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1782_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1782_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec_ref(v___x_1776_);
lean_dec(v_val_1773_);
lean_dec(v_a_1762_);
lean_dec_ref(v_type_1750_);
v_a_1869_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1780_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1780_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
lean_dec(v_a_1769_);
lean_dec_ref_known(v___x_1765_, 2);
lean_dec(v_a_1762_);
lean_dec_ref(v_type_1750_);
v___x_1877_ = lean_box(0);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1877_);
v___x_1879_ = v___x_1771_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref_known(v___x_1765_, 2);
lean_dec(v_a_1762_);
lean_dec_ref(v_type_1750_);
v_a_1882_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1768_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1768_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec_ref(v_type_1750_);
v_a_1890_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1761_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1761_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
v___jp_1758_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_box(0);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
return v___x_1760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___boxed(lean_object* v_type_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(v_type_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0(lean_object* v___x_1907_, lean_object* v_s_1908_){
_start:
{
lean_object* v_exp_1909_; lean_object* v_rings_1910_; lean_object* v_semirings_1911_; lean_object* v_ncRings_1912_; lean_object* v_ncSemirings_1913_; lean_object* v_typeClassify_1914_; lean_object* v_orders_1915_; lean_object* v_typeOrderClassify_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1924_; 
v_exp_1909_ = lean_ctor_get(v_s_1908_, 0);
v_rings_1910_ = lean_ctor_get(v_s_1908_, 1);
v_semirings_1911_ = lean_ctor_get(v_s_1908_, 2);
v_ncRings_1912_ = lean_ctor_get(v_s_1908_, 3);
v_ncSemirings_1913_ = lean_ctor_get(v_s_1908_, 4);
v_typeClassify_1914_ = lean_ctor_get(v_s_1908_, 5);
v_orders_1915_ = lean_ctor_get(v_s_1908_, 6);
v_typeOrderClassify_1916_ = lean_ctor_get(v_s_1908_, 7);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_s_1908_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1918_ = v_s_1908_;
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_typeOrderClassify_1916_);
lean_inc(v_orders_1915_);
lean_inc(v_typeClassify_1914_);
lean_inc(v_ncSemirings_1913_);
lean_inc(v_ncRings_1912_);
lean_inc(v_semirings_1911_);
lean_inc(v_rings_1910_);
lean_inc(v_exp_1909_);
lean_dec(v_s_1908_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1920_ = lean_array_push(v_ncSemirings_1913_, v___x_1907_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 4, v___x_1920_);
v___x_1922_ = v___x_1918_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_exp_1909_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_rings_1910_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_semirings_1911_);
lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_ncRings_1912_);
lean_ctor_set(v_reuseFailAlloc_1923_, 4, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1923_, 5, v_typeClassify_1914_);
lean_ctor_set(v_reuseFailAlloc_1923_, 6, v_orders_1915_);
lean_ctor_set(v_reuseFailAlloc_1923_, 7, v_typeOrderClassify_1916_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(lean_object* v_type_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v___x_1932_; 
lean_inc_ref(v_type_1925_);
v___x_1932_ = l_Lean_Meta_getDecLevel(v_type_1925_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc_n(v_a_1933_, 2);
lean_dec_ref_known(v___x_1932_, 1);
v___x_1934_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16));
v___x_1935_ = lean_box(0);
v___x_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1936_, 0, v_a_1933_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = l_Lean_mkConst(v___x_1934_, v___x_1936_);
lean_inc_ref(v_type_1925_);
v___x_1938_ = l_Lean_Expr_app___override(v___x_1937_, v_type_1925_);
v___x_1939_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1938_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1989_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1989_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1989_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
if (lean_obj_tag(v_a_1940_) == 1)
{
lean_object* v_val_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1984_; 
lean_del_object(v___x_1942_);
v_val_1944_ = lean_ctor_get(v_a_1940_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_a_1940_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1946_ = v_a_1940_;
v_isShared_1947_ = v_isSharedCheck_1984_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_val_1944_);
lean_dec(v_a_1940_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1984_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1926_, v_a_1929_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v_ncSemirings_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___f_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1948_, 1);
v_ncSemirings_1950_ = lean_ctor_get(v_a_1949_, 4);
lean_inc_ref(v_ncSemirings_1950_);
lean_dec(v_a_1949_);
v___x_1951_ = lean_array_get_size(v_ncSemirings_1950_);
lean_dec_ref(v_ncSemirings_1950_);
v___x_1952_ = lean_box(0);
v___x_1953_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1951_);
lean_ctor_set(v___x_1953_, 1, v_type_1925_);
lean_ctor_set(v___x_1953_, 2, v_a_1933_);
lean_ctor_set(v___x_1953_, 3, v_val_1944_);
lean_ctor_set(v___x_1953_, 4, v___x_1952_);
lean_ctor_set(v___x_1953_, 5, v___x_1952_);
lean_ctor_set(v___x_1953_, 6, v___x_1952_);
lean_ctor_set(v___x_1953_, 7, v___x_1952_);
lean_ctor_set(v___x_1953_, 8, v___x_1952_);
v___f_1954_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1954_, 0, v___x_1953_);
v___x_1955_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1956_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1955_, v___f_1954_, v_a_1926_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1966_; 
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1966_ == 0)
{
lean_object* v_unused_1967_; 
v_unused_1967_ = lean_ctor_get(v___x_1956_, 0);
lean_dec(v_unused_1967_);
v___x_1958_ = v___x_1956_;
v_isShared_1959_ = v_isSharedCheck_1966_;
goto v_resetjp_1957_;
}
else
{
lean_dec(v___x_1956_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1966_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1951_);
v___x_1961_ = v___x_1946_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1951_);
v___x_1961_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1963_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1961_);
v___x_1963_ = v___x_1958_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_del_object(v___x_1946_);
v_a_1968_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1956_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1956_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_del_object(v___x_1946_);
lean_dec(v_val_1944_);
lean_dec(v_a_1933_);
lean_dec_ref(v_type_1925_);
v_a_1976_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1948_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1948_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
lean_dec(v_a_1940_);
lean_dec(v_a_1933_);
lean_dec_ref(v_type_1925_);
v___x_1985_ = lean_box(0);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1985_);
v___x_1987_ = v___x_1942_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v_a_1933_);
lean_dec_ref(v_type_1925_);
v_a_1990_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1939_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1939_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec_ref(v_type_1925_);
v_a_1998_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1932_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1932_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___boxed(lean_object* v_type_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(lean_object* v_type_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2014_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___boxed(lean_object* v_type_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(v_type_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
lean_dec(v_a_2025_);
lean_dec_ref(v_a_2024_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(lean_object* v_type_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v___x_2040_; 
lean_inc_ref(v_type_2032_);
v___x_2040_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2135_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2135_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2135_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
if (lean_obj_tag(v_a_2041_) == 1)
{
lean_object* v_val_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref(v_type_2032_);
v_val_2045_ = lean_ctor_get(v_a_2041_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_a_2041_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2047_ = v_a_2041_;
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_val_2045_);
lean_dec(v_a_2041_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set_tag(v___x_2047_, 0);
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_val_2045_);
v___x_2050_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2052_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2050_);
v___x_2052_ = v___x_2043_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v___x_2056_; 
lean_del_object(v___x_2043_);
lean_dec(v_a_2041_);
lean_inc_ref(v_type_2032_);
v___x_2056_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(v_type_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2126_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2126_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2126_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
if (lean_obj_tag(v_a_2057_) == 1)
{
lean_object* v_val_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v_type_2032_);
v_val_2061_ = lean_ctor_get(v_a_2057_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_a_2057_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2063_ = v_a_2057_;
v_isShared_2064_ = v_isSharedCheck_2071_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_val_2061_);
lean_dec(v_a_2057_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2071_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_val_2061_);
v___x_2066_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2068_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2066_);
v___x_2068_ = v___x_2059_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_2072_; 
lean_del_object(v___x_2059_);
lean_dec(v_a_2057_);
lean_inc_ref(v_type_2032_);
v___x_2072_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(v_type_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2117_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2117_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2117_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
if (lean_obj_tag(v_a_2073_) == 1)
{
lean_object* v_val_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2087_; 
lean_dec_ref(v_type_2032_);
v_val_2077_ = lean_ctor_get(v_a_2073_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_a_2073_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2079_ = v_a_2073_;
v_isShared_2080_ = v_isSharedCheck_2087_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_val_2077_);
lean_dec(v_a_2073_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2087_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 2);
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_val_2077_);
v___x_2082_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2084_; 
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2082_);
v___x_2084_ = v___x_2075_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
lean_object* v___x_2088_; 
lean_del_object(v___x_2075_);
lean_dec(v_a_2073_);
v___x_2088_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2032_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2108_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2108_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2108_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
if (lean_obj_tag(v_a_2089_) == 1)
{
lean_object* v_val_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2103_; 
v_val_2093_ = lean_ctor_get(v_a_2089_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_a_2089_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2095_ = v_a_2089_;
v_isShared_2096_ = v_isSharedCheck_2103_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_val_2093_);
lean_dec(v_a_2089_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2103_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
lean_ctor_set_tag(v___x_2095_, 3);
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_val_2093_);
v___x_2098_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2100_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2098_);
v___x_2100_ = v___x_2091_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
lean_dec(v_a_2089_);
v___x_2104_ = lean_box(4);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2104_);
v___x_2106_ = v___x_2091_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
v_a_2109_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2088_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2088_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec_ref(v_type_2032_);
v_a_2118_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2072_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2072_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v_type_2032_);
v_a_2127_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2056_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2056_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v_type_2032_);
v_a_2136_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2040_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2040_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go___boxed(lean_object* v_type_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(v_type_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___lam__0(lean_object* v_type_2153_, lean_object* v_a_2154_, lean_object* v_s_2155_){
_start:
{
lean_object* v_exp_2156_; lean_object* v_rings_2157_; lean_object* v_semirings_2158_; lean_object* v_ncRings_2159_; lean_object* v_ncSemirings_2160_; lean_object* v_typeClassify_2161_; lean_object* v_orders_2162_; lean_object* v_typeOrderClassify_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2171_; 
v_exp_2156_ = lean_ctor_get(v_s_2155_, 0);
v_rings_2157_ = lean_ctor_get(v_s_2155_, 1);
v_semirings_2158_ = lean_ctor_get(v_s_2155_, 2);
v_ncRings_2159_ = lean_ctor_get(v_s_2155_, 3);
v_ncSemirings_2160_ = lean_ctor_get(v_s_2155_, 4);
v_typeClassify_2161_ = lean_ctor_get(v_s_2155_, 5);
v_orders_2162_ = lean_ctor_get(v_s_2155_, 6);
v_typeOrderClassify_2163_ = lean_ctor_get(v_s_2155_, 7);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_s_2155_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2165_ = v_s_2155_;
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_typeOrderClassify_2163_);
lean_inc(v_orders_2162_);
lean_inc(v_typeClassify_2161_);
lean_inc(v_ncSemirings_2160_);
lean_inc(v_ncRings_2159_);
lean_inc(v_semirings_2158_);
lean_inc(v_rings_2157_);
lean_inc(v_exp_2156_);
lean_dec(v_s_2155_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2167_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_2161_, v_type_2153_, v_a_2154_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 5, v___x_2167_);
v___x_2169_ = v___x_2165_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_exp_2156_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_rings_2157_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_semirings_2158_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v_ncRings_2159_);
lean_ctor_set(v_reuseFailAlloc_2170_, 4, v_ncSemirings_2160_);
lean_ctor_set(v_reuseFailAlloc_2170_, 5, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2170_, 6, v_orders_2162_);
lean_ctor_set(v_reuseFailAlloc_2170_, 7, v_typeOrderClassify_2163_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f(lean_object* v_type_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2174_, v_a_2177_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2212_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2212_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2212_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v_typeClassify_2185_; lean_object* v___x_2186_; 
v_typeClassify_2185_ = lean_ctor_get(v_a_2181_, 5);
lean_inc_ref(v_typeClassify_2185_);
lean_dec(v_a_2181_);
v___x_2186_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_2185_, v_type_2172_);
lean_dec_ref(v_typeClassify_2185_);
if (lean_obj_tag(v___x_2186_) == 1)
{
lean_object* v_val_2187_; lean_object* v___x_2189_; 
lean_dec_ref(v_type_2172_);
v_val_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_val_2187_);
lean_dec_ref_known(v___x_2186_, 1);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v_val_2187_);
v___x_2189_ = v___x_2183_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_val_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
else
{
lean_object* v___x_2191_; 
lean_dec(v___x_2186_);
lean_del_object(v___x_2183_);
lean_inc_ref(v_type_2172_);
v___x_2191_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(v_type_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___f_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc_n(v_a_2192_, 2);
lean_dec_ref_known(v___x_2191_, 1);
v___f_2193_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_classify_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2193_, 0, v_type_2172_);
lean_closure_set(v___f_2193_, 1, v_a_2192_);
v___x_2194_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2195_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2194_, v___f_2193_, v_a_2174_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; 
v_unused_2203_ = lean_ctor_get(v___x_2195_, 0);
lean_dec(v_unused_2203_);
v___x_2197_ = v___x_2195_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_dec(v___x_2195_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v_a_2192_);
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2192_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v_a_2192_);
v_a_2204_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2195_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2195_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_dec_ref(v_type_2172_);
return v___x_2191_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref(v_type_2172_);
v_a_2213_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2180_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2180_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___boxed(lean_object* v_type_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_Meta_Sym_Arith_classify_x3f(v_type_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(lean_object* v_fn_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_Meta_Sym_canon(v_fn_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2240_ = l_Lean_Meta_Sym_shareCommon(v_a_2239_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
return v___x_2240_;
}
else
{
return v___x_2238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn___boxed(lean_object* v_fn_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(v_fn_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(lean_object* v_u_2255_, lean_object* v_type_2256_, lean_object* v_semiringInst_2257_, lean_object* v_leInst_2258_, lean_object* v_ltInst_2259_, lean_object* v_isPreorderInst_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2267_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_2268_ = lean_box(0);
v___x_2269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2269_, 0, v_u_2255_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = l_Lean_mkConst(v___x_2267_, v___x_2269_);
v___x_2271_ = l_Lean_mkApp5(v___x_2270_, v_type_2256_, v_semiringInst_2257_, v_leInst_2258_, v_ltInst_2259_, v_isPreorderInst_2260_);
v___x_2272_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2271_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_2273_, lean_object* v_type_2274_, lean_object* v_semiringInst_2275_, lean_object* v_leInst_2276_, lean_object* v_ltInst_2277_, lean_object* v_isPreorderInst_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_u_2273_, v_type_2274_, v_semiringInst_2275_, v_leInst_2276_, v_ltInst_2277_, v_isPreorderInst_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
lean_dec(v_a_2281_);
lean_dec_ref(v_a_2280_);
lean_dec(v_a_2279_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f(lean_object* v_u_2286_, lean_object* v_type_2287_, lean_object* v_semiringInst_2288_, lean_object* v_leInst_2289_, lean_object* v_ltInst_2290_, lean_object* v_isPreorderInst_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_u_2286_, v_type_2287_, v_semiringInst_2288_, v_leInst_2289_, v_ltInst_2290_, v_isPreorderInst_2291_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___boxed(lean_object* v_u_2300_, lean_object* v_type_2301_, lean_object* v_semiringInst_2302_, lean_object* v_leInst_2303_, lean_object* v_ltInst_2304_, lean_object* v_isPreorderInst_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f(v_u_2300_, v_type_2301_, v_semiringInst_2302_, v_leInst_2303_, v_ltInst_2304_, v_isPreorderInst_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f_spec__0(lean_object* v_msg_2314_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = l_Lean_instInhabitedExpr;
v___x_2316_ = lean_panic_fn_borrowed(v___x_2315_, v_msg_2314_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___lam__0(lean_object* v___x_2317_, lean_object* v_s_2318_){
_start:
{
lean_object* v_exp_2319_; lean_object* v_rings_2320_; lean_object* v_semirings_2321_; lean_object* v_ncRings_2322_; lean_object* v_ncSemirings_2323_; lean_object* v_typeClassify_2324_; lean_object* v_orders_2325_; lean_object* v_typeOrderClassify_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2334_; 
v_exp_2319_ = lean_ctor_get(v_s_2318_, 0);
v_rings_2320_ = lean_ctor_get(v_s_2318_, 1);
v_semirings_2321_ = lean_ctor_get(v_s_2318_, 2);
v_ncRings_2322_ = lean_ctor_get(v_s_2318_, 3);
v_ncSemirings_2323_ = lean_ctor_get(v_s_2318_, 4);
v_typeClassify_2324_ = lean_ctor_get(v_s_2318_, 5);
v_orders_2325_ = lean_ctor_get(v_s_2318_, 6);
v_typeOrderClassify_2326_ = lean_ctor_get(v_s_2318_, 7);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_s_2318_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2328_ = v_s_2318_;
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_typeOrderClassify_2326_);
lean_inc(v_orders_2325_);
lean_inc(v_typeClassify_2324_);
lean_inc(v_ncSemirings_2323_);
lean_inc(v_ncRings_2322_);
lean_inc(v_semirings_2321_);
lean_inc(v_rings_2320_);
lean_inc(v_exp_2319_);
lean_dec(v_s_2318_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2330_ = lean_array_push(v_orders_2325_, v___x_2317_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 6, v___x_2330_);
v___x_2332_ = v___x_2328_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_exp_2319_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_rings_2320_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_semirings_2321_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v_ncRings_2322_);
lean_ctor_set(v_reuseFailAlloc_2333_, 4, v_ncSemirings_2323_);
lean_ctor_set(v_reuseFailAlloc_2333_, 5, v_typeClassify_2324_);
lean_ctor_set(v_reuseFailAlloc_2333_, 6, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2333_, 7, v_typeOrderClassify_2326_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(lean_object* v_type_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2357_ = l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default;
v___x_2358_ = l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
v___x_2359_ = l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default;
v___x_2360_ = l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
lean_inc_ref(v_type_2349_);
v___x_2361_ = l_Lean_Meta_getDecLevel_x3f(v_type_2349_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2701_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2701_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2701_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
if (lean_obj_tag(v_a_2362_) == 1)
{
lean_object* v_val_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2696_; 
lean_del_object(v___x_2364_);
v_val_2366_ = lean_ctor_get(v_a_2362_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_a_2362_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2368_ = v_a_2362_;
v_isShared_2369_ = v_isSharedCheck_2696_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_val_2366_);
lean_dec(v_a_2362_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2696_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1));
v___x_2371_ = lean_box(0);
lean_inc(v_val_2366_);
v___x_2372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2372_, 0, v_val_2366_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
lean_inc_ref(v___x_2372_);
v___x_2373_ = l_Lean_mkConst(v___x_2370_, v___x_2372_);
lean_inc_ref(v_type_2349_);
v___x_2374_ = l_Lean_Expr_app___override(v___x_2373_, v_type_2349_);
v___x_2375_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2374_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2687_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2687_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2687_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
if (lean_obj_tag(v_a_2376_) == 1)
{
lean_object* v_val_2380_; lean_object* v___x_2381_; 
lean_del_object(v___x_2378_);
v_val_2380_ = lean_ctor_get(v_a_2376_, 0);
lean_inc(v_val_2380_);
lean_inc_ref(v_a_2376_);
lean_inc_ref(v_type_2349_);
lean_inc(v_val_2366_);
v___x_2381_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_val_2366_, v_type_2349_, v_a_2376_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2674_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2674_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2674_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
if (lean_obj_tag(v_a_2382_) == 1)
{
lean_object* v_val_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2669_; 
lean_del_object(v___x_2384_);
v_val_2386_ = lean_ctor_get(v_a_2382_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v_a_2382_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2388_ = v_a_2382_;
v_isShared_2389_ = v_isSharedCheck_2669_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_val_2386_);
lean_dec(v_a_2382_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2669_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; 
lean_inc_ref(v_a_2376_);
lean_inc_ref(v_type_2349_);
lean_inc(v_val_2366_);
v___x_2390_ = l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(v_val_2366_, v_type_2349_, v_a_2376_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2392_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
lean_inc_ref(v_a_2376_);
lean_inc_ref(v_type_2349_);
lean_inc(v_val_2366_);
v___x_2392_ = l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f(v_val_2366_, v_type_2349_, v_a_2376_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2394_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3));
lean_inc_ref(v___x_2372_);
v___x_2395_ = l_Lean_mkConst(v___x_2394_, v___x_2372_);
lean_inc_ref(v_type_2349_);
v___x_2396_ = l_Lean_Expr_app___override(v___x_2395_, v_type_2349_);
v___x_2397_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2396_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref_known(v___x_2397_, 1);
v___x_2399_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5));
lean_inc_ref(v___x_2372_);
v___x_2400_ = l_Lean_mkConst(v___x_2399_, v___x_2372_);
lean_inc(v_val_2380_);
lean_inc_ref(v_type_2349_);
v___x_2401_ = l_Lean_mkAppB(v___x_2400_, v_type_2349_, v_val_2380_);
v___x_2402_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(v___x_2401_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v_fst_2407_; lean_object* v_fst_2408_; uint8_t v_fst_2409_; lean_object* v_fst_2410_; lean_object* v_fst_2411_; uint8_t v_snd_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v_fst_2451_; lean_object* v_snd_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2402_, 1);
if (lean_obj_tag(v_a_2398_) == 1)
{
lean_object* v_val_2458_; lean_object* v___x_2459_; 
v_val_2458_ = lean_ctor_get(v_a_2398_, 0);
lean_inc_ref(v_a_2398_);
lean_inc_ref(v_type_2349_);
lean_inc(v_val_2366_);
v___x_2459_ = l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(v_val_2366_, v_type_2349_, v_a_2398_, v_a_2376_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
if (lean_obj_tag(v_a_2460_) == 0)
{
lean_dec_ref_known(v___x_2372_, 2);
lean_del_object(v___x_2368_);
v_fst_2451_ = v_a_2460_;
v_snd_2452_ = v_a_2460_;
v___y_2453_ = v_a_2351_;
v___y_2454_ = v_a_2354_;
goto v___jp_2450_;
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2461_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7));
v___x_2462_ = l_Lean_mkConst(v___x_2461_, v___x_2372_);
lean_inc(v_val_2458_);
lean_inc_ref(v_type_2349_);
v___x_2463_ = l_Lean_mkAppB(v___x_2462_, v_type_2349_, v_val_2458_);
v___x_2464_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(v___x_2463_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2467_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2464_, 1);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v_a_2465_);
v___x_2467_ = v___x_2368_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2465_);
v___x_2467_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
uint8_t v___x_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; 
v___x_2468_ = 0;
v___x_2469_ = 1;
lean_inc_ref(v_type_2349_);
v___x_2470_ = l_Lean_Meta_Sym_Arith_classify_x3f(v_type_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2470_, 1);
switch(lean_obj_tag(v_a_2471_))
{
case 0:
{
lean_object* v_id_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2507_; 
v_id_2472_ = lean_ctor_get(v_a_2471_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_a_2471_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2474_ = v_a_2471_;
v_isShared_2475_ = v_isSharedCheck_2507_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_id_2472_);
lean_dec(v_a_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2507_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2351_, v_a_2354_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v_rings_2478_; lean_object* v___x_2479_; lean_object* v_toRing_2480_; lean_object* v_ringInst_2481_; lean_object* v_semiringInst_2482_; lean_object* v___x_2483_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2476_, 1);
v_rings_2478_ = lean_ctor_get(v_a_2477_, 1);
lean_inc_ref(v_rings_2478_);
lean_dec(v_a_2477_);
v___x_2479_ = lean_array_get(v___x_2357_, v_rings_2478_, v_id_2472_);
lean_dec_ref(v_rings_2478_);
v_toRing_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc_ref(v_toRing_2480_);
lean_dec(v___x_2479_);
v_ringInst_2481_ = lean_ctor_get(v_toRing_2480_, 3);
lean_inc_ref(v_ringInst_2481_);
v_semiringInst_2482_ = lean_ctor_get(v_toRing_2480_, 4);
lean_inc_ref(v_semiringInst_2482_);
lean_dec_ref(v_toRing_2480_);
lean_inc(v_val_2386_);
lean_inc(v_val_2458_);
lean_inc(v_val_2380_);
lean_inc_ref(v_type_2349_);
lean_inc(v_val_2366_);
v___x_2483_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2366_, v_type_2349_, v_semiringInst_2482_, v_val_2380_, v_val_2458_, v_val_2386_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
if (lean_obj_tag(v_a_2484_) == 1)
{
lean_object* v___x_2486_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set_tag(v___x_2474_, 1);
v___x_2486_ = v___x_2474_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_id_2472_);
v___x_2486_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = lean_box(0);
v___x_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_ringInst_2481_);
v___y_2405_ = v___x_2467_;
v___y_2406_ = v_a_2460_;
v_fst_2407_ = v___x_2486_;
v_fst_2408_ = v___x_2487_;
v_fst_2409_ = v___x_2469_;
v_fst_2410_ = v___x_2488_;
v_fst_2411_ = v_a_2484_;
v_snd_2412_ = v___x_2469_;
v___y_2413_ = v_a_2351_;
v___y_2414_ = v_a_2354_;
goto v___jp_2404_;
}
}
else
{
lean_object* v___x_2490_; 
lean_dec(v_a_2484_);
lean_dec_ref(v_ringInst_2481_);
lean_del_object(v___x_2474_);
lean_dec(v_id_2472_);
v___x_2490_ = lean_box(0);
v___y_2405_ = v___x_2467_;
v___y_2406_ = v_a_2460_;
v_fst_2407_ = v___x_2490_;
v_fst_2408_ = v___x_2490_;
v_fst_2409_ = v___x_2469_;
v_fst_2410_ = v___x_2490_;
v_fst_2411_ = v___x_2490_;
v_snd_2412_ = v___x_2469_;
v___y_2413_ = v_a_2351_;
v___y_2414_ = v_a_2354_;
goto v___jp_2404_;
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v_ringInst_2481_);
lean_del_object(v___x_2474_);
lean_dec(v_id_2472_);
lean_dec_ref(v___x_2467_);
lean_dec_ref_known(v_a_2460_, 1);
lean_dec_ref_known(v_a_2398_, 1);
lean_dec(v_a_2403_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2491_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2483_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2483_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_del_object(v___x_2474_);
lean_dec(v_id_2472_);
lean_dec_ref(v___x_2467_);
lean_dec_ref_known(v_a_2460_, 1);
lean_dec_ref_known(v_a_2398_, 1);
lean_dec(v_a_2403_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2499_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2476_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2476_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
case 1:
{
lean_object* v_id_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2542_; 
v_id_2508_ = lean_ctor_get(v_a_2471_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_a_2471_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2510_ = v_a_2471_;
v_isShared_2511_ = v_isSharedCheck_2542_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_id_2508_);
lean_dec(v_a_2471_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2542_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2351_, v_a_2354_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v_ncRings_2514_; lean_object* v___x_2515_; lean_object* v_ringInst_2516_; lean_object* v_semiringInst_2517_; lean_object* v___x_2518_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
v_ncRings_2514_ = lean_ctor_get(v_a_2513_, 3);
lean_inc_ref(v_ncRings_2514_);
lean_dec(v_a_2513_);
v___x_2515_ = lean_array_get(v___x_2358_, v_ncRings_2514_, v_id_2508_);
lean_dec_ref(v_ncRings_2514_);
v_ringInst_2516_ = lean_ctor_get(v___x_2515_, 3);
lean_inc_ref(v_ringInst_2516_);
v_semiringInst_2517_ = lean_ctor_get(v___x_2515_, 4);
lean_inc_ref(v_semiringInst_2517_);
lean_dec(v___x_2515_);
lean_inc(v_val_2386_);
lean_inc(v_val_2458_);
lean_inc(v_val_2380_);
lean_inc_ref(v_type_2349_);
lean_inc(v_val_2366_);
v___x_2518_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2366_, v_type_2349_, v_semiringInst_2517_, v_val_2380_, v_val_2458_, v_val_2386_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2518_, 1);
if (lean_obj_tag(v_a_2519_) == 1)
{
lean_object* v___x_2521_; 
if (v_isShared_2511_ == 0)
{
v___x_2521_ = v___x_2510_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_id_2508_);
v___x_2521_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_box(0);
v___x_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2523_, 0, v_ringInst_2516_);
v___y_2405_ = v___x_2467_;
v___y_2406_ = v_a_2460_;
v_fst_2407_ = v___x_2521_;
v_fst_2408_ = v___x_2522_;
v_fst_2409_ = v___x_2469_;
v_fst_2410_ = v___x_2523_;
v_fst_2411_ = v_a_2519_;
v_snd_2412_ = v___x_2468_;
v___y_2413_ = v_a_2351_;
v___y_2414_ = v_a_2354_;
goto v___jp_2404_;
}
}
else
{
lean_object* v___x_2525_; 
lean_dec(v_a_2519_);
lean_dec_ref(v_ringInst_2516_);
lean_del_object(v___x_2510_);
lean_dec(v_id_2508_);
v___x_2525_ = lean_box(0);
v___y_2405_ = v___x_2467_;
v___y_2406_ = v_a_2460_;
v_fst_2407_ = v___x_2525_;
v_fst_2408_ = v___x_2525_;
v_fst_2409_ = v___x_2469_;
v_fst_2410_ = v___x_2525_;
v_fst_2411_ = v___x_2525_;
v_snd_2412_ = v___x_2468_;
v___y_2413_ = v_a_2351_;
v___y_2414_ = v_a_2354_;
goto v___jp_2404_;
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec_ref(v_ringInst_2516_);
lean_del_object(v___x_2510_);
lean_dec(v_id_2508_);
lean_dec_ref(v___x_2467_);
lean_dec_ref_known(v_a_2460_, 1);
lean_dec_ref_known(v_a_2398_, 1);
lean_dec(v_a_2403_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2526_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2518_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2518_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_del_object(v___x_2510_);
lean_dec(v_id_2508_);
lean_dec_ref(v___x_2467_);
lean_dec_ref_known(v_a_2460_, 1);
lean_dec_ref_known(v_a_2398_, 1);
lean_dec(v_a_2403_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2534_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2512_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2512_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
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
}
case 2:
{
lean_object* v_id_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2576_; 
v_id_2543_ = lean_ctor_get(v_a_2471_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_a_2471_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2545_ = v_a_2471_;
v_isShared_2546_ = v_isSharedCheck_2576_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_id_2543_);
lean_dec(v_a_2471_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2576_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; 
v___x_2547_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2351_, v_a_2354_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v_semirings_2549_; lean_object* v___x_2550_; lean_object* v_toSemiring_2551_; lean_object* v_semiringInst_2552_; lean_object* v___x_2553_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2547_, 1);
v_semirings_2549_ = lean_ctor_get(v_a_2548_, 2);
lean_inc_ref(v_semirings_2549_);
lean_dec(v_a_2548_);
v___x_2550_ = lean_array_get(v___x_2359_, v_semirings_2549_, v_id_2543_);
lean_dec_ref(v_semirings_2549_);
v_toSemiring_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc_ref(v_toSemiring_2551_);
lean_dec(v___x_2550_);
v_semiringInst_2552_ = lean_ctor_get(v_toSemiring_2551_, 3);
lean_inc_ref(v_semiringInst_2552_);
lean_dec_ref(v_toSemiring_2551_);
lean_inc(v_val_2386_);
lean_inc(v_val_2458_);
lean_inc(v_val_2380_);
lean_inc_ref(v_type_2349_);
lean_inc(v_val_2366_);
v___x_2553_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2366_, v_type_2349_, v_semiringInst_2552_, v_val_2380_, v_val_2458_, v_val_2386_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
if (lean_obj_tag(v_a_2554_) == 1)
{
lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2555_ = lean_box(0);
if (v_isShared_2546_ == 0)
{
lean_ctor_set_tag(v___x_2545_, 1);
v___x_2557_ = v___x_2545_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_id_2543_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
v___y_2405_ = v___x_2467_;
v___y_2406_ = v_a_2460_;
v_fst_2407_ = v___x_2555_;
v_fst_2408_ = v___x_2557_;
v_fst_2409_ = v___x_2469_;
v_fst_2410_ = v___x_2555_;
v_fst_2411_ = v_a_2554_;
v_snd_2412_ = v___x_2468_;
v___y_2413_ = v_a_2351_;
v___y_2414_ = v_a_2354_;
goto v___jp_2404_;
}
}
else
{
lean_object* v___x_2559_; 
lean_dec(v_a_2554_);
lean_del_object(v___x_2545_);
lean_dec(v_id_2543_);
v___x_2559_ = lean_box(0);
v___y_2405_ = v___x_2467_;
v___y_2406_ = v_a_2460_;
v_fst_2407_ = v___x_2559_;
v_fst_2408_ = v___x_2559_;
v_fst_2409_ = v___x_2469_;
v_fst_2410_ = v___x_2559_;
v_fst_2411_ = v___x_2559_;
v_snd_2412_ = v___x_2468_;
v___y_2413_ = v_a_2351_;
v___y_2414_ = v_a_2354_;
goto v___jp_2404_;
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_del_object(v___x_2545_);
lean_dec(v_id_2543_);
lean_dec_ref(v___x_2467_);
lean_dec_ref_known(v_a_2460_, 1);
lean_dec_ref_known(v_a_2398_, 1);
lean_dec(v_a_2403_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2560_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2553_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2553_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_del_object(v___x_2545_);
lean_dec(v_id_2543_);
lean_dec_ref(v___x_2467_);
lean_dec_ref_known(v_a_2460_, 1);
lean_dec_ref_known(v_a_2398_, 1);
lean_dec(v_a_2403_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2568_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2547_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2547_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
case 3:
{
lean_object* v_id_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2609_; 
v_id_2577_ = lean_ctor_get(v_a_2471_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_a_2471_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2579_ = v_a_2471_;
v_isShared_2580_ = v_isSharedCheck_2609_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_id_2577_);
lean_dec(v_a_2471_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2609_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2351_, v_a_2354_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v_ncSemirings_2583_; lean_object* v___x_2584_; lean_object* v_semiringInst_2585_; lean_object* v___x_2586_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v_ncSemirings_2583_ = lean_ctor_get(v_a_2582_, 4);
lean_inc_ref(v_ncSemirings_2583_);
lean_dec(v_a_2582_);
v___x_2584_ = lean_array_get(v___x_2360_, v_ncSemirings_2583_, v_id_2577_);
lean_dec_ref(v_ncSemirings_2583_);
v_semiringInst_2585_ = lean_ctor_get(v___x_2584_, 3);
lean_inc_ref(v_semiringInst_2585_);
lean_dec(v___x_2584_);
lean_inc(v_val_2386_);
lean_inc(v_val_2458_);
lean_inc(v_val_2380_);
lean_inc_ref(v_type_2349_);
lean_inc(v_val_2366_);
v___x_2586_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2366_, v_type_2349_, v_semiringInst_2585_, v_val_2380_, v_val_2458_, v_val_2386_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
if (lean_obj_tag(v_a_2587_) == 1)
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2588_ = lean_box(0);
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 1);
v___x_2590_ = v___x_2579_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_id_2577_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
v___y_2405_ = v___x_2467_;
v___y_2406_ = v_a_2460_;
v_fst_2407_ = v___x_2588_;
v_fst_2408_ = v___x_2590_;
v_fst_2409_ = v___x_2468_;
v_fst_2410_ = v___x_2588_;
v_fst_2411_ = v_a_2587_;
v_snd_2412_ = v___x_2468_;
v___y_2413_ = v_a_2351_;
v___y_2414_ = v_a_2354_;
goto v___jp_2404_;
}
}
else
{
lean_object* v___x_2592_; 
lean_dec(v_a_2587_);
lean_del_object(v___x_2579_);
lean_dec(v_id_2577_);
v___x_2592_ = lean_box(0);
v___y_2405_ = v___x_2467_;
v___y_2406_ = v_a_2460_;
v_fst_2407_ = v___x_2592_;
v_fst_2408_ = v___x_2592_;
v_fst_2409_ = v___x_2469_;
v_fst_2410_ = v___x_2592_;
v_fst_2411_ = v___x_2592_;
v_snd_2412_ = v___x_2468_;
v___y_2413_ = v_a_2351_;
v___y_2414_ = v_a_2354_;
goto v___jp_2404_;
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_del_object(v___x_2579_);
lean_dec(v_id_2577_);
lean_dec_ref(v___x_2467_);
lean_dec_ref_known(v_a_2460_, 1);
lean_dec_ref_known(v_a_2398_, 1);
lean_dec(v_a_2403_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2593_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2586_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2586_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_del_object(v___x_2579_);
lean_dec(v_id_2577_);
lean_dec_ref(v___x_2467_);
lean_dec_ref_known(v_a_2460_, 1);
lean_dec_ref_known(v_a_2398_, 1);
lean_dec(v_a_2403_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2601_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2581_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2581_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
default: 
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_box(0);
v___y_2405_ = v___x_2467_;
v___y_2406_ = v_a_2460_;
v_fst_2407_ = v___x_2610_;
v_fst_2408_ = v___x_2610_;
v_fst_2409_ = v___x_2469_;
v_fst_2410_ = v___x_2610_;
v_fst_2411_ = v___x_2610_;
v_snd_2412_ = v___x_2468_;
v___y_2413_ = v_a_2351_;
v___y_2414_ = v_a_2354_;
goto v___jp_2404_;
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec_ref(v___x_2467_);
lean_dec_ref_known(v_a_2460_, 1);
lean_dec_ref_known(v_a_2398_, 1);
lean_dec(v_a_2403_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2611_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2470_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2470_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref_known(v_a_2460_, 1);
lean_dec_ref_known(v_a_2398_, 1);
lean_dec(v_a_2403_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_del_object(v___x_2368_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2620_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2464_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2464_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec_ref_known(v_a_2398_, 1);
lean_dec(v_a_2403_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec_ref_known(v___x_2372_, 2);
lean_del_object(v___x_2368_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2628_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2459_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2459_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v___x_2636_; 
lean_dec_ref_known(v_a_2376_, 1);
lean_dec_ref_known(v___x_2372_, 2);
lean_del_object(v___x_2368_);
v___x_2636_ = lean_box(0);
v_fst_2451_ = v___x_2636_;
v_snd_2452_ = v___x_2636_;
v___y_2453_ = v_a_2351_;
v___y_2454_ = v_a_2354_;
goto v___jp_2450_;
}
v___jp_2404_:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v_orders_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___f_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v_orders_2417_ = lean_ctor_get(v_a_2416_, 6);
lean_inc_ref(v_orders_2417_);
lean_dec(v_a_2416_);
v___x_2418_ = lean_array_get_size(v_orders_2417_);
lean_dec_ref(v_orders_2417_);
v___x_2419_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
lean_ctor_set(v___x_2419_, 1, v_type_2349_);
lean_ctor_set(v___x_2419_, 2, v_val_2366_);
lean_ctor_set(v___x_2419_, 3, v_val_2386_);
lean_ctor_set(v___x_2419_, 4, v_val_2380_);
lean_ctor_set(v___x_2419_, 5, v_a_2398_);
lean_ctor_set(v___x_2419_, 6, v_a_2391_);
lean_ctor_set(v___x_2419_, 7, v_a_2393_);
lean_ctor_set(v___x_2419_, 8, v___y_2406_);
lean_ctor_set(v___x_2419_, 9, v_fst_2407_);
lean_ctor_set(v___x_2419_, 10, v_fst_2408_);
lean_ctor_set(v___x_2419_, 11, v_fst_2410_);
lean_ctor_set(v___x_2419_, 12, v_fst_2411_);
lean_ctor_set(v___x_2419_, 13, v_a_2403_);
lean_ctor_set(v___x_2419_, 14, v___y_2405_);
lean_ctor_set_uint8(v___x_2419_, sizeof(void*)*15, v_snd_2412_);
lean_ctor_set_uint8(v___x_2419_, sizeof(void*)*15 + 1, v_fst_2409_);
v___f_2420_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___lam__0), 2, 1);
lean_closure_set(v___f_2420_, 0, v___x_2419_);
v___x_2421_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2422_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2421_, v___f_2420_, v___y_2413_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2432_; 
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v___x_2422_, 0);
lean_dec(v_unused_2433_);
v___x_2424_ = v___x_2422_;
v_isShared_2425_ = v_isSharedCheck_2432_;
goto v_resetjp_2423_;
}
else
{
lean_dec(v___x_2422_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2432_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2418_);
v___x_2427_ = v___x_2388_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2418_);
v___x_2427_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2429_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2427_);
v___x_2429_ = v___x_2424_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_del_object(v___x_2388_);
v_a_2434_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2422_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2422_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_fst_2411_);
lean_dec(v_fst_2410_);
lean_dec(v_fst_2408_);
lean_dec(v_fst_2407_);
lean_dec(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec(v_a_2403_);
lean_dec(v_a_2398_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2442_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2415_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2415_);
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
v___jp_2450_:
{
uint8_t v___x_2455_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2455_ = 1;
v___x_2456_ = lean_box(0);
v___x_2457_ = 0;
lean_inc_n(v_fst_2451_, 2);
v___y_2405_ = v_snd_2452_;
v___y_2406_ = v_fst_2451_;
v_fst_2407_ = v___x_2456_;
v_fst_2408_ = v___x_2456_;
v_fst_2409_ = v___x_2455_;
v_fst_2410_ = v_fst_2451_;
v_fst_2411_ = v_fst_2451_;
v_snd_2412_ = v___x_2457_;
v___y_2413_ = v___y_2453_;
v___y_2414_ = v___y_2454_;
goto v___jp_2404_;
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v_a_2398_);
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec_ref_known(v_a_2376_, 1);
lean_dec(v_val_2380_);
lean_dec_ref_known(v___x_2372_, 2);
lean_del_object(v___x_2368_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2637_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2402_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2402_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec_ref_known(v_a_2376_, 1);
lean_dec_ref_known(v___x_2372_, 2);
lean_del_object(v___x_2368_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2645_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2397_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2397_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec(v_a_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec(v_val_2380_);
lean_dec_ref_known(v_a_2376_, 1);
lean_dec_ref_known(v___x_2372_, 2);
lean_del_object(v___x_2368_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2653_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2392_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2392_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_del_object(v___x_2388_);
lean_dec(v_val_2386_);
lean_dec_ref_known(v_a_2376_, 1);
lean_dec(v_val_2380_);
lean_dec_ref_known(v___x_2372_, 2);
lean_del_object(v___x_2368_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2661_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2390_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2390_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2672_; 
lean_dec(v_a_2382_);
lean_dec_ref_known(v_a_2376_, 1);
lean_dec(v_val_2380_);
lean_dec_ref_known(v___x_2372_, 2);
lean_del_object(v___x_2368_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v___x_2670_ = lean_box(0);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2670_);
v___x_2672_ = v___x_2384_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_val_2380_);
lean_dec_ref_known(v_a_2376_, 1);
lean_dec_ref_known(v___x_2372_, 2);
lean_del_object(v___x_2368_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2675_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2381_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2381_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2685_; 
lean_dec(v_a_2376_);
lean_dec_ref_known(v___x_2372_, 2);
lean_del_object(v___x_2368_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v___x_2683_ = lean_box(0);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2683_);
v___x_2685_ = v___x_2378_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec_ref_known(v___x_2372_, 2);
lean_del_object(v___x_2368_);
lean_dec(v_val_2366_);
lean_dec_ref(v_type_2349_);
v_a_2688_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2375_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2375_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
lean_dec(v_a_2362_);
lean_dec_ref(v_type_2349_);
v___x_2697_ = lean_box(0);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2697_);
v___x_2699_ = v___x_2364_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref(v_type_2349_);
v_a_2702_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2361_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2361_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___boxed(lean_object* v_type_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(v_type_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___lam__0(lean_object* v_type_2719_, lean_object* v_a_2720_, lean_object* v_s_2721_){
_start:
{
lean_object* v_exp_2722_; lean_object* v_rings_2723_; lean_object* v_semirings_2724_; lean_object* v_ncRings_2725_; lean_object* v_ncSemirings_2726_; lean_object* v_typeClassify_2727_; lean_object* v_orders_2728_; lean_object* v_typeOrderClassify_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2737_; 
v_exp_2722_ = lean_ctor_get(v_s_2721_, 0);
v_rings_2723_ = lean_ctor_get(v_s_2721_, 1);
v_semirings_2724_ = lean_ctor_get(v_s_2721_, 2);
v_ncRings_2725_ = lean_ctor_get(v_s_2721_, 3);
v_ncSemirings_2726_ = lean_ctor_get(v_s_2721_, 4);
v_typeClassify_2727_ = lean_ctor_get(v_s_2721_, 5);
v_orders_2728_ = lean_ctor_get(v_s_2721_, 6);
v_typeOrderClassify_2729_ = lean_ctor_get(v_s_2721_, 7);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_s_2721_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2731_ = v_s_2721_;
v_isShared_2732_ = v_isSharedCheck_2737_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_typeOrderClassify_2729_);
lean_inc(v_orders_2728_);
lean_inc(v_typeClassify_2727_);
lean_inc(v_ncSemirings_2726_);
lean_inc(v_ncRings_2725_);
lean_inc(v_semirings_2724_);
lean_inc(v_rings_2723_);
lean_inc(v_exp_2722_);
lean_dec(v_s_2721_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2737_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2733_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeOrderClassify_2729_, v_type_2719_, v_a_2720_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 7, v___x_2733_);
v___x_2735_ = v___x_2731_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_exp_2722_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_rings_2723_);
lean_ctor_set(v_reuseFailAlloc_2736_, 2, v_semirings_2724_);
lean_ctor_set(v_reuseFailAlloc_2736_, 3, v_ncRings_2725_);
lean_ctor_set(v_reuseFailAlloc_2736_, 4, v_ncSemirings_2726_);
lean_ctor_set(v_reuseFailAlloc_2736_, 5, v_typeClassify_2727_);
lean_ctor_set(v_reuseFailAlloc_2736_, 6, v_orders_2728_);
lean_ctor_set(v_reuseFailAlloc_2736_, 7, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f(lean_object* v_type_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2740_, v_a_2743_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2778_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2778_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2778_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v_typeOrderClassify_2751_; lean_object* v___x_2752_; 
v_typeOrderClassify_2751_ = lean_ctor_get(v_a_2747_, 7);
lean_inc_ref(v_typeOrderClassify_2751_);
lean_dec(v_a_2747_);
v___x_2752_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeOrderClassify_2751_, v_type_2738_);
lean_dec_ref(v_typeOrderClassify_2751_);
if (lean_obj_tag(v___x_2752_) == 1)
{
lean_object* v_val_2753_; lean_object* v___x_2755_; 
lean_dec_ref(v_type_2738_);
v_val_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_val_2753_);
lean_dec_ref_known(v___x_2752_, 1);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v_val_2753_);
v___x_2755_ = v___x_2749_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_val_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
else
{
lean_object* v___x_2757_; 
lean_dec(v___x_2752_);
lean_del_object(v___x_2749_);
lean_inc_ref(v_type_2738_);
v___x_2757_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(v_type_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___f_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc_n(v_a_2758_, 2);
lean_dec_ref_known(v___x_2757_, 1);
v___f_2759_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_classifyOrder_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2759_, 0, v_type_2738_);
lean_closure_set(v___f_2759_, 1, v_a_2758_);
v___x_2760_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2761_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2760_, v___f_2759_, v_a_2740_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2768_ == 0)
{
lean_object* v_unused_2769_; 
v_unused_2769_ = lean_ctor_get(v___x_2761_, 0);
lean_dec(v_unused_2769_);
v___x_2763_ = v___x_2761_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_dec(v___x_2761_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v_a_2758_);
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2758_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_a_2758_);
v_a_2770_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2761_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2761_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
else
{
lean_dec_ref(v_type_2738_);
return v___x_2757_;
}
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec_ref(v_type_2738_);
v_a_2779_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2746_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2746_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___boxed(lean_object* v_type_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_Meta_Sym_Arith_classifyOrder_x3f(v_type_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
return v_res_2795_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Insts(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Canon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_Insts(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Canon(uint8_t builtin);
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_Classify(builtin);
}
#ifdef __cplusplus
}
#endif
