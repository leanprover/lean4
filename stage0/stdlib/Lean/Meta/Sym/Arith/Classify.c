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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* v___x_57_; lean_object* v_env_58_; uint8_t v___x_59_; lean_object* v_env_60_; lean_object* v___x_61_; lean_object* v_toCold_62_; lean_object* v_mctx_63_; lean_object* v_lctx_64_; lean_object* v_options_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_57_ = lean_st_ref_get(v___y_55_);
v_env_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc_ref(v_env_58_);
lean_dec(v___x_57_);
v___x_59_ = 0;
v_env_60_ = l_Lean_Environment_setRecordingDeps(v_env_58_, v___x_59_);
v___x_61_ = lean_st_ref_get(v___y_53_);
v_toCold_62_ = lean_ctor_get(v___y_54_, 0);
v_mctx_63_ = lean_ctor_get(v___x_61_, 0);
lean_inc_ref(v_mctx_63_);
lean_dec(v___x_61_);
v_lctx_64_ = lean_ctor_get(v___y_52_, 2);
v_options_65_ = lean_ctor_get(v_toCold_62_, 2);
lean_inc_ref(v_options_65_);
lean_inc_ref(v_lctx_64_);
v___x_66_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_66_, 0, v_env_60_);
lean_ctor_set(v___x_66_, 1, v_mctx_63_);
lean_ctor_set(v___x_66_, 2, v_lctx_64_);
lean_ctor_set(v___x_66_, 3, v_options_65_);
v___x_67_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v_msgData_51_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(v_msgData_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
return v_res_75_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_76_; double v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_float_of_nat(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(lean_object* v_cls_81_, lean_object* v_msg_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_ref_88_; lean_object* v___x_89_; lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_135_; 
v_ref_88_ = lean_ctor_get(v___y_85_, 2);
v___x_89_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(v_msg_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
v_a_90_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_135_ == 0)
{
v___x_92_ = v___x_89_;
v_isShared_93_ = v_isSharedCheck_135_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_135_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; lean_object* v_traceState_95_; lean_object* v_env_96_; lean_object* v_nextMacroScope_97_; lean_object* v_ngen_98_; lean_object* v_auxDeclNGen_99_; lean_object* v_cache_100_; lean_object* v_recordedDeps_101_; lean_object* v_messages_102_; lean_object* v_infoState_103_; lean_object* v_snapshotTasks_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_134_; 
v___x_94_ = lean_st_ref_take(v___y_86_);
v_traceState_95_ = lean_ctor_get(v___x_94_, 4);
v_env_96_ = lean_ctor_get(v___x_94_, 0);
v_nextMacroScope_97_ = lean_ctor_get(v___x_94_, 1);
v_ngen_98_ = lean_ctor_get(v___x_94_, 2);
v_auxDeclNGen_99_ = lean_ctor_get(v___x_94_, 3);
v_cache_100_ = lean_ctor_get(v___x_94_, 5);
v_recordedDeps_101_ = lean_ctor_get(v___x_94_, 6);
v_messages_102_ = lean_ctor_get(v___x_94_, 7);
v_infoState_103_ = lean_ctor_get(v___x_94_, 8);
v_snapshotTasks_104_ = lean_ctor_get(v___x_94_, 9);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_134_ == 0)
{
v___x_106_ = v___x_94_;
v_isShared_107_ = v_isSharedCheck_134_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_snapshotTasks_104_);
lean_inc(v_infoState_103_);
lean_inc(v_messages_102_);
lean_inc(v_recordedDeps_101_);
lean_inc(v_cache_100_);
lean_inc(v_traceState_95_);
lean_inc(v_auxDeclNGen_99_);
lean_inc(v_ngen_98_);
lean_inc(v_nextMacroScope_97_);
lean_inc(v_env_96_);
lean_dec(v___x_94_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_134_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
uint64_t v_tid_108_; lean_object* v_traces_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_133_; 
v_tid_108_ = lean_ctor_get_uint64(v_traceState_95_, sizeof(void*)*1);
v_traces_109_ = lean_ctor_get(v_traceState_95_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v_traceState_95_);
if (v_isSharedCheck_133_ == 0)
{
v___x_111_ = v_traceState_95_;
v_isShared_112_ = v_isSharedCheck_133_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_traces_109_);
lean_dec(v_traceState_95_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_133_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; double v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_113_ = lean_box(0);
v___x_114_ = lean_box(0);
v___x_115_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0);
v___x_116_ = 0;
v___x_117_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1));
v___x_118_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_118_, 0, v_cls_81_);
lean_ctor_set(v___x_118_, 1, v___x_114_);
lean_ctor_set(v___x_118_, 2, v___x_117_);
lean_ctor_set_float(v___x_118_, sizeof(void*)*3, v___x_115_);
lean_ctor_set_float(v___x_118_, sizeof(void*)*3 + 8, v___x_115_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*3 + 16, v___x_116_);
v___x_119_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2));
v___x_120_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set(v___x_120_, 1, v_a_90_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
lean_inc(v_ref_88_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_ref_88_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = l_Lean_PersistentArray_push___redArg(v_traces_109_, v___x_121_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_122_);
v___x_124_ = v___x_111_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_122_);
lean_ctor_set_uint64(v_reuseFailAlloc_132_, sizeof(void*)*1, v_tid_108_);
v___x_124_ = v_reuseFailAlloc_132_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_126_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 4, v___x_124_);
v___x_126_ = v___x_106_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_env_96_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_nextMacroScope_97_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v_ngen_98_);
lean_ctor_set(v_reuseFailAlloc_131_, 3, v_auxDeclNGen_99_);
lean_ctor_set(v_reuseFailAlloc_131_, 4, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_131_, 5, v_cache_100_);
lean_ctor_set(v_reuseFailAlloc_131_, 6, v_recordedDeps_101_);
lean_ctor_set(v_reuseFailAlloc_131_, 7, v_messages_102_);
lean_ctor_set(v_reuseFailAlloc_131_, 8, v_infoState_103_);
lean_ctor_set(v_reuseFailAlloc_131_, 9, v_snapshotTasks_104_);
v___x_126_ = v_reuseFailAlloc_131_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_st_ref_put(v___y_86_, v___x_126_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_113_);
v___x_129_ = v___x_92_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_113_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___boxed(lean_object* v_cls_136_, lean_object* v_msg_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v_cls_136_, v_msg_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
return v_res_143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = l_Lean_Level_ofNat(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_283_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1));
v___x_284_ = l_Lean_Name_append(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62));
v___x_287_ = l_Lean_stringToMessageData(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64));
v___x_290_ = l_Lean_stringToMessageData(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77));
v___x_318_ = l_Lean_stringToMessageData(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(lean_object* v_type_319_, lean_object* v_base_320_, lean_object* v_semiringInst_321_, lean_object* v_commSemiringInst_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; 
lean_inc_ref(v_base_320_);
v___x_330_ = l_Lean_Meta_getDecLevel_x3f(v_base_320_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_775_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_775_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_775_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_775_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
if (lean_obj_tag(v_a_331_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_770_; 
lean_del_object(v___x_333_);
v_val_335_ = lean_ctor_get(v_a_331_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v_a_331_);
if (v_isSharedCheck_770_ == 0)
{
v___x_337_ = v_a_331_;
v_isShared_338_ = v_isSharedCheck_770_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_val_335_);
lean_dec(v_a_331_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_770_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5));
v___x_340_ = lean_box(0);
lean_inc(v_val_335_);
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v_val_335_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_inc_ref_n(v___x_341_, 5);
v___x_342_ = l_Lean_mkConst(v___x_339_, v___x_341_);
lean_inc_ref(v_base_320_);
v___x_343_ = l_Lean_mkAppB(v___x_342_, v_base_320_, v_commSemiringInst_322_);
v___x_344_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7));
v___x_345_ = l_Lean_mkConst(v___x_344_, v___x_341_);
lean_inc_ref_n(v___x_343_, 2);
lean_inc_ref_n(v_type_319_, 4);
v___x_346_ = l_Lean_mkAppB(v___x_345_, v_type_319_, v___x_343_);
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10));
v___x_348_ = l_Lean_mkConst(v___x_347_, v___x_341_);
lean_inc_ref(v___x_346_);
v___x_349_ = l_Lean_mkAppB(v___x_348_, v_type_319_, v___x_346_);
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12));
v___x_351_ = l_Lean_mkConst(v___x_350_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_352_ = l_Lean_mkAppB(v___x_351_, v_type_319_, v___x_349_);
v___x_395_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13));
v___x_396_ = l_Lean_mkConst(v___x_395_, v___x_341_);
v___x_397_ = l_Lean_Expr_app___override(v___x_396_, v_type_319_);
v___x_398_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_397_, v___x_343_, v_a_324_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref_known(v___x_398_, 1);
v___x_399_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14));
lean_inc_ref(v___x_341_);
v___x_400_ = l_Lean_mkConst(v___x_399_, v___x_341_);
lean_inc_ref(v_type_319_);
v___x_401_ = l_Lean_Expr_app___override(v___x_400_, v_type_319_);
lean_inc_ref(v___x_346_);
v___x_402_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_401_, v___x_346_, v_a_324_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec_ref_known(v___x_402_, 1);
v___x_403_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16));
lean_inc_ref(v___x_341_);
v___x_404_ = l_Lean_mkConst(v___x_403_, v___x_341_);
lean_inc_ref(v_type_319_);
v___x_405_ = l_Lean_Expr_app___override(v___x_404_, v_type_319_);
lean_inc_ref(v___x_349_);
v___x_406_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_405_, v___x_349_, v_a_324_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec_ref_known(v___x_406_, 1);
v___x_407_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18));
lean_inc_ref(v___x_341_);
v___x_408_ = l_Lean_mkConst(v___x_407_, v___x_341_);
lean_inc_ref(v_type_319_);
v___x_409_ = l_Lean_Expr_app___override(v___x_408_, v_type_319_);
lean_inc_ref(v___x_352_);
v___x_410_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_409_, v___x_352_, v_a_324_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec_ref_known(v___x_410_, 1);
v___x_411_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20));
lean_inc_ref_n(v___x_341_, 2);
v___x_412_ = l_Lean_mkConst(v___x_411_, v___x_341_);
lean_inc_ref_n(v_type_319_, 2);
v___x_413_ = l_Lean_Expr_app___override(v___x_412_, v_type_319_);
v___x_414_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22));
v___x_415_ = l_Lean_mkConst(v___x_414_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_416_ = l_Lean_mkAppB(v___x_415_, v_type_319_, v___x_349_);
v___x_417_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_413_, v___x_416_, v_a_324_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec_ref_known(v___x_417_, 1);
v___x_418_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24));
lean_inc_ref_n(v___x_341_, 3);
lean_inc_n(v_val_335_, 2);
v___x_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_419_, 0, v_val_335_);
lean_ctor_set(v___x_419_, 1, v___x_341_);
v___x_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_420_, 0, v_val_335_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
lean_inc_ref(v___x_420_);
v___x_421_ = l_Lean_mkConst(v___x_418_, v___x_420_);
lean_inc_ref_n(v_type_319_, 5);
v___x_422_ = l_Lean_mkApp3(v___x_421_, v_type_319_, v_type_319_, v_type_319_);
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26));
v___x_424_ = l_Lean_mkConst(v___x_423_, v___x_341_);
v___x_425_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28));
v___x_426_ = l_Lean_mkConst(v___x_425_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_427_ = l_Lean_mkAppB(v___x_426_, v_type_319_, v___x_349_);
v___x_428_ = l_Lean_mkAppB(v___x_424_, v_type_319_, v___x_427_);
v___x_429_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_422_, v___x_428_, v_a_324_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec_ref_known(v___x_429_, 1);
v___x_430_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30));
lean_inc_ref(v___x_420_);
v___x_431_ = l_Lean_mkConst(v___x_430_, v___x_420_);
lean_inc_ref_n(v_type_319_, 5);
v___x_432_ = l_Lean_mkApp3(v___x_431_, v_type_319_, v_type_319_, v_type_319_);
v___x_433_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32));
lean_inc_ref_n(v___x_341_, 2);
v___x_434_ = l_Lean_mkConst(v___x_433_, v___x_341_);
v___x_435_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34));
v___x_436_ = l_Lean_mkConst(v___x_435_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_437_ = l_Lean_mkAppB(v___x_436_, v_type_319_, v___x_349_);
v___x_438_ = l_Lean_mkAppB(v___x_434_, v_type_319_, v___x_437_);
v___x_439_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_432_, v___x_438_, v_a_324_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref_known(v___x_439_, 1);
v___x_440_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36));
v___x_441_ = l_Lean_mkConst(v___x_440_, v___x_420_);
lean_inc_ref_n(v_type_319_, 5);
v___x_442_ = l_Lean_mkApp3(v___x_441_, v_type_319_, v_type_319_, v_type_319_);
v___x_443_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38));
lean_inc_ref_n(v___x_341_, 2);
v___x_444_ = l_Lean_mkConst(v___x_443_, v___x_341_);
v___x_445_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40));
v___x_446_ = l_Lean_mkConst(v___x_445_, v___x_341_);
lean_inc_ref(v___x_346_);
v___x_447_ = l_Lean_mkAppB(v___x_446_, v_type_319_, v___x_346_);
v___x_448_ = l_Lean_mkAppB(v___x_444_, v_type_319_, v___x_447_);
v___x_449_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_442_, v___x_448_, v_a_324_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec_ref_known(v___x_449_, 1);
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42));
lean_inc_ref_n(v___x_341_, 2);
v___x_451_ = l_Lean_mkConst(v___x_450_, v___x_341_);
lean_inc_ref_n(v_type_319_, 2);
v___x_452_ = l_Lean_Expr_app___override(v___x_451_, v_type_319_);
v___x_453_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44));
v___x_454_ = l_Lean_mkConst(v___x_453_, v___x_341_);
lean_inc_ref(v___x_346_);
v___x_455_ = l_Lean_mkAppB(v___x_454_, v_type_319_, v___x_346_);
v___x_456_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_452_, v___x_455_, v_a_324_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec_ref_known(v___x_456_, 1);
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46));
v___x_458_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47);
lean_inc_ref_n(v___x_341_, 2);
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_341_);
lean_inc(v_val_335_);
v___x_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_460_, 0, v_val_335_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = l_Lean_mkConst(v___x_457_, v___x_460_);
v___x_462_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_319_, 3);
v___x_463_ = l_Lean_mkApp3(v___x_461_, v_type_319_, v___x_462_, v_type_319_);
v___x_464_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49));
v___x_465_ = l_Lean_mkConst(v___x_464_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_466_ = l_Lean_mkAppB(v___x_465_, v_type_319_, v___x_349_);
v___x_467_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_463_, v___x_466_, v_a_324_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec_ref_known(v___x_467_, 1);
v___x_468_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51));
lean_inc_ref_n(v___x_341_, 2);
v___x_469_ = l_Lean_mkConst(v___x_468_, v___x_341_);
lean_inc_ref_n(v_type_319_, 2);
v___x_470_ = l_Lean_Expr_app___override(v___x_469_, v_type_319_);
v___x_471_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53));
v___x_472_ = l_Lean_mkConst(v___x_471_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_473_ = l_Lean_mkAppB(v___x_472_, v_type_319_, v___x_349_);
v___x_474_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_470_, v___x_473_, v_a_324_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec_ref_known(v___x_474_, 1);
v___x_475_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55));
lean_inc_ref_n(v___x_341_, 2);
v___x_476_ = l_Lean_mkConst(v___x_475_, v___x_341_);
lean_inc_ref_n(v_type_319_, 2);
v___x_477_ = l_Lean_Expr_app___override(v___x_476_, v_type_319_);
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57));
v___x_479_ = l_Lean_mkConst(v___x_478_, v___x_341_);
lean_inc_ref(v___x_346_);
v___x_480_ = l_Lean_mkAppB(v___x_479_, v_type_319_, v___x_346_);
v___x_481_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_477_, v___x_480_, v_a_324_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_toCold_482_; lean_object* v_inheritedTraceOptions_483_; lean_object* v___x_484_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v_options_492_; lean_object* v_inheritedTraceOptions_493_; lean_object* v___y_494_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_534_; lean_object* v_noZeroDivInst_x3f_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v_val_552_; lean_object* v_charInst_x3f_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___x_659_; lean_object* v_a_660_; uint8_t v___x_661_; 
lean_dec_ref_known(v___x_481_, 1);
v_toCold_482_ = lean_ctor_get(v_a_327_, 0);
v_inheritedTraceOptions_483_ = lean_ctor_get(v_toCold_482_, 11);
v___x_484_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_659_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_484_, v_inheritedTraceOptions_483_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref(v___x_659_);
v___x_661_ = lean_unbox(v_a_660_);
lean_dec(v_a_660_);
if (v___x_661_ == 0)
{
v___y_591_ = v_a_323_;
v___y_592_ = v_a_324_;
v___y_593_ = v_a_325_;
v___y_594_ = v_a_326_;
v___y_595_ = v_a_327_;
v___y_596_ = v_a_328_;
goto v___jp_590_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78);
lean_inc_ref(v_type_319_);
v___x_663_ = l_Lean_MessageData_ofExpr(v_type_319_);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_484_, v___x_664_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_dec_ref_known(v___x_665_, 1);
v___y_591_ = v_a_323_;
v___y_592_ = v_a_324_;
v___y_593_ = v_a_325_;
v___y_594_ = v_a_326_;
v___y_595_ = v_a_327_;
v___y_596_ = v_a_328_;
goto v___jp_590_;
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
v___jp_485_:
{
uint8_t v_hasTrace_495_; 
v_hasTrace_495_ = lean_ctor_get_uint8(v_options_492_, sizeof(void*)*1);
if (v_hasTrace_495_ == 0)
{
v___y_354_ = v___y_486_;
v___y_355_ = v___y_487_;
v___y_356_ = v___y_488_;
v___y_357_ = v___y_491_;
goto v___jp_353_;
}
else
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61);
v___x_497_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_493_, v_options_492_, v___x_496_);
if (v___x_497_ == 0)
{
v___y_354_ = v___y_486_;
v___y_355_ = v___y_487_;
v___y_356_ = v___y_488_;
v___y_357_ = v___y_491_;
goto v___jp_353_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63);
v___x_499_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_484_, v___x_498_, v___y_489_, v___y_490_, v___y_491_, v___y_494_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_dec_ref_known(v___x_499_, 1);
v___y_354_ = v___y_486_;
v___y_355_ = v___y_487_;
v___y_356_ = v___y_488_;
v___y_357_ = v___y_491_;
goto v___jp_353_;
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_type_319_);
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
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
}
}
v___jp_508_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_inc_ref(v___y_517_);
v___x_518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_518_, 0, v___y_517_);
v___x_519_ = l_Lean_MessageData_ofFormat(v___x_518_);
lean_inc_ref(v___y_515_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___y_515_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_484_, v___x_520_, v___y_512_, v___y_513_, v___y_510_, v___y_509_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_toCold_522_; lean_object* v_options_523_; lean_object* v_inheritedTraceOptions_524_; 
lean_dec_ref_known(v___x_521_, 1);
v_toCold_522_ = lean_ctor_get(v___y_510_, 0);
v_options_523_ = lean_ctor_get(v_toCold_522_, 2);
v_inheritedTraceOptions_524_ = lean_ctor_get(v_toCold_522_, 11);
v___y_486_ = v___y_511_;
v___y_487_ = v___y_514_;
v___y_488_ = v___y_516_;
v___y_489_ = v___y_512_;
v___y_490_ = v___y_513_;
v___y_491_ = v___y_510_;
v_options_492_ = v_options_523_;
v_inheritedTraceOptions_493_ = v_inheritedTraceOptions_524_;
v___y_494_ = v___y_509_;
goto v___jp_485_;
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v___y_514_);
lean_dec(v___y_511_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_type_319_);
v_a_525_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_521_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_521_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
v___jp_533_:
{
lean_object* v_toCold_542_; lean_object* v_options_543_; lean_object* v_inheritedTraceOptions_544_; lean_object* v___x_545_; lean_object* v_a_546_; uint8_t v___x_547_; 
v_toCold_542_ = lean_ctor_get(v___y_540_, 0);
v_options_543_ = lean_ctor_get(v_toCold_542_, 2);
v_inheritedTraceOptions_544_ = lean_ctor_get(v_toCold_542_, 11);
v___x_545_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_484_, v_inheritedTraceOptions_544_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref(v___x_545_);
v___x_547_ = lean_unbox(v_a_546_);
lean_dec(v_a_546_);
if (v___x_547_ == 0)
{
v___y_486_ = v___y_534_;
v___y_487_ = v_noZeroDivInst_x3f_535_;
v___y_488_ = v___y_537_;
v___y_489_ = v___y_538_;
v___y_490_ = v___y_539_;
v___y_491_ = v___y_540_;
v_options_492_ = v_options_543_;
v_inheritedTraceOptions_493_ = v_inheritedTraceOptions_544_;
v___y_494_ = v___y_541_;
goto v___jp_485_;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65);
if (lean_obj_tag(v_noZeroDivInst_x3f_535_) == 0)
{
lean_object* v___x_549_; 
v___x_549_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66));
v___y_509_ = v___y_541_;
v___y_510_ = v___y_540_;
v___y_511_ = v___y_534_;
v___y_512_ = v___y_538_;
v___y_513_ = v___y_539_;
v___y_514_ = v_noZeroDivInst_x3f_535_;
v___y_515_ = v___x_548_;
v___y_516_ = v___y_537_;
v___y_517_ = v___x_549_;
goto v___jp_508_;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67));
v___y_509_ = v___y_541_;
v___y_510_ = v___y_540_;
v___y_511_ = v___y_534_;
v___y_512_ = v___y_538_;
v___y_513_ = v___y_539_;
v___y_514_ = v_noZeroDivInst_x3f_535_;
v___y_515_ = v___x_548_;
v___y_516_ = v___y_537_;
v___y_517_ = v___x_550_;
goto v___jp_508_;
}
}
}
v___jp_551_:
{
lean_object* v___x_560_; 
lean_inc_ref(v_base_320_);
lean_inc(v_val_335_);
v___x_560_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_val_335_, v_base_320_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_560_, 1);
if (lean_obj_tag(v_a_561_) == 1)
{
lean_object* v_val_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_572_; 
v_val_562_ = lean_ctor_get(v_a_561_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v_a_561_);
if (v_isSharedCheck_572_ == 0)
{
v___x_564_ = v_a_561_;
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_val_562_);
lean_dec(v_a_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70));
v___x_567_ = l_Lean_mkConst(v___x_566_, v___x_341_);
v___x_568_ = l_Lean_mkApp4(v___x_567_, v_base_320_, v_semiringInst_321_, v_val_552_, v_val_562_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_568_);
v___x_570_ = v___x_564_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
v___y_534_ = v_charInst_x3f_553_;
v_noZeroDivInst_x3f_535_ = v___x_570_;
v___y_536_ = v___y_554_;
v___y_537_ = v___y_555_;
v___y_538_ = v___y_556_;
v___y_539_ = v___y_557_;
v___y_540_ = v___y_558_;
v___y_541_ = v___y_559_;
goto v___jp_533_;
}
}
}
else
{
lean_object* v___x_573_; 
lean_dec(v_a_561_);
lean_dec_ref(v_val_552_);
lean_dec_ref_known(v___x_341_, 2);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
v___x_573_ = lean_box(0);
v___y_534_ = v_charInst_x3f_553_;
v_noZeroDivInst_x3f_535_ = v___x_573_;
v___y_536_ = v___y_554_;
v___y_537_ = v___y_555_;
v___y_538_ = v___y_556_;
v___y_539_ = v___y_557_;
v___y_540_ = v___y_558_;
v___y_541_ = v___y_559_;
goto v___jp_533_;
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec(v_charInst_x3f_553_);
lean_dec_ref(v_val_552_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_574_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_560_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_560_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
v___jp_582_:
{
lean_object* v___x_589_; 
v___x_589_ = lean_box(0);
v___y_534_ = v___x_589_;
v_noZeroDivInst_x3f_535_ = v___x_589_;
v___y_536_ = v___y_583_;
v___y_537_ = v___y_584_;
v___y_538_ = v___y_585_;
v___y_539_ = v___y_586_;
v___y_540_ = v___y_587_;
v___y_541_ = v___y_588_;
goto v___jp_533_;
}
v___jp_590_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_597_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72));
lean_inc_ref(v___x_341_);
v___x_598_ = l_Lean_mkConst(v___x_597_, v___x_341_);
lean_inc_ref(v_base_320_);
v___x_599_ = l_Lean_Expr_app___override(v___x_598_, v_base_320_);
v___x_600_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_599_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
if (lean_obj_tag(v_a_601_) == 1)
{
lean_object* v_val_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_val_602_ = lean_ctor_get(v_a_601_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v_a_601_, 1);
v___x_603_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74));
lean_inc_ref(v___x_341_);
v___x_604_ = l_Lean_mkConst(v___x_603_, v___x_341_);
lean_inc_ref(v_base_320_);
v___x_605_ = l_Lean_mkAppB(v___x_604_, v_base_320_, v_val_602_);
v___x_606_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_605_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
if (lean_obj_tag(v_a_607_) == 1)
{
lean_object* v_val_608_; lean_object* v___x_609_; 
v_val_608_ = lean_ctor_get(v_a_607_, 0);
lean_inc(v_val_608_);
lean_dec_ref_known(v_a_607_, 1);
lean_inc_ref(v_semiringInst_321_);
lean_inc_ref(v_base_320_);
lean_inc(v_val_335_);
v___x_609_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_val_335_, v_base_320_, v_semiringInst_321_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
if (lean_obj_tag(v_a_610_) == 1)
{
lean_object* v_val_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_631_; 
v_val_611_ = lean_ctor_get(v_a_610_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v_a_610_);
if (v_isSharedCheck_631_ == 0)
{
v___x_613_ = v_a_610_;
v_isShared_614_ = v_isSharedCheck_631_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_val_611_);
lean_dec(v_a_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_631_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_630_; 
v_fst_615_ = lean_ctor_get(v_val_611_, 0);
v_snd_616_ = lean_ctor_get(v_val_611_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_val_611_);
if (v_isSharedCheck_630_ == 0)
{
v___x_618_ = v_val_611_;
v_isShared_619_ = v_isSharedCheck_630_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
lean_dec(v_val_611_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_630_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_620_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76));
lean_inc_ref(v___x_341_);
v___x_621_ = l_Lean_mkConst(v___x_620_, v___x_341_);
lean_inc(v_snd_616_);
v___x_622_ = l_Lean_mkRawNatLit(v_snd_616_);
lean_inc(v_val_608_);
lean_inc_ref(v_semiringInst_321_);
lean_inc_ref(v_base_320_);
v___x_623_ = l_Lean_mkApp5(v___x_621_, v_base_320_, v___x_622_, v_semiringInst_321_, v_val_608_, v_fst_615_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_623_);
v___x_625_ = v___x_618_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_snd_616_);
v___x_625_ = v_reuseFailAlloc_629_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_625_);
v___x_627_ = v___x_613_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
v_val_552_ = v_val_608_;
v_charInst_x3f_553_ = v___x_627_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_593_;
v___y_557_ = v___y_594_;
v___y_558_ = v___y_595_;
v___y_559_ = v___y_596_;
goto v___jp_551_;
}
}
}
}
}
else
{
lean_object* v___x_632_; 
lean_dec(v_a_610_);
v___x_632_ = lean_box(0);
v_val_552_ = v_val_608_;
v_charInst_x3f_553_ = v___x_632_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_593_;
v___y_557_ = v___y_594_;
v___y_558_ = v___y_595_;
v___y_559_ = v___y_596_;
goto v___jp_551_;
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_val_608_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_633_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_609_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_609_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
if (lean_obj_tag(v_a_607_) == 1)
{
lean_object* v_val_641_; lean_object* v___x_642_; 
v_val_641_ = lean_ctor_get(v_a_607_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v_a_607_, 1);
v___x_642_ = lean_box(0);
v_val_552_ = v_val_641_;
v_charInst_x3f_553_ = v___x_642_;
v___y_554_ = v___y_591_;
v___y_555_ = v___y_592_;
v___y_556_ = v___y_593_;
v___y_557_ = v___y_594_;
v___y_558_ = v___y_595_;
v___y_559_ = v___y_596_;
goto v___jp_551_;
}
else
{
lean_dec(v_a_607_);
lean_dec_ref_known(v___x_341_, 2);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
v___y_583_ = v___y_591_;
v___y_584_ = v___y_592_;
v___y_585_ = v___y_593_;
v___y_586_ = v___y_594_;
v___y_587_ = v___y_595_;
v___y_588_ = v___y_596_;
goto v___jp_582_;
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_643_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_606_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_606_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_dec(v_a_601_);
lean_dec_ref_known(v___x_341_, 2);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
v___y_583_ = v___y_591_;
v___y_584_ = v___y_592_;
v___y_585_ = v___y_593_;
v___y_586_ = v___y_594_;
v___y_587_ = v___y_595_;
v___y_588_ = v___y_596_;
goto v___jp_582_;
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_651_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_600_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_600_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_674_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_481_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_481_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_682_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_474_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_474_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_690_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_467_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_467_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_698_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_456_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_456_);
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
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_706_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_449_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_449_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref_known(v___x_420_, 2);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_714_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_439_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_439_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref_known(v___x_420_, 2);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_722_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_429_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_429_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_730_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_417_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_417_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_738_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_410_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_410_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_746_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_406_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_406_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_754_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_402_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_402_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_762_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_398_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_398_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
v___jp_353_:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v_rings_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v_rings_360_ = lean_ctor_get(v_a_359_, 1);
lean_inc_ref(v_rings_360_);
lean_dec(v_a_359_);
v___x_361_ = lean_array_get_size(v_rings_360_);
lean_dec_ref(v_rings_360_);
v___x_362_ = lean_box(0);
v___x_363_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v_type_319_);
lean_ctor_set(v___x_363_, 2, v_val_335_);
lean_ctor_set(v___x_363_, 3, v___x_346_);
lean_ctor_set(v___x_363_, 4, v___x_349_);
lean_ctor_set(v___x_363_, 5, v___y_354_);
lean_ctor_set(v___x_363_, 6, v___x_362_);
lean_ctor_set(v___x_363_, 7, v___x_362_);
lean_ctor_set(v___x_363_, 8, v___x_362_);
lean_ctor_set(v___x_363_, 9, v___x_362_);
lean_ctor_set(v___x_363_, 10, v___x_362_);
lean_ctor_set(v___x_363_, 11, v___x_362_);
lean_ctor_set(v___x_363_, 12, v___x_362_);
lean_ctor_set(v___x_363_, 13, v___x_362_);
lean_ctor_set(v___x_363_, 14, v___x_362_);
lean_ctor_set(v___x_363_, 15, v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
lean_ctor_set(v___x_364_, 2, v___x_362_);
lean_ctor_set(v___x_364_, 3, v___x_362_);
lean_ctor_set(v___x_364_, 4, v___x_352_);
lean_ctor_set(v___x_364_, 5, v___x_343_);
lean_ctor_set(v___x_364_, 6, v___y_355_);
lean_ctor_set(v___x_364_, 7, v___x_362_);
lean_ctor_set(v___x_364_, 8, v___x_362_);
v___f_365_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0), 2, 1);
lean_closure_set(v___f_365_, 0, v___x_364_);
v___x_366_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_367_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_366_, v___f_365_, v___y_356_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_377_; 
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_367_, 0);
lean_dec(v_unused_378_);
v___x_369_ = v___x_367_;
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
else
{
lean_dec(v___x_367_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_361_);
v___x_372_ = v___x_337_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_361_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_372_);
v___x_374_ = v___x_369_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_del_object(v___x_337_);
v_a_379_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_367_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_367_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_type_319_);
v_a_387_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_358_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_358_);
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
}
else
{
lean_object* v___x_771_; lean_object* v___x_773_; 
lean_dec(v_a_331_);
lean_dec_ref(v_commSemiringInst_322_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v___x_771_ = lean_box(0);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_771_);
v___x_773_ = v___x_333_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_commSemiringInst_322_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_776_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_330_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_330_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___boxed(lean_object* v_type_784_, lean_object* v_base_785_, lean_object* v_semiringInst_786_, lean_object* v_commSemiringInst_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(v_type_784_, v_base_785_, v_semiringInst_786_, v_commSemiringInst_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0(lean_object* v_cls_796_, lean_object* v_msg_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v_cls_796_, v_msg_797_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___boxed(lean_object* v_cls_806_, lean_object* v_msg_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0(v_cls_806_, v_msg_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
return v_res_815_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2));
v___x_823_ = l_Lean_stringToMessageData(v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(lean_object* v_type_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v___x_832_; 
lean_inc_ref(v_type_824_);
v___x_832_ = l_Lean_Meta_getDecLevel(v_type_824_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc_n(v_a_833_, 2);
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13));
v___x_835_ = lean_box(0);
v___x_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_836_, 0, v_a_833_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
lean_inc_ref(v___x_836_);
v___x_837_ = l_Lean_mkConst(v___x_834_, v___x_836_);
lean_inc_ref(v_type_824_);
v___x_838_ = l_Lean_Expr_app___override(v___x_837_, v_type_824_);
v___x_839_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_838_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_1048_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_1048_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_1048_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
if (lean_obj_tag(v_a_840_) == 1)
{
lean_object* v_val_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_1043_; 
lean_del_object(v___x_842_);
v_val_844_ = lean_ctor_get(v_a_840_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_a_840_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_846_ = v_a_840_;
v_isShared_847_ = v_isSharedCheck_1043_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_val_844_);
lean_dec(v_a_840_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_1043_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v_toCold_851_; lean_object* v_inheritedTraceOptions_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___x_903_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___x_1028_; lean_object* v_a_1029_; uint8_t v___x_1030_; 
v___x_848_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7));
lean_inc_ref_n(v___x_836_, 3);
v___x_849_ = l_Lean_mkConst(v___x_848_, v___x_836_);
lean_inc(v_val_844_);
lean_inc_ref_n(v_type_824_, 3);
v___x_850_ = l_Lean_mkAppB(v___x_849_, v_type_824_, v_val_844_);
v_toCold_851_ = lean_ctor_get(v_a_829_, 0);
v_inheritedTraceOptions_852_ = lean_ctor_get(v_toCold_851_, 11);
v___x_853_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10));
v___x_854_ = l_Lean_mkConst(v___x_853_, v___x_836_);
lean_inc_ref(v___x_850_);
v___x_855_ = l_Lean_mkAppB(v___x_854_, v_type_824_, v___x_850_);
v___x_856_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12));
v___x_857_ = l_Lean_mkConst(v___x_856_, v___x_836_);
lean_inc_ref(v___x_855_);
v___x_858_ = l_Lean_mkAppB(v___x_857_, v_type_824_, v___x_855_);
v___x_903_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_1028_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_903_, v_inheritedTraceOptions_852_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = lean_unbox(v_a_1029_);
lean_dec(v_a_1029_);
if (v___x_1030_ == 0)
{
v___y_994_ = v_a_825_;
v___y_995_ = v_a_826_;
v___y_996_ = v_a_827_;
v___y_997_ = v_a_828_;
v___y_998_ = v_a_829_;
v___y_999_ = v_a_830_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1031_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78);
lean_inc_ref(v_type_824_);
v___x_1032_ = l_Lean_MessageData_ofExpr(v_type_824_);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_903_, v___x_1033_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_dec_ref_known(v___x_1034_, 1);
v___y_994_ = v_a_825_;
v___y_995_ = v_a_826_;
v___y_996_ = v_a_827_;
v___y_997_ = v_a_828_;
v___y_998_ = v_a_829_;
v___y_999_ = v_a_830_;
goto v___jp_993_;
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v___x_858_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_850_);
lean_del_object(v___x_846_);
lean_dec(v_val_844_);
lean_dec_ref_known(v___x_836_, 2);
lean_dec(v_a_833_);
lean_dec_ref(v_type_824_);
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
v___jp_859_:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_box(0);
v___x_867_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v_rings_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v_rings_869_ = lean_ctor_get(v_a_868_, 1);
lean_inc_ref(v_rings_869_);
lean_dec(v_a_868_);
v___x_870_ = lean_array_get_size(v_rings_869_);
lean_dec_ref(v_rings_869_);
v___x_871_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v_type_824_);
lean_ctor_set(v___x_871_, 2, v_a_833_);
lean_ctor_set(v___x_871_, 3, v___x_850_);
lean_ctor_set(v___x_871_, 4, v___x_855_);
lean_ctor_set(v___x_871_, 5, v___y_863_);
lean_ctor_set(v___x_871_, 6, v___x_866_);
lean_ctor_set(v___x_871_, 7, v___x_866_);
lean_ctor_set(v___x_871_, 8, v___x_866_);
lean_ctor_set(v___x_871_, 9, v___x_866_);
lean_ctor_set(v___x_871_, 10, v___x_866_);
lean_ctor_set(v___x_871_, 11, v___x_866_);
lean_ctor_set(v___x_871_, 12, v___x_866_);
lean_ctor_set(v___x_871_, 13, v___x_866_);
lean_ctor_set(v___x_871_, 14, v___x_866_);
lean_ctor_set(v___x_871_, 15, v___x_866_);
v___x_872_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___x_866_);
lean_ctor_set(v___x_872_, 2, v___x_866_);
lean_ctor_set(v___x_872_, 3, v___x_866_);
lean_ctor_set(v___x_872_, 4, v___x_858_);
lean_ctor_set(v___x_872_, 5, v_val_844_);
lean_ctor_set(v___x_872_, 6, v___y_861_);
lean_ctor_set(v___x_872_, 7, v___y_862_);
lean_ctor_set(v___x_872_, 8, v___y_860_);
v___f_873_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0), 2, 1);
lean_closure_set(v___f_873_, 0, v___x_872_);
v___x_874_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_875_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_874_, v___f_873_, v___y_864_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_885_; 
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v___x_875_, 0);
lean_dec(v_unused_886_);
v___x_877_ = v___x_875_;
v_isShared_878_ = v_isSharedCheck_885_;
goto v_resetjp_876_;
}
else
{
lean_dec(v___x_875_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_885_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_870_);
v___x_880_ = v___x_846_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_870_);
v___x_880_ = v_reuseFailAlloc_884_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_880_);
v___x_882_ = v___x_877_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
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
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_del_object(v___x_846_);
v_a_887_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_875_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_875_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v___y_863_);
lean_dec(v___y_862_);
lean_dec(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___x_858_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_850_);
lean_del_object(v___x_846_);
lean_dec(v_val_844_);
lean_dec(v_a_833_);
lean_dec_ref(v_type_824_);
v_a_895_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_867_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_867_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
v___jp_904_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_inc_ref(v___y_915_);
v___x_916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_916_, 0, v___y_915_);
v___x_917_ = l_Lean_MessageData_ofFormat(v___x_916_);
lean_inc_ref(v___y_910_);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___y_910_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_903_, v___x_918_, v___y_908_, v___y_913_, v___y_905_, v___y_909_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_dec_ref_known(v___x_919_, 1);
v___y_860_ = v___y_907_;
v___y_861_ = v___y_911_;
v___y_862_ = v___y_912_;
v___y_863_ = v___y_914_;
v___y_864_ = v___y_906_;
v___y_865_ = v___y_905_;
goto v___jp_859_;
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v___y_914_);
lean_dec(v___y_912_);
lean_dec(v___y_911_);
lean_dec(v___y_907_);
lean_dec_ref(v___x_858_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_850_);
lean_del_object(v___x_846_);
lean_dec(v_val_844_);
lean_dec(v_a_833_);
lean_dec_ref(v_type_824_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
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
v___jp_928_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1));
v___x_938_ = l_Lean_mkConst(v___x_937_, v___x_836_);
lean_inc_ref(v_type_824_);
v___x_939_ = l_Lean_Expr_app___override(v___x_938_, v_type_824_);
v___x_940_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_939_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_942_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
lean_inc_ref(v_type_824_);
lean_inc(v_a_833_);
v___x_942_ = l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(v_a_833_, v_type_824_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_toCold_943_; lean_object* v_options_944_; uint8_t v_hasTrace_945_; 
v_toCold_943_ = lean_ctor_get(v___y_935_, 0);
v_options_944_ = lean_ctor_get(v_toCold_943_, 2);
v_hasTrace_945_ = lean_ctor_get_uint8(v_options_944_, sizeof(void*)*1);
if (v_hasTrace_945_ == 0)
{
lean_object* v_a_946_; 
v_a_946_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_946_);
lean_dec_ref_known(v___x_942_, 1);
v___y_860_ = v_a_946_;
v___y_861_ = v___y_929_;
v___y_862_ = v_a_941_;
v___y_863_ = v___y_930_;
v___y_864_ = v___y_932_;
v___y_865_ = v___y_935_;
goto v___jp_859_;
}
else
{
lean_object* v_a_947_; lean_object* v_inheritedTraceOptions_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_a_947_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_942_, 1);
v_inheritedTraceOptions_948_ = lean_ctor_get(v_toCold_943_, 11);
v___x_949_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61);
v___x_950_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_948_, v_options_944_, v___x_949_);
if (v___x_950_ == 0)
{
v___y_860_ = v_a_947_;
v___y_861_ = v___y_929_;
v___y_862_ = v_a_941_;
v___y_863_ = v___y_930_;
v___y_864_ = v___y_932_;
v___y_865_ = v___y_935_;
goto v___jp_859_;
}
else
{
lean_object* v___x_951_; 
v___x_951_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3);
if (lean_obj_tag(v_a_947_) == 0)
{
lean_object* v___x_952_; 
v___x_952_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66));
v___y_905_ = v___y_935_;
v___y_906_ = v___y_932_;
v___y_907_ = v_a_947_;
v___y_908_ = v___y_933_;
v___y_909_ = v___y_936_;
v___y_910_ = v___x_951_;
v___y_911_ = v___y_929_;
v___y_912_ = v_a_941_;
v___y_913_ = v___y_934_;
v___y_914_ = v___y_930_;
v___y_915_ = v___x_952_;
goto v___jp_904_;
}
else
{
lean_object* v___x_953_; 
v___x_953_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67));
v___y_905_ = v___y_935_;
v___y_906_ = v___y_932_;
v___y_907_ = v_a_947_;
v___y_908_ = v___y_933_;
v___y_909_ = v___y_936_;
v___y_910_ = v___x_951_;
v___y_911_ = v___y_929_;
v___y_912_ = v_a_941_;
v___y_913_ = v___y_934_;
v___y_914_ = v___y_930_;
v___y_915_ = v___x_953_;
goto v___jp_904_;
}
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec(v_a_941_);
lean_dec(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___x_858_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_850_);
lean_del_object(v___x_846_);
lean_dec(v_val_844_);
lean_dec(v_a_833_);
lean_dec_ref(v_type_824_);
v_a_954_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_942_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_942_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___x_858_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_850_);
lean_del_object(v___x_846_);
lean_dec(v_val_844_);
lean_dec(v_a_833_);
lean_dec_ref(v_type_824_);
v_a_962_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_940_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_940_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
v___jp_970_:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_inc_ref(v___y_980_);
v___x_981_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_981_, 0, v___y_980_);
v___x_982_ = l_Lean_MessageData_ofFormat(v___x_981_);
lean_inc_ref(v___y_975_);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___y_975_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_903_, v___x_983_, v___y_971_, v___y_978_, v___y_974_, v___y_972_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_dec_ref_known(v___x_984_, 1);
v___y_929_ = v___y_976_;
v___y_930_ = v___y_979_;
v___y_931_ = v___y_977_;
v___y_932_ = v___y_973_;
v___y_933_ = v___y_971_;
v___y_934_ = v___y_978_;
v___y_935_ = v___y_974_;
v___y_936_ = v___y_972_;
goto v___jp_928_;
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v___y_979_);
lean_dec(v___y_976_);
lean_dec_ref(v___x_858_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_850_);
lean_del_object(v___x_846_);
lean_dec(v_val_844_);
lean_dec_ref_known(v___x_836_, 2);
lean_dec(v_a_833_);
lean_dec_ref(v_type_824_);
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
v___jp_993_:
{
lean_object* v___x_1000_; 
lean_inc_ref(v___x_855_);
lean_inc_ref(v_type_824_);
lean_inc(v_a_833_);
v___x_1000_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_a_833_, v_type_824_, v___x_855_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
lean_inc_ref(v_type_824_);
lean_inc(v_a_833_);
v___x_1002_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_a_833_, v_type_824_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_toCold_1003_; lean_object* v_a_1004_; lean_object* v_inheritedTraceOptions_1005_; lean_object* v___x_1006_; lean_object* v_a_1007_; uint8_t v___x_1008_; 
v_toCold_1003_ = lean_ctor_get(v___y_998_, 0);
v_a_1004_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1002_, 1);
v_inheritedTraceOptions_1005_ = lean_ctor_get(v_toCold_1003_, 11);
v___x_1006_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_903_, v_inheritedTraceOptions_1005_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref(v___x_1006_);
v___x_1008_ = lean_unbox(v_a_1007_);
lean_dec(v_a_1007_);
if (v___x_1008_ == 0)
{
v___y_929_ = v_a_1004_;
v___y_930_ = v_a_1001_;
v___y_931_ = v___y_994_;
v___y_932_ = v___y_995_;
v___y_933_ = v___y_996_;
v___y_934_ = v___y_997_;
v___y_935_ = v___y_998_;
v___y_936_ = v___y_999_;
goto v___jp_928_;
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65);
if (lean_obj_tag(v_a_1004_) == 0)
{
lean_object* v___x_1010_; 
v___x_1010_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66));
v___y_971_ = v___y_996_;
v___y_972_ = v___y_999_;
v___y_973_ = v___y_995_;
v___y_974_ = v___y_998_;
v___y_975_ = v___x_1009_;
v___y_976_ = v_a_1004_;
v___y_977_ = v___y_994_;
v___y_978_ = v___y_997_;
v___y_979_ = v_a_1001_;
v___y_980_ = v___x_1010_;
goto v___jp_970_;
}
else
{
lean_object* v___x_1011_; 
v___x_1011_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67));
v___y_971_ = v___y_996_;
v___y_972_ = v___y_999_;
v___y_973_ = v___y_995_;
v___y_974_ = v___y_998_;
v___y_975_ = v___x_1009_;
v___y_976_ = v_a_1004_;
v___y_977_ = v___y_994_;
v___y_978_ = v___y_997_;
v___y_979_ = v_a_1001_;
v___y_980_ = v___x_1011_;
goto v___jp_970_;
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec(v_a_1001_);
lean_dec_ref(v___x_858_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_850_);
lean_del_object(v___x_846_);
lean_dec(v_val_844_);
lean_dec_ref_known(v___x_836_, 2);
lean_dec(v_a_833_);
lean_dec_ref(v_type_824_);
v_a_1012_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1002_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1002_);
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
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec_ref(v___x_858_);
lean_dec_ref(v___x_855_);
lean_dec_ref(v___x_850_);
lean_del_object(v___x_846_);
lean_dec(v_val_844_);
lean_dec_ref_known(v___x_836_, 2);
lean_dec(v_a_833_);
lean_dec_ref(v_type_824_);
v_a_1020_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1000_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1000_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
lean_dec(v_a_840_);
lean_dec_ref_known(v___x_836_, 2);
lean_dec(v_a_833_);
lean_dec_ref(v_type_824_);
v___x_1044_ = lean_box(0);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_1044_);
v___x_1046_ = v___x_842_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref_known(v___x_836_, 2);
lean_dec(v_a_833_);
lean_dec_ref(v_type_824_);
v_a_1049_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_839_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_839_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref(v_type_824_);
v_a_1057_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_832_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_832_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___boxed(lean_object* v_type_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(lean_object* v_type_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v___x_1094_; uint8_t v___x_1095_; 
lean_inc_ref(v_type_1086_);
v___x_1094_ = l_Lean_Expr_cleanupAnnotations(v_type_1086_);
v___x_1095_ = l_Lean_Expr_isApp(v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
lean_dec_ref(v___x_1094_);
v___x_1096_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
return v___x_1096_;
}
else
{
lean_object* v_arg_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_arg_1097_ = lean_ctor_get(v___x_1094_, 1);
lean_inc_ref(v_arg_1097_);
v___x_1098_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1094_);
v___x_1099_ = l_Lean_Expr_isApp(v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_dec_ref(v___x_1098_);
lean_dec_ref(v_arg_1097_);
v___x_1100_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
return v___x_1100_;
}
else
{
lean_object* v_arg_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_arg_1101_ = lean_ctor_get(v___x_1098_, 1);
lean_inc_ref(v_arg_1101_);
v___x_1102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1098_);
v___x_1103_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1));
v___x_1104_ = l_Lean_Expr_isConstOf(v___x_1102_, v___x_1103_);
lean_dec_ref(v___x_1102_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; 
lean_dec_ref(v_arg_1101_);
lean_dec_ref(v_arg_1097_);
v___x_1105_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
lean_inc_ref(v_arg_1097_);
v___x_1106_ = l_Lean_Expr_cleanupAnnotations(v_arg_1097_);
v___x_1107_ = l_Lean_Expr_isApp(v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
lean_dec_ref(v___x_1106_);
lean_dec_ref(v_arg_1101_);
lean_dec_ref(v_arg_1097_);
v___x_1108_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
return v___x_1108_;
}
else
{
lean_object* v_arg_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_arg_1109_ = lean_ctor_get(v___x_1106_, 1);
lean_inc_ref(v_arg_1109_);
v___x_1110_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1106_);
v___x_1111_ = l_Lean_Expr_isApp(v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_arg_1109_);
lean_dec_ref(v_arg_1101_);
lean_dec_ref(v_arg_1097_);
v___x_1112_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1113_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1110_);
v___x_1114_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2));
v___x_1115_ = l_Lean_Expr_isConstOf(v___x_1113_, v___x_1114_);
lean_dec_ref(v___x_1113_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
lean_dec_ref(v_arg_1109_);
lean_dec_ref(v_arg_1101_);
lean_dec_ref(v_arg_1097_);
v___x_1116_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; 
v___x_1117_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(v_type_1086_, v_arg_1101_, v_arg_1097_, v_arg_1109_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
return v___x_1117_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___boxed(lean_object* v_type_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0(lean_object* v___x_1127_, lean_object* v_s_1128_){
_start:
{
lean_object* v_exp_1129_; lean_object* v_rings_1130_; lean_object* v_semirings_1131_; lean_object* v_ncRings_1132_; lean_object* v_ncSemirings_1133_; lean_object* v_typeClassify_1134_; lean_object* v_orders_1135_; lean_object* v_typeOrderClassify_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1144_; 
v_exp_1129_ = lean_ctor_get(v_s_1128_, 0);
v_rings_1130_ = lean_ctor_get(v_s_1128_, 1);
v_semirings_1131_ = lean_ctor_get(v_s_1128_, 2);
v_ncRings_1132_ = lean_ctor_get(v_s_1128_, 3);
v_ncSemirings_1133_ = lean_ctor_get(v_s_1128_, 4);
v_typeClassify_1134_ = lean_ctor_get(v_s_1128_, 5);
v_orders_1135_ = lean_ctor_get(v_s_1128_, 6);
v_typeOrderClassify_1136_ = lean_ctor_get(v_s_1128_, 7);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_s_1128_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1138_ = v_s_1128_;
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_typeOrderClassify_1136_);
lean_inc(v_orders_1135_);
lean_inc(v_typeClassify_1134_);
lean_inc(v_ncSemirings_1133_);
lean_inc(v_ncRings_1132_);
lean_inc(v_semirings_1131_);
lean_inc(v_rings_1130_);
lean_inc(v_exp_1129_);
lean_dec(v_s_1128_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = lean_array_push(v_ncRings_1132_, v___x_1127_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 3, v___x_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_exp_1129_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_rings_1130_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_semirings_1131_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_ncSemirings_1133_);
lean_ctor_set(v_reuseFailAlloc_1143_, 5, v_typeClassify_1134_);
lean_ctor_set(v_reuseFailAlloc_1143_, 6, v_orders_1135_);
lean_ctor_set(v_reuseFailAlloc_1143_, 7, v_typeOrderClassify_1136_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(lean_object* v_type_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___x_1153_; 
lean_inc_ref(v_type_1145_);
v___x_1153_ = l_Lean_Meta_getDecLevel(v_type_1145_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc_n(v_a_1154_, 2);
lean_dec_ref_known(v___x_1153_, 1);
v___x_1155_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14));
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_a_1154_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
lean_inc_ref(v___x_1157_);
v___x_1158_ = l_Lean_mkConst(v___x_1155_, v___x_1157_);
lean_inc_ref(v_type_1145_);
v___x_1159_ = l_Lean_Expr_app___override(v___x_1158_, v_type_1145_);
v___x_1160_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1159_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1249_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1249_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1249_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
if (lean_obj_tag(v_a_1161_) == 1)
{
lean_object* v_toCold_1165_; lean_object* v_options_1166_; lean_object* v_val_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1244_; 
lean_del_object(v___x_1163_);
v_toCold_1165_ = lean_ctor_get(v_a_1150_, 0);
v_options_1166_ = lean_ctor_get(v_toCold_1165_, 2);
v_val_1167_ = lean_ctor_get(v_a_1161_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_a_1161_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1169_ = v_a_1161_;
v_isShared_1170_ = v_isSharedCheck_1244_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_val_1167_);
lean_dec(v_a_1161_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1244_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_inheritedTraceOptions_1171_; uint8_t v_hasTrace_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; 
v_inheritedTraceOptions_1171_ = lean_ctor_get(v_toCold_1165_, 11);
v_hasTrace_1172_ = lean_ctor_get_uint8(v_options_1166_, sizeof(void*)*1);
v___x_1173_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10));
v___x_1174_ = l_Lean_mkConst(v___x_1173_, v___x_1157_);
lean_inc(v_val_1167_);
lean_inc_ref(v_type_1145_);
v___x_1175_ = l_Lean_mkAppB(v___x_1174_, v_type_1145_, v_val_1167_);
if (v_hasTrace_1172_ == 0)
{
v___y_1177_ = v_a_1146_;
v___y_1178_ = v_a_1147_;
v___y_1179_ = v_a_1148_;
v___y_1180_ = v_a_1149_;
v___y_1181_ = v_a_1150_;
v___y_1182_ = v_a_1151_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1229_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_1230_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61);
v___x_1231_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1171_, v_options_1166_, v___x_1230_);
if (v___x_1231_ == 0)
{
v___y_1177_ = v_a_1146_;
v___y_1178_ = v_a_1147_;
v___y_1179_ = v_a_1148_;
v___y_1180_ = v_a_1149_;
v___y_1181_ = v_a_1150_;
v___y_1182_ = v_a_1151_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1232_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78);
lean_inc_ref(v_type_1145_);
v___x_1233_ = l_Lean_MessageData_ofExpr(v_type_1145_);
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_1229_, v___x_1234_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_dec_ref_known(v___x_1235_, 1);
v___y_1177_ = v_a_1146_;
v___y_1178_ = v_a_1147_;
v___y_1179_ = v_a_1148_;
v___y_1180_ = v_a_1149_;
v___y_1181_ = v_a_1150_;
v___y_1182_ = v_a_1151_;
goto v___jp_1176_;
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_dec_ref(v___x_1175_);
lean_del_object(v___x_1169_);
lean_dec(v_val_1167_);
lean_dec(v_a_1154_);
lean_dec_ref(v_type_1145_);
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
v___jp_1176_:
{
lean_object* v___x_1183_; 
lean_inc_ref(v___x_1175_);
lean_inc_ref(v_type_1145_);
lean_inc(v_a_1154_);
v___x_1183_ = l_Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_a_1154_, v_type_1145_, v___x_1175_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_1178_, v___y_1181_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v_ncRings_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v_ncRings_1187_ = lean_ctor_get(v_a_1186_, 3);
lean_inc_ref(v_ncRings_1187_);
lean_dec(v_a_1186_);
v___x_1188_ = lean_array_get_size(v_ncRings_1187_);
lean_dec_ref(v_ncRings_1187_);
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v_type_1145_);
lean_ctor_set(v___x_1190_, 2, v_a_1154_);
lean_ctor_set(v___x_1190_, 3, v_val_1167_);
lean_ctor_set(v___x_1190_, 4, v___x_1175_);
lean_ctor_set(v___x_1190_, 5, v_a_1184_);
lean_ctor_set(v___x_1190_, 6, v___x_1189_);
lean_ctor_set(v___x_1190_, 7, v___x_1189_);
lean_ctor_set(v___x_1190_, 8, v___x_1189_);
lean_ctor_set(v___x_1190_, 9, v___x_1189_);
lean_ctor_set(v___x_1190_, 10, v___x_1189_);
lean_ctor_set(v___x_1190_, 11, v___x_1189_);
lean_ctor_set(v___x_1190_, 12, v___x_1189_);
lean_ctor_set(v___x_1190_, 13, v___x_1189_);
lean_ctor_set(v___x_1190_, 14, v___x_1189_);
lean_ctor_set(v___x_1190_, 15, v___x_1189_);
v___f_1191_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1191_, 0, v___x_1190_);
v___x_1192_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1193_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1192_, v___f_1191_, v___y_1178_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1203_; 
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v___x_1193_, 0);
lean_dec(v_unused_1204_);
v___x_1195_ = v___x_1193_;
v_isShared_1196_ = v_isSharedCheck_1203_;
goto v_resetjp_1194_;
}
else
{
lean_dec(v___x_1193_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1203_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1188_);
v___x_1198_ = v___x_1169_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1188_);
v___x_1198_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1198_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
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
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_del_object(v___x_1169_);
v_a_1205_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1193_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1193_);
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
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec(v_a_1184_);
lean_dec_ref(v___x_1175_);
lean_del_object(v___x_1169_);
lean_dec(v_val_1167_);
lean_dec(v_a_1154_);
lean_dec_ref(v_type_1145_);
v_a_1213_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1185_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1185_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
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
lean_dec_ref(v___x_1175_);
lean_del_object(v___x_1169_);
lean_dec(v_val_1167_);
lean_dec(v_a_1154_);
lean_dec_ref(v_type_1145_);
v_a_1221_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1183_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1183_);
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
else
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
lean_dec(v_a_1161_);
lean_dec_ref_known(v___x_1157_, 2);
lean_dec(v_a_1154_);
lean_dec_ref(v_type_1145_);
v___x_1245_ = lean_box(0);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1245_);
v___x_1247_ = v___x_1163_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
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
lean_dec_ref_known(v___x_1157_, 2);
lean_dec(v_a_1154_);
lean_dec_ref(v_type_1145_);
v_a_1250_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1160_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1160_);
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
lean_dec_ref(v_type_1145_);
v_a_1258_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1153_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1153_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___boxed(lean_object* v_type_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(v_type_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
lean_object* v_ks_1279_; lean_object* v_vs_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1306_; 
v_ks_1279_ = lean_ctor_get(v_x_1275_, 0);
v_vs_1280_ = lean_ctor_get(v_x_1275_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_x_1275_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1282_ = v_x_1275_;
v_isShared_1283_ = v_isSharedCheck_1306_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_vs_1280_);
lean_inc(v_ks_1279_);
lean_dec(v_x_1275_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1306_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = lean_array_get_size(v_ks_1279_);
v___x_1285_ = lean_nat_dec_lt(v_x_1276_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
lean_dec(v_x_1276_);
v___x_1286_ = lean_array_push(v_ks_1279_, v_x_1277_);
v___x_1287_ = lean_array_push(v_vs_1280_, v_x_1278_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v___x_1287_);
lean_ctor_set(v___x_1282_, 0, v___x_1286_);
v___x_1289_ = v___x_1282_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
lean_object* v_k_x27_1291_; size_t v___x_1292_; size_t v___x_1293_; uint8_t v___x_1294_; 
v_k_x27_1291_ = lean_array_fget_borrowed(v_ks_1279_, v_x_1276_);
v___x_1292_ = lean_ptr_addr(v_x_1277_);
v___x_1293_ = lean_ptr_addr(v_k_x27_1291_);
v___x_1294_ = lean_usize_dec_eq(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1296_; 
if (v_isShared_1283_ == 0)
{
v___x_1296_ = v___x_1282_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_ks_1279_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_vs_1280_);
v___x_1296_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_unsigned_to_nat(1u);
v___x_1298_ = lean_nat_add(v_x_1276_, v___x_1297_);
lean_dec(v_x_1276_);
v_x_1275_ = v___x_1296_;
v_x_1276_ = v___x_1298_;
goto _start;
}
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1301_ = lean_array_fset(v_ks_1279_, v_x_1276_, v_x_1277_);
v___x_1302_ = lean_array_fset(v_vs_1280_, v_x_1276_, v_x_1278_);
lean_dec(v_x_1276_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v___x_1302_);
lean_ctor_set(v___x_1282_, 0, v___x_1301_);
v___x_1304_ = v___x_1282_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1307_, lean_object* v_k_1308_, lean_object* v_v_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1307_, v___x_1310_, v_k_1308_, v_v_1309_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(lean_object* v_x_1313_, size_t v_x_1314_, size_t v_x_1315_, lean_object* v_x_1316_, lean_object* v_x_1317_){
_start:
{
if (lean_obj_tag(v_x_1313_) == 0)
{
lean_object* v_es_1318_; size_t v___x_1319_; size_t v___x_1320_; lean_object* v_j_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_es_1318_ = lean_ctor_get(v_x_1313_, 0);
v___x_1319_ = ((size_t)31ULL);
v___x_1320_ = lean_usize_land(v_x_1314_, v___x_1319_);
v_j_1321_ = lean_usize_to_nat(v___x_1320_);
v___x_1322_ = lean_array_get_size(v_es_1318_);
v___x_1323_ = lean_nat_dec_lt(v_j_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_dec(v_j_1321_);
lean_dec(v_x_1317_);
lean_dec_ref(v_x_1316_);
return v_x_1313_;
}
else
{
lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1364_; 
lean_inc_ref(v_es_1318_);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_x_1313_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v_x_1313_, 0);
lean_dec(v_unused_1365_);
v___x_1325_ = v_x_1313_;
v_isShared_1326_ = v_isSharedCheck_1364_;
goto v_resetjp_1324_;
}
else
{
lean_dec(v_x_1313_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1364_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v_v_1327_; lean_object* v___x_1328_; lean_object* v_xs_x27_1329_; lean_object* v___y_1331_; 
v_v_1327_ = lean_array_fget(v_es_1318_, v_j_1321_);
v___x_1328_ = lean_box(0);
v_xs_x27_1329_ = lean_array_fset(v_es_1318_, v_j_1321_, v___x_1328_);
switch(lean_obj_tag(v_v_1327_))
{
case 0:
{
lean_object* v_key_1336_; lean_object* v_val_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1349_; 
v_key_1336_ = lean_ctor_get(v_v_1327_, 0);
v_val_1337_ = lean_ctor_get(v_v_1327_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_v_1327_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1339_ = v_v_1327_;
v_isShared_1340_ = v_isSharedCheck_1349_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_val_1337_);
lean_inc(v_key_1336_);
lean_dec(v_v_1327_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1349_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
size_t v___x_1341_; size_t v___x_1342_; uint8_t v___x_1343_; 
v___x_1341_ = lean_ptr_addr(v_x_1316_);
v___x_1342_ = lean_ptr_addr(v_key_1336_);
v___x_1343_ = lean_usize_dec_eq(v___x_1341_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_del_object(v___x_1339_);
v___x_1344_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1336_, v_val_1337_, v_x_1316_, v_x_1317_);
v___x_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
v___y_1331_ = v___x_1345_;
goto v___jp_1330_;
}
else
{
lean_object* v___x_1347_; 
lean_dec(v_val_1337_);
lean_dec(v_key_1336_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v_x_1317_);
lean_ctor_set(v___x_1339_, 0, v_x_1316_);
v___x_1347_ = v___x_1339_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_x_1316_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_x_1317_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
v___y_1331_ = v___x_1347_;
goto v___jp_1330_;
}
}
}
}
case 1:
{
lean_object* v_node_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1362_; 
v_node_1350_ = lean_ctor_get(v_v_1327_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_v_1327_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1352_ = v_v_1327_;
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_node_1350_);
lean_dec(v_v_1327_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
size_t v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1354_ = ((size_t)5ULL);
v___x_1355_ = lean_usize_shift_right(v_x_1314_, v___x_1354_);
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_add(v_x_1315_, v___x_1356_);
v___x_1358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_node_1350_, v___x_1355_, v___x_1357_, v_x_1316_, v_x_1317_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1358_);
v___x_1360_ = v___x_1352_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
v___y_1331_ = v___x_1360_;
goto v___jp_1330_;
}
}
}
default: 
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_x_1316_);
lean_ctor_set(v___x_1363_, 1, v_x_1317_);
v___y_1331_ = v___x_1363_;
goto v___jp_1330_;
}
}
v___jp_1330_:
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1332_ = lean_array_fset(v_xs_x27_1329_, v_j_1321_, v___y_1331_);
lean_dec(v_j_1321_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1332_);
v___x_1334_ = v___x_1325_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
else
{
lean_object* v_ks_1366_; lean_object* v_vs_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1385_; 
v_ks_1366_ = lean_ctor_get(v_x_1313_, 0);
v_vs_1367_ = lean_ctor_get(v_x_1313_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_x_1313_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1369_ = v_x_1313_;
v_isShared_1370_ = v_isSharedCheck_1385_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_vs_1367_);
lean_inc(v_ks_1366_);
lean_dec(v_x_1313_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1385_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_ks_1366_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_vs_1367_);
v___x_1372_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v_newNode_1373_; size_t v___x_1374_; uint8_t v___x_1375_; 
v_newNode_1373_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v___x_1372_, v_x_1316_, v_x_1317_);
v___x_1374_ = ((size_t)7ULL);
v___x_1375_ = lean_usize_dec_le(v___x_1374_, v_x_1315_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1376_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1373_);
v___x_1377_ = lean_unsigned_to_nat(4u);
v___x_1378_ = lean_nat_dec_lt(v___x_1376_, v___x_1377_);
lean_dec(v___x_1376_);
if (v___x_1378_ == 0)
{
lean_object* v_ks_1379_; lean_object* v_vs_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_ks_1379_ = lean_ctor_get(v_newNode_1373_, 0);
lean_inc_ref(v_ks_1379_);
v_vs_1380_ = lean_ctor_get(v_newNode_1373_, 1);
lean_inc_ref(v_vs_1380_);
lean_dec_ref(v_newNode_1373_);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0);
v___x_1383_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_x_1315_, v_ks_1379_, v_vs_1380_, v___x_1381_, v___x_1382_);
lean_dec_ref(v_vs_1380_);
lean_dec_ref(v_ks_1379_);
return v___x_1383_;
}
else
{
return v_newNode_1373_;
}
}
else
{
return v_newNode_1373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_1386_, lean_object* v_keys_1387_, lean_object* v_vals_1388_, lean_object* v_i_1389_, lean_object* v_entries_1390_){
_start:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1391_ = lean_array_get_size(v_keys_1387_);
v___x_1392_ = lean_nat_dec_lt(v_i_1389_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_dec(v_i_1389_);
return v_entries_1390_;
}
else
{
lean_object* v_k_1393_; lean_object* v_v_1394_; size_t v___x_1395_; size_t v___x_1396_; size_t v___x_1397_; uint64_t v___x_1398_; size_t v_h_1399_; size_t v___x_1400_; lean_object* v___x_1401_; size_t v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; size_t v_h_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v_k_1393_ = lean_array_fget_borrowed(v_keys_1387_, v_i_1389_);
v_v_1394_ = lean_array_fget_borrowed(v_vals_1388_, v_i_1389_);
v___x_1395_ = lean_ptr_addr(v_k_1393_);
v___x_1396_ = ((size_t)3ULL);
v___x_1397_ = lean_usize_shift_right(v___x_1395_, v___x_1396_);
v___x_1398_ = lean_usize_to_uint64(v___x_1397_);
v_h_1399_ = lean_uint64_to_usize(v___x_1398_);
v___x_1400_ = ((size_t)5ULL);
v___x_1401_ = lean_unsigned_to_nat(1u);
v___x_1402_ = ((size_t)1ULL);
v___x_1403_ = lean_usize_sub(v_depth_1386_, v___x_1402_);
v___x_1404_ = lean_usize_mul(v___x_1400_, v___x_1403_);
v_h_1405_ = lean_usize_shift_right(v_h_1399_, v___x_1404_);
v___x_1406_ = lean_nat_add(v_i_1389_, v___x_1401_);
lean_dec(v_i_1389_);
lean_inc(v_v_1394_);
lean_inc(v_k_1393_);
v___x_1407_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_entries_1390_, v_h_1405_, v_depth_1386_, v_k_1393_, v_v_1394_);
v_i_1389_ = v___x_1406_;
v_entries_1390_ = v___x_1407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1409_, lean_object* v_keys_1410_, lean_object* v_vals_1411_, lean_object* v_i_1412_, lean_object* v_entries_1413_){
_start:
{
size_t v_depth_boxed_1414_; lean_object* v_res_1415_; 
v_depth_boxed_1414_ = lean_unbox_usize(v_depth_1409_);
lean_dec(v_depth_1409_);
v_res_1415_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1414_, v_keys_1410_, v_vals_1411_, v_i_1412_, v_entries_1413_);
lean_dec_ref(v_vals_1411_);
lean_dec_ref(v_keys_1410_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_){
_start:
{
size_t v_x_2146__boxed_1421_; size_t v_x_2147__boxed_1422_; lean_object* v_res_1423_; 
v_x_2146__boxed_1421_ = lean_unbox_usize(v_x_1417_);
lean_dec(v_x_1417_);
v_x_2147__boxed_1422_ = lean_unbox_usize(v_x_1418_);
lean_dec(v_x_1418_);
v_res_1423_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_1416_, v_x_2146__boxed_1421_, v_x_2147__boxed_1422_, v_x_1419_, v_x_1420_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(lean_object* v_x_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
size_t v___x_1427_; size_t v___x_1428_; size_t v___x_1429_; uint64_t v___x_1430_; size_t v___x_1431_; size_t v___x_1432_; lean_object* v___x_1433_; 
v___x_1427_ = lean_ptr_addr(v_x_1425_);
v___x_1428_ = ((size_t)3ULL);
v___x_1429_ = lean_usize_shift_right(v___x_1427_, v___x_1428_);
v___x_1430_ = lean_usize_to_uint64(v___x_1429_);
v___x_1431_ = lean_uint64_to_usize(v___x_1430_);
v___x_1432_ = ((size_t)1ULL);
v___x_1433_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_1424_, v___x_1431_, v___x_1432_, v_x_1425_, v_x_1426_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0(lean_object* v_type_1434_, lean_object* v___y_1435_, lean_object* v_s_1436_){
_start:
{
lean_object* v_exp_1437_; lean_object* v_rings_1438_; lean_object* v_semirings_1439_; lean_object* v_ncRings_1440_; lean_object* v_ncSemirings_1441_; lean_object* v_typeClassify_1442_; lean_object* v_orders_1443_; lean_object* v_typeOrderClassify_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1452_; 
v_exp_1437_ = lean_ctor_get(v_s_1436_, 0);
v_rings_1438_ = lean_ctor_get(v_s_1436_, 1);
v_semirings_1439_ = lean_ctor_get(v_s_1436_, 2);
v_ncRings_1440_ = lean_ctor_get(v_s_1436_, 3);
v_ncSemirings_1441_ = lean_ctor_get(v_s_1436_, 4);
v_typeClassify_1442_ = lean_ctor_get(v_s_1436_, 5);
v_orders_1443_ = lean_ctor_get(v_s_1436_, 6);
v_typeOrderClassify_1444_ = lean_ctor_get(v_s_1436_, 7);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_s_1436_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1446_ = v_s_1436_;
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_typeOrderClassify_1444_);
lean_inc(v_orders_1443_);
lean_inc(v_typeClassify_1442_);
lean_inc(v_ncSemirings_1441_);
lean_inc(v_ncRings_1440_);
lean_inc(v_semirings_1439_);
lean_inc(v_rings_1438_);
lean_inc(v_exp_1437_);
lean_dec(v_s_1436_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1448_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_1442_, v_type_1434_, v___y_1435_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 5, v___x_1448_);
v___x_1450_ = v___x_1446_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_exp_1437_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_rings_1438_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_semirings_1439_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v_ncRings_1440_);
lean_ctor_set(v_reuseFailAlloc_1451_, 4, v_ncSemirings_1441_);
lean_ctor_set(v_reuseFailAlloc_1451_, 5, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1451_, 6, v_orders_1443_);
lean_ctor_set(v_reuseFailAlloc_1451_, 7, v_typeOrderClassify_1444_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1453_, lean_object* v_vals_1454_, lean_object* v_i_1455_, lean_object* v_k_1456_){
_start:
{
lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1457_ = lean_array_get_size(v_keys_1453_);
v___x_1458_ = lean_nat_dec_lt(v_i_1455_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
lean_dec(v_i_1455_);
v___x_1459_ = lean_box(0);
return v___x_1459_;
}
else
{
lean_object* v_k_x27_1460_; size_t v___x_1461_; size_t v___x_1462_; uint8_t v___x_1463_; 
v_k_x27_1460_ = lean_array_fget_borrowed(v_keys_1453_, v_i_1455_);
v___x_1461_ = lean_ptr_addr(v_k_1456_);
v___x_1462_ = lean_ptr_addr(v_k_x27_1460_);
v___x_1463_ = lean_usize_dec_eq(v___x_1461_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_add(v_i_1455_, v___x_1464_);
lean_dec(v_i_1455_);
v_i_1455_ = v___x_1465_;
goto _start;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_array_fget_borrowed(v_vals_1454_, v_i_1455_);
lean_dec(v_i_1455_);
lean_inc(v___x_1467_);
v___x_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1469_, lean_object* v_vals_1470_, lean_object* v_i_1471_, lean_object* v_k_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1469_, v_vals_1470_, v_i_1471_, v_k_1472_);
lean_dec_ref(v_k_1472_);
lean_dec_ref(v_vals_1470_);
lean_dec_ref(v_keys_1469_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(lean_object* v_x_1474_, size_t v_x_1475_, lean_object* v_x_1476_){
_start:
{
if (lean_obj_tag(v_x_1474_) == 0)
{
lean_object* v_es_1477_; lean_object* v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; lean_object* v_j_1481_; lean_object* v___x_1482_; 
v_es_1477_ = lean_ctor_get(v_x_1474_, 0);
v___x_1478_ = lean_box(2);
v___x_1479_ = ((size_t)31ULL);
v___x_1480_ = lean_usize_land(v_x_1475_, v___x_1479_);
v_j_1481_ = lean_usize_to_nat(v___x_1480_);
v___x_1482_ = lean_array_get_borrowed(v___x_1478_, v_es_1477_, v_j_1481_);
lean_dec(v_j_1481_);
switch(lean_obj_tag(v___x_1482_))
{
case 0:
{
lean_object* v_key_1483_; lean_object* v_val_1484_; size_t v___x_1485_; size_t v___x_1486_; uint8_t v___x_1487_; 
v_key_1483_ = lean_ctor_get(v___x_1482_, 0);
v_val_1484_ = lean_ctor_get(v___x_1482_, 1);
v___x_1485_ = lean_ptr_addr(v_x_1476_);
v___x_1486_ = lean_ptr_addr(v_key_1483_);
v___x_1487_ = lean_usize_dec_eq(v___x_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_box(0);
return v___x_1488_;
}
else
{
lean_object* v___x_1489_; 
lean_inc(v_val_1484_);
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_val_1484_);
return v___x_1489_;
}
}
case 1:
{
lean_object* v_node_1490_; size_t v___x_1491_; size_t v___x_1492_; 
v_node_1490_ = lean_ctor_get(v___x_1482_, 0);
v___x_1491_ = ((size_t)5ULL);
v___x_1492_ = lean_usize_shift_right(v_x_1475_, v___x_1491_);
v_x_1474_ = v_node_1490_;
v_x_1475_ = v___x_1492_;
goto _start;
}
default: 
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_box(0);
return v___x_1494_;
}
}
}
else
{
lean_object* v_ks_1495_; lean_object* v_vs_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_ks_1495_ = lean_ctor_get(v_x_1474_, 0);
v_vs_1496_ = lean_ctor_get(v_x_1474_, 1);
v___x_1497_ = lean_unsigned_to_nat(0u);
v___x_1498_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1495_, v_vs_1496_, v___x_1497_, v_x_1476_);
return v___x_1498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
size_t v_x_2365__boxed_1502_; lean_object* v_res_1503_; 
v_x_2365__boxed_1502_ = lean_unbox_usize(v_x_1500_);
lean_dec(v_x_1500_);
v_res_1503_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_1499_, v_x_2365__boxed_1502_, v_x_1501_);
lean_dec_ref(v_x_1501_);
lean_dec_ref(v_x_1499_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(lean_object* v_x_1504_, lean_object* v_x_1505_){
_start:
{
size_t v___x_1506_; size_t v___x_1507_; size_t v___x_1508_; uint64_t v___x_1509_; size_t v___x_1510_; lean_object* v___x_1511_; 
v___x_1506_ = lean_ptr_addr(v_x_1505_);
v___x_1507_ = ((size_t)3ULL);
v___x_1508_ = lean_usize_shift_right(v___x_1506_, v___x_1507_);
v___x_1509_ = lean_usize_to_uint64(v___x_1508_);
v___x_1510_ = lean_uint64_to_usize(v___x_1509_);
v___x_1511_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_1504_, v___x_1510_, v_x_1505_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg___boxed(lean_object* v_x_1512_, lean_object* v_x_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_1512_, v_x_1513_);
lean_dec_ref(v_x_1513_);
lean_dec_ref(v_x_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(lean_object* v_type_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1517_, v_a_1520_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1578_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1578_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1578_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_typeClassify_1528_; lean_object* v___x_1529_; 
v_typeClassify_1528_ = lean_ctor_get(v_a_1524_, 5);
lean_inc_ref(v_typeClassify_1528_);
lean_dec(v_a_1524_);
v___x_1529_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_1528_, v_type_1515_);
lean_dec_ref(v_typeClassify_1528_);
if (lean_obj_tag(v___x_1529_) == 1)
{
lean_object* v_val_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1545_; 
lean_dec_ref(v_type_1515_);
v_val_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1545_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_val_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1545_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
if (lean_obj_tag(v_val_1530_) == 0)
{
lean_object* v_id_1534_; lean_object* v___x_1536_; 
v_id_1534_ = lean_ctor_get(v_val_1530_, 0);
lean_inc(v_id_1534_);
lean_dec_ref_known(v_val_1530_, 1);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v_id_1534_);
v___x_1536_ = v___x_1532_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_id_1534_);
v___x_1536_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1538_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1536_);
v___x_1538_ = v___x_1526_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
lean_del_object(v___x_1532_);
lean_dec(v_val_1530_);
v___x_1541_ = lean_box(0);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1541_);
v___x_1543_ = v___x_1526_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
lean_object* v___x_1546_; 
lean_dec(v___x_1529_);
lean_del_object(v___x_1526_);
lean_inc_ref(v_type_1515_);
v___x_1546_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1577_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1577_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1577_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___y_1552_; 
if (lean_obj_tag(v_a_1547_) == 0)
{
lean_object* v___x_1572_; 
lean_del_object(v___x_1549_);
v___x_1572_ = lean_box(4);
v___y_1552_ = v___x_1572_;
goto v___jp_1551_;
}
else
{
lean_object* v_val_1573_; lean_object* v___x_1575_; 
v_val_1573_ = lean_ctor_get(v_a_1547_, 0);
lean_inc(v_val_1573_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v_val_1573_);
v___x_1575_ = v___x_1549_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_val_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
v___y_1552_ = v___x_1575_;
goto v___jp_1551_;
}
}
v___jp_1551_:
{
lean_object* v___f_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___f_1553_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1553_, 0, v_type_1515_);
lean_closure_set(v___f_1553_, 1, v___y_1552_);
v___x_1554_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1555_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1554_, v___f_1553_, v_a_1517_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v___x_1555_, 0);
lean_dec(v_unused_1563_);
v___x_1557_ = v___x_1555_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_dec(v___x_1555_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v_a_1547_);
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1547_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_a_1547_);
v_a_1564_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1555_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1555_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_type_1515_);
return v___x_1546_;
}
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec_ref(v_type_1515_);
v_a_1579_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1523_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1523_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___boxed(lean_object* v_type_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(v_type_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(lean_object* v_00_u03b2_1596_, lean_object* v_x_1597_, lean_object* v_x_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_1597_, v_x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___boxed(lean_object* v_00_u03b2_1600_, lean_object* v_x_1601_, lean_object* v_x_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(v_00_u03b2_1600_, v_x_1601_, v_x_1602_);
lean_dec_ref(v_x_1602_);
lean_dec_ref(v_x_1601_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1(lean_object* v_00_u03b2_1604_, lean_object* v_x_1605_, lean_object* v_x_1606_, lean_object* v_x_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_x_1605_, v_x_1606_, v_x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1609_, lean_object* v_x_1610_, size_t v_x_1611_, lean_object* v_x_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_1610_, v_x_1611_, v_x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_, lean_object* v_x_1617_){
_start:
{
size_t v_x_2581__boxed_1618_; lean_object* v_res_1619_; 
v_x_2581__boxed_1618_ = lean_unbox_usize(v_x_1616_);
lean_dec(v_x_1616_);
v_res_1619_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(v_00_u03b2_1614_, v_x_1615_, v_x_2581__boxed_1618_, v_x_1617_);
lean_dec_ref(v_x_1617_);
lean_dec_ref(v_x_1615_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(lean_object* v_00_u03b2_1620_, lean_object* v_x_1621_, size_t v_x_1622_, size_t v_x_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_1621_, v_x_1622_, v_x_1623_, v_x_1624_, v_x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_){
_start:
{
size_t v_x_2592__boxed_1633_; size_t v_x_2593__boxed_1634_; lean_object* v_res_1635_; 
v_x_2592__boxed_1633_ = lean_unbox_usize(v_x_1629_);
lean_dec(v_x_1629_);
v_x_2593__boxed_1634_ = lean_unbox_usize(v_x_1630_);
lean_dec(v_x_1630_);
v_res_1635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(v_00_u03b2_1627_, v_x_1628_, v_x_2592__boxed_1633_, v_x_2593__boxed_1634_, v_x_1631_, v_x_1632_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1636_, lean_object* v_keys_1637_, lean_object* v_vals_1638_, lean_object* v_heq_1639_, lean_object* v_i_1640_, lean_object* v_k_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1637_, v_vals_1638_, v_i_1640_, v_k_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1643_, lean_object* v_keys_1644_, lean_object* v_vals_1645_, lean_object* v_heq_1646_, lean_object* v_i_1647_, lean_object* v_k_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1643_, v_keys_1644_, v_vals_1645_, v_heq_1646_, v_i_1647_, v_k_1648_);
lean_dec_ref(v_k_1648_);
lean_dec_ref(v_vals_1645_);
lean_dec_ref(v_keys_1644_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1650_, lean_object* v_n_1651_, lean_object* v_k_1652_, lean_object* v_v_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v_n_1651_, v_k_1652_, v_v_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1655_, size_t v_depth_1656_, lean_object* v_keys_1657_, lean_object* v_vals_1658_, lean_object* v_heq_1659_, lean_object* v_i_1660_, lean_object* v_entries_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_1656_, v_keys_1657_, v_vals_1658_, v_i_1660_, v_entries_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1663_, lean_object* v_depth_1664_, lean_object* v_keys_1665_, lean_object* v_vals_1666_, lean_object* v_heq_1667_, lean_object* v_i_1668_, lean_object* v_entries_1669_){
_start:
{
size_t v_depth_boxed_1670_; lean_object* v_res_1671_; 
v_depth_boxed_1670_ = lean_unbox_usize(v_depth_1664_);
lean_dec(v_depth_1664_);
v_res_1671_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1663_, v_depth_boxed_1670_, v_keys_1665_, v_vals_1666_, v_heq_1667_, v_i_1668_, v_entries_1669_);
lean_dec_ref(v_vals_1666_);
lean_dec_ref(v_keys_1665_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1672_, lean_object* v_x_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1673_, v_x_1674_, v_x_1675_, v_x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(lean_object* v_val_1678_, lean_object* v___x_1679_, lean_object* v_s_1680_){
_start:
{
lean_object* v_exp_1681_; lean_object* v_rings_1682_; lean_object* v_semirings_1683_; lean_object* v_ncRings_1684_; lean_object* v_ncSemirings_1685_; lean_object* v_typeClassify_1686_; lean_object* v_orders_1687_; lean_object* v_typeOrderClassify_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v_exp_1681_ = lean_ctor_get(v_s_1680_, 0);
v_rings_1682_ = lean_ctor_get(v_s_1680_, 1);
v_semirings_1683_ = lean_ctor_get(v_s_1680_, 2);
v_ncRings_1684_ = lean_ctor_get(v_s_1680_, 3);
v_ncSemirings_1685_ = lean_ctor_get(v_s_1680_, 4);
v_typeClassify_1686_ = lean_ctor_get(v_s_1680_, 5);
v_orders_1687_ = lean_ctor_get(v_s_1680_, 6);
v_typeOrderClassify_1688_ = lean_ctor_get(v_s_1680_, 7);
v___x_1689_ = lean_array_get_size(v_rings_1682_);
v___x_1690_ = lean_nat_dec_lt(v_val_1678_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_dec(v___x_1679_);
return v_s_1680_;
}
else
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1718_; 
lean_inc_ref(v_typeOrderClassify_1688_);
lean_inc_ref(v_orders_1687_);
lean_inc_ref(v_typeClassify_1686_);
lean_inc_ref(v_ncSemirings_1685_);
lean_inc_ref(v_ncRings_1684_);
lean_inc_ref(v_semirings_1683_);
lean_inc_ref(v_rings_1682_);
lean_inc(v_exp_1681_);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_s_1680_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; lean_object* v_unused_1720_; lean_object* v_unused_1721_; lean_object* v_unused_1722_; lean_object* v_unused_1723_; lean_object* v_unused_1724_; lean_object* v_unused_1725_; lean_object* v_unused_1726_; 
v_unused_1719_ = lean_ctor_get(v_s_1680_, 7);
lean_dec(v_unused_1719_);
v_unused_1720_ = lean_ctor_get(v_s_1680_, 6);
lean_dec(v_unused_1720_);
v_unused_1721_ = lean_ctor_get(v_s_1680_, 5);
lean_dec(v_unused_1721_);
v_unused_1722_ = lean_ctor_get(v_s_1680_, 4);
lean_dec(v_unused_1722_);
v_unused_1723_ = lean_ctor_get(v_s_1680_, 3);
lean_dec(v_unused_1723_);
v_unused_1724_ = lean_ctor_get(v_s_1680_, 2);
lean_dec(v_unused_1724_);
v_unused_1725_ = lean_ctor_get(v_s_1680_, 1);
lean_dec(v_unused_1725_);
v_unused_1726_ = lean_ctor_get(v_s_1680_, 0);
lean_dec(v_unused_1726_);
v___x_1692_ = v_s_1680_;
v_isShared_1693_ = v_isSharedCheck_1718_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v_s_1680_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1718_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_v_1694_; lean_object* v_toRing_1695_; lean_object* v_invFn_x3f_1696_; lean_object* v_divFn_x3f_1697_; lean_object* v_commSemiringInst_1698_; lean_object* v_commRingInst_1699_; lean_object* v_noZeroDivInst_x3f_1700_; lean_object* v_fieldInst_x3f_1701_; lean_object* v_powIdentityInst_x3f_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1716_; 
v_v_1694_ = lean_array_fget(v_rings_1682_, v_val_1678_);
v_toRing_1695_ = lean_ctor_get(v_v_1694_, 0);
v_invFn_x3f_1696_ = lean_ctor_get(v_v_1694_, 1);
v_divFn_x3f_1697_ = lean_ctor_get(v_v_1694_, 2);
v_commSemiringInst_1698_ = lean_ctor_get(v_v_1694_, 4);
v_commRingInst_1699_ = lean_ctor_get(v_v_1694_, 5);
v_noZeroDivInst_x3f_1700_ = lean_ctor_get(v_v_1694_, 6);
v_fieldInst_x3f_1701_ = lean_ctor_get(v_v_1694_, 7);
v_powIdentityInst_x3f_1702_ = lean_ctor_get(v_v_1694_, 8);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_v_1694_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v_v_1694_, 3);
lean_dec(v_unused_1717_);
v___x_1704_ = v_v_1694_;
v_isShared_1705_ = v_isSharedCheck_1716_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1702_);
lean_inc(v_fieldInst_x3f_1701_);
lean_inc(v_noZeroDivInst_x3f_1700_);
lean_inc(v_commRingInst_1699_);
lean_inc(v_commSemiringInst_1698_);
lean_inc(v_divFn_x3f_1697_);
lean_inc(v_invFn_x3f_1696_);
lean_inc(v_toRing_1695_);
lean_dec(v_v_1694_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1716_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v_xs_x27_1707_; lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1706_ = lean_box(0);
v_xs_x27_1707_ = lean_array_fset(v_rings_1682_, v_val_1678_, v___x_1706_);
v___x_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1679_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 3, v___x_1708_);
v___x_1710_ = v___x_1704_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_toRing_1695_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_invFn_x3f_1696_);
lean_ctor_set(v_reuseFailAlloc_1715_, 2, v_divFn_x3f_1697_);
lean_ctor_set(v_reuseFailAlloc_1715_, 3, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1715_, 4, v_commSemiringInst_1698_);
lean_ctor_set(v_reuseFailAlloc_1715_, 5, v_commRingInst_1699_);
lean_ctor_set(v_reuseFailAlloc_1715_, 6, v_noZeroDivInst_x3f_1700_);
lean_ctor_set(v_reuseFailAlloc_1715_, 7, v_fieldInst_x3f_1701_);
lean_ctor_set(v_reuseFailAlloc_1715_, 8, v_powIdentityInst_x3f_1702_);
v___x_1710_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1711_ = lean_array_fset(v_xs_x27_1707_, v_val_1678_, v___x_1710_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v___x_1711_);
v___x_1713_ = v___x_1692_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_exp_1681_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1714_, 2, v_semirings_1683_);
lean_ctor_set(v_reuseFailAlloc_1714_, 3, v_ncRings_1684_);
lean_ctor_set(v_reuseFailAlloc_1714_, 4, v_ncSemirings_1685_);
lean_ctor_set(v_reuseFailAlloc_1714_, 5, v_typeClassify_1686_);
lean_ctor_set(v_reuseFailAlloc_1714_, 6, v_orders_1687_);
lean_ctor_set(v_reuseFailAlloc_1714_, 7, v_typeOrderClassify_1688_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0___boxed(lean_object* v_val_1727_, lean_object* v___x_1728_, lean_object* v_s_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(v_val_1727_, v___x_1728_, v_s_1729_);
lean_dec(v_val_1727_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(lean_object* v___x_1731_, lean_object* v_s_1732_){
_start:
{
lean_object* v_exp_1733_; lean_object* v_rings_1734_; lean_object* v_semirings_1735_; lean_object* v_ncRings_1736_; lean_object* v_ncSemirings_1737_; lean_object* v_typeClassify_1738_; lean_object* v_orders_1739_; lean_object* v_typeOrderClassify_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1748_; 
v_exp_1733_ = lean_ctor_get(v_s_1732_, 0);
v_rings_1734_ = lean_ctor_get(v_s_1732_, 1);
v_semirings_1735_ = lean_ctor_get(v_s_1732_, 2);
v_ncRings_1736_ = lean_ctor_get(v_s_1732_, 3);
v_ncSemirings_1737_ = lean_ctor_get(v_s_1732_, 4);
v_typeClassify_1738_ = lean_ctor_get(v_s_1732_, 5);
v_orders_1739_ = lean_ctor_get(v_s_1732_, 6);
v_typeOrderClassify_1740_ = lean_ctor_get(v_s_1732_, 7);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_s_1732_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1742_ = v_s_1732_;
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_typeOrderClassify_1740_);
lean_inc(v_orders_1739_);
lean_inc(v_typeClassify_1738_);
lean_inc(v_ncSemirings_1737_);
lean_inc(v_ncRings_1736_);
lean_inc(v_semirings_1735_);
lean_inc(v_rings_1734_);
lean_inc(v_exp_1733_);
lean_dec(v_s_1732_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1744_ = lean_array_push(v_semirings_1735_, v___x_1731_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 2, v___x_1744_);
v___x_1746_ = v___x_1742_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_exp_1733_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_rings_1734_);
lean_ctor_set(v_reuseFailAlloc_1747_, 2, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1747_, 3, v_ncRings_1736_);
lean_ctor_set(v_reuseFailAlloc_1747_, 4, v_ncSemirings_1737_);
lean_ctor_set(v_reuseFailAlloc_1747_, 5, v_typeClassify_1738_);
lean_ctor_set(v_reuseFailAlloc_1747_, 6, v_orders_1739_);
lean_ctor_set(v_reuseFailAlloc_1747_, 7, v_typeOrderClassify_1740_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0));
v___x_1751_ = l_Lean_stringToMessageData(v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(lean_object* v_type_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v___x_1763_; 
lean_inc_ref(v_type_1752_);
v___x_1763_ = l_Lean_Meta_getDecLevel(v_type_1752_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc_n(v_a_1764_, 2);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18));
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_a_1764_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
lean_inc_ref(v___x_1767_);
v___x_1768_ = l_Lean_mkConst(v___x_1765_, v___x_1767_);
lean_inc_ref(v_type_1752_);
v___x_1769_ = l_Lean_Expr_app___override(v___x_1768_, v_type_1752_);
v___x_1770_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1769_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1883_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1883_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1883_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
if (lean_obj_tag(v_a_1771_) == 1)
{
lean_object* v_val_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_del_object(v___x_1773_);
v_val_1775_ = lean_ctor_get(v_a_1771_, 0);
lean_inc_n(v_val_1775_, 2);
lean_dec_ref_known(v_a_1771_, 1);
v___x_1776_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2));
lean_inc_ref(v___x_1767_);
v___x_1777_ = l_Lean_mkConst(v___x_1776_, v___x_1767_);
lean_inc_ref_n(v_type_1752_, 2);
v___x_1778_ = l_Lean_mkAppB(v___x_1777_, v_type_1752_, v_val_1775_);
v___x_1779_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1));
v___x_1780_ = l_Lean_mkConst(v___x_1779_, v___x_1767_);
lean_inc_ref(v___x_1778_);
v___x_1781_ = l_Lean_mkAppB(v___x_1780_, v_type_1752_, v___x_1778_);
v___x_1782_ = l_Lean_Meta_Sym_canon(v___x_1781_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v___x_1784_ = l_Lean_Meta_Sym_shareCommon(v_a_1783_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc_n(v_a_1785_, 2);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(v_a_1785_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
if (lean_obj_tag(v_a_1787_) == 1)
{
lean_object* v_val_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_a_1785_);
v_val_1788_ = lean_ctor_get(v_a_1787_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_a_1787_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1790_ = v_a_1787_;
v_isShared_1791_ = v_isSharedCheck_1839_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_val_1788_);
lean_dec(v_a_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1839_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1754_, v_a_1757_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v_semirings_1794_; lean_object* v___x_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___f_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v_semirings_1794_ = lean_ctor_get(v_a_1793_, 2);
lean_inc_ref(v_semirings_1794_);
lean_dec(v_a_1793_);
v___x_1795_ = lean_array_get_size(v_semirings_1794_);
lean_dec_ref(v_semirings_1794_);
lean_inc(v_val_1788_);
v___f_1796_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1796_, 0, v_val_1788_);
lean_closure_set(v___f_1796_, 1, v___x_1795_);
v___x_1797_ = lean_box(0);
v___x_1798_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1795_);
lean_ctor_set(v___x_1798_, 1, v_type_1752_);
lean_ctor_set(v___x_1798_, 2, v_a_1764_);
lean_ctor_set(v___x_1798_, 3, v___x_1778_);
lean_ctor_set(v___x_1798_, 4, v___x_1797_);
lean_ctor_set(v___x_1798_, 5, v___x_1797_);
lean_ctor_set(v___x_1798_, 6, v___x_1797_);
lean_ctor_set(v___x_1798_, 7, v___x_1797_);
lean_ctor_set(v___x_1798_, 8, v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v_val_1788_);
lean_ctor_set(v___x_1799_, 2, v_val_1775_);
lean_ctor_set(v___x_1799_, 3, v___x_1797_);
lean_ctor_set(v___x_1799_, 4, v___x_1797_);
v___f_1800_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1), 2, 1);
lean_closure_set(v___f_1800_, 0, v___x_1799_);
v___x_1801_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1802_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1801_, v___f_1800_, v_a_1754_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v___x_1803_; 
lean_dec_ref_known(v___x_1802_, 1);
v___x_1803_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1801_, v___f_1796_, v_a_1754_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1813_; 
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v___x_1803_, 0);
lean_dec(v_unused_1814_);
v___x_1805_ = v___x_1803_;
v_isShared_1806_ = v_isSharedCheck_1813_;
goto v_resetjp_1804_;
}
else
{
lean_dec(v___x_1803_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1813_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1795_);
v___x_1808_ = v___x_1790_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1795_);
v___x_1808_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1810_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1808_);
v___x_1810_ = v___x_1805_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_del_object(v___x_1790_);
v_a_1815_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1803_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1803_);
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
lean_dec_ref(v___f_1796_);
lean_del_object(v___x_1790_);
v_a_1823_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1802_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1802_);
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
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_del_object(v___x_1790_);
lean_dec(v_val_1788_);
lean_dec_ref(v___x_1778_);
lean_dec(v_val_1775_);
lean_dec(v_a_1764_);
lean_dec_ref(v_type_1752_);
v_a_1831_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1792_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1792_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
lean_dec(v_a_1787_);
lean_dec_ref(v___x_1778_);
lean_dec(v_val_1775_);
lean_dec(v_a_1764_);
lean_dec_ref(v_type_1752_);
v___x_1840_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1);
v___x_1841_ = l_Lean_indentExpr(v_a_1785_);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1753_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; uint8_t v_verbose_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v_verbose_1845_ = lean_ctor_get_uint8(v_a_1844_, 0);
lean_dec(v_a_1844_);
if (v_verbose_1845_ == 0)
{
lean_dec_ref_known(v___x_1842_, 2);
goto v___jp_1760_;
}
else
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_Meta_Sym_reportIssue(v___x_1842_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_dec_ref_known(v___x_1846_, 1);
goto v___jp_1760_;
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec_ref_known(v___x_1842_, 2);
v_a_1855_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1843_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1843_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
else
{
lean_dec(v_a_1785_);
lean_dec_ref(v___x_1778_);
lean_dec(v_val_1775_);
lean_dec(v_a_1764_);
lean_dec_ref(v_type_1752_);
return v___x_1786_;
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v___x_1778_);
lean_dec(v_val_1775_);
lean_dec(v_a_1764_);
lean_dec_ref(v_type_1752_);
v_a_1863_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1784_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1784_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v___x_1778_);
lean_dec(v_val_1775_);
lean_dec(v_a_1764_);
lean_dec_ref(v_type_1752_);
v_a_1871_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1782_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1782_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
lean_dec(v_a_1771_);
lean_dec_ref_known(v___x_1767_, 2);
lean_dec(v_a_1764_);
lean_dec_ref(v_type_1752_);
v___x_1879_ = lean_box(0);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1879_);
v___x_1881_ = v___x_1773_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref_known(v___x_1767_, 2);
lean_dec(v_a_1764_);
lean_dec_ref(v_type_1752_);
v_a_1884_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1770_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1770_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec_ref(v_type_1752_);
v_a_1892_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1763_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1763_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
v___jp_1760_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_box(0);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___boxed(lean_object* v_type_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(v_type_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0(lean_object* v___x_1909_, lean_object* v_s_1910_){
_start:
{
lean_object* v_exp_1911_; lean_object* v_rings_1912_; lean_object* v_semirings_1913_; lean_object* v_ncRings_1914_; lean_object* v_ncSemirings_1915_; lean_object* v_typeClassify_1916_; lean_object* v_orders_1917_; lean_object* v_typeOrderClassify_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1926_; 
v_exp_1911_ = lean_ctor_get(v_s_1910_, 0);
v_rings_1912_ = lean_ctor_get(v_s_1910_, 1);
v_semirings_1913_ = lean_ctor_get(v_s_1910_, 2);
v_ncRings_1914_ = lean_ctor_get(v_s_1910_, 3);
v_ncSemirings_1915_ = lean_ctor_get(v_s_1910_, 4);
v_typeClassify_1916_ = lean_ctor_get(v_s_1910_, 5);
v_orders_1917_ = lean_ctor_get(v_s_1910_, 6);
v_typeOrderClassify_1918_ = lean_ctor_get(v_s_1910_, 7);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_s_1910_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1920_ = v_s_1910_;
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_typeOrderClassify_1918_);
lean_inc(v_orders_1917_);
lean_inc(v_typeClassify_1916_);
lean_inc(v_ncSemirings_1915_);
lean_inc(v_ncRings_1914_);
lean_inc(v_semirings_1913_);
lean_inc(v_rings_1912_);
lean_inc(v_exp_1911_);
lean_dec(v_s_1910_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1922_ = lean_array_push(v_ncSemirings_1915_, v___x_1909_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 4, v___x_1922_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_exp_1911_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_rings_1912_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v_semirings_1913_);
lean_ctor_set(v_reuseFailAlloc_1925_, 3, v_ncRings_1914_);
lean_ctor_set(v_reuseFailAlloc_1925_, 4, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1925_, 5, v_typeClassify_1916_);
lean_ctor_set(v_reuseFailAlloc_1925_, 6, v_orders_1917_);
lean_ctor_set(v_reuseFailAlloc_1925_, 7, v_typeOrderClassify_1918_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(lean_object* v_type_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v___x_1934_; 
lean_inc_ref(v_type_1927_);
v___x_1934_ = l_Lean_Meta_getDecLevel(v_type_1927_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc_n(v_a_1935_, 2);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1936_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16));
v___x_1937_ = lean_box(0);
v___x_1938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_a_1935_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = l_Lean_mkConst(v___x_1936_, v___x_1938_);
lean_inc_ref(v_type_1927_);
v___x_1940_ = l_Lean_Expr_app___override(v___x_1939_, v_type_1927_);
v___x_1941_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1940_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1991_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1991_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1991_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
if (lean_obj_tag(v_a_1942_) == 1)
{
lean_object* v_val_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1986_; 
lean_del_object(v___x_1944_);
v_val_1946_ = lean_ctor_get(v_a_1942_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_a_1942_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1948_ = v_a_1942_;
v_isShared_1949_ = v_isSharedCheck_1986_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_val_1946_);
lean_dec(v_a_1942_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1986_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1928_, v_a_1931_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v_ncSemirings_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___f_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v_ncSemirings_1952_ = lean_ctor_get(v_a_1951_, 4);
lean_inc_ref(v_ncSemirings_1952_);
lean_dec(v_a_1951_);
v___x_1953_ = lean_array_get_size(v_ncSemirings_1952_);
lean_dec_ref(v_ncSemirings_1952_);
v___x_1954_ = lean_box(0);
v___x_1955_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v_type_1927_);
lean_ctor_set(v___x_1955_, 2, v_a_1935_);
lean_ctor_set(v___x_1955_, 3, v_val_1946_);
lean_ctor_set(v___x_1955_, 4, v___x_1954_);
lean_ctor_set(v___x_1955_, 5, v___x_1954_);
lean_ctor_set(v___x_1955_, 6, v___x_1954_);
lean_ctor_set(v___x_1955_, 7, v___x_1954_);
lean_ctor_set(v___x_1955_, 8, v___x_1954_);
v___f_1956_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1956_, 0, v___x_1955_);
v___x_1957_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1958_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1957_, v___f_1956_, v_a_1928_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1968_; 
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; 
v_unused_1969_ = lean_ctor_get(v___x_1958_, 0);
lean_dec(v_unused_1969_);
v___x_1960_ = v___x_1958_;
v_isShared_1961_ = v_isSharedCheck_1968_;
goto v_resetjp_1959_;
}
else
{
lean_dec(v___x_1958_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1968_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1953_);
v___x_1963_ = v___x_1948_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1953_);
v___x_1963_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1965_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1963_);
v___x_1965_ = v___x_1960_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_del_object(v___x_1948_);
v_a_1970_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1958_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1958_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_del_object(v___x_1948_);
lean_dec(v_val_1946_);
lean_dec(v_a_1935_);
lean_dec_ref(v_type_1927_);
v_a_1978_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1950_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1950_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1989_; 
lean_dec(v_a_1942_);
lean_dec(v_a_1935_);
lean_dec_ref(v_type_1927_);
v___x_1987_ = lean_box(0);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1987_);
v___x_1989_ = v___x_1944_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_a_1935_);
lean_dec_ref(v_type_1927_);
v_a_1992_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1941_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1941_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec_ref(v_type_1927_);
v_a_2000_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1934_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1934_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___boxed(lean_object* v_type_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(lean_object* v_type_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2016_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___boxed(lean_object* v_type_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(v_type_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(lean_object* v_type_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v___x_2042_; 
lean_inc_ref(v_type_2034_);
v___x_2042_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2137_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2137_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2137_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
if (lean_obj_tag(v_a_2043_) == 1)
{
lean_object* v_val_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v_type_2034_);
v_val_2047_ = lean_ctor_get(v_a_2043_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_a_2043_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2049_ = v_a_2043_;
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_val_2047_);
lean_dec(v_a_2043_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set_tag(v___x_2049_, 0);
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_val_2047_);
v___x_2052_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2054_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2052_);
v___x_2054_ = v___x_2045_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v___x_2058_; 
lean_del_object(v___x_2045_);
lean_dec(v_a_2043_);
lean_inc_ref(v_type_2034_);
v___x_2058_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(v_type_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2128_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2128_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2128_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
if (lean_obj_tag(v_a_2059_) == 1)
{
lean_object* v_val_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v_type_2034_);
v_val_2063_ = lean_ctor_get(v_a_2059_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_a_2059_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2065_ = v_a_2059_;
v_isShared_2066_ = v_isSharedCheck_2073_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_val_2063_);
lean_dec(v_a_2059_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2073_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_val_2063_);
v___x_2068_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2070_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2068_);
v___x_2070_ = v___x_2061_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_object* v___x_2074_; 
lean_del_object(v___x_2061_);
lean_dec(v_a_2059_);
lean_inc_ref(v_type_2034_);
v___x_2074_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(v_type_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2119_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2119_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2119_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
if (lean_obj_tag(v_a_2075_) == 1)
{
lean_object* v_val_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref(v_type_2034_);
v_val_2079_ = lean_ctor_get(v_a_2075_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_a_2075_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2081_ = v_a_2075_;
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_val_2079_);
lean_dec(v_a_2075_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set_tag(v___x_2081_, 2);
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_val_2079_);
v___x_2084_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2086_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2084_);
v___x_2086_ = v___x_2077_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v___x_2090_; 
lean_del_object(v___x_2077_);
lean_dec(v_a_2075_);
v___x_2090_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2034_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2110_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2110_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2110_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
if (lean_obj_tag(v_a_2091_) == 1)
{
lean_object* v_val_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2105_; 
v_val_2095_ = lean_ctor_get(v_a_2091_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_a_2091_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2097_ = v_a_2091_;
v_isShared_2098_ = v_isSharedCheck_2105_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_val_2095_);
lean_dec(v_a_2091_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2105_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set_tag(v___x_2097_, 3);
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_val_2095_);
v___x_2100_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2102_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2100_);
v___x_2102_ = v___x_2093_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
lean_dec(v_a_2091_);
v___x_2106_ = lean_box(4);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2106_);
v___x_2108_ = v___x_2093_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2090_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2090_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v_type_2034_);
v_a_2120_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2074_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2074_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec_ref(v_type_2034_);
v_a_2129_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2058_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2058_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v_type_2034_);
v_a_2138_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2042_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2042_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go___boxed(lean_object* v_type_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(v_type_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___lam__0(lean_object* v_type_2155_, lean_object* v_a_2156_, lean_object* v_s_2157_){
_start:
{
lean_object* v_exp_2158_; lean_object* v_rings_2159_; lean_object* v_semirings_2160_; lean_object* v_ncRings_2161_; lean_object* v_ncSemirings_2162_; lean_object* v_typeClassify_2163_; lean_object* v_orders_2164_; lean_object* v_typeOrderClassify_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2173_; 
v_exp_2158_ = lean_ctor_get(v_s_2157_, 0);
v_rings_2159_ = lean_ctor_get(v_s_2157_, 1);
v_semirings_2160_ = lean_ctor_get(v_s_2157_, 2);
v_ncRings_2161_ = lean_ctor_get(v_s_2157_, 3);
v_ncSemirings_2162_ = lean_ctor_get(v_s_2157_, 4);
v_typeClassify_2163_ = lean_ctor_get(v_s_2157_, 5);
v_orders_2164_ = lean_ctor_get(v_s_2157_, 6);
v_typeOrderClassify_2165_ = lean_ctor_get(v_s_2157_, 7);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_s_2157_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2167_ = v_s_2157_;
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_typeOrderClassify_2165_);
lean_inc(v_orders_2164_);
lean_inc(v_typeClassify_2163_);
lean_inc(v_ncSemirings_2162_);
lean_inc(v_ncRings_2161_);
lean_inc(v_semirings_2160_);
lean_inc(v_rings_2159_);
lean_inc(v_exp_2158_);
lean_dec(v_s_2157_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_2163_, v_type_2155_, v_a_2156_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 5, v___x_2169_);
v___x_2171_ = v___x_2167_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_exp_2158_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_rings_2159_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_semirings_2160_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_ncRings_2161_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_ncSemirings_2162_);
lean_ctor_set(v_reuseFailAlloc_2172_, 5, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2172_, 6, v_orders_2164_);
lean_ctor_set(v_reuseFailAlloc_2172_, 7, v_typeOrderClassify_2165_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f(lean_object* v_type_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2176_, v_a_2179_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2214_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2185_ = v___x_2182_;
v_isShared_2186_ = v_isSharedCheck_2214_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2182_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2214_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v_typeClassify_2187_; lean_object* v___x_2188_; 
v_typeClassify_2187_ = lean_ctor_get(v_a_2183_, 5);
lean_inc_ref(v_typeClassify_2187_);
lean_dec(v_a_2183_);
v___x_2188_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_2187_, v_type_2174_);
lean_dec_ref(v_typeClassify_2187_);
if (lean_obj_tag(v___x_2188_) == 1)
{
lean_object* v_val_2189_; lean_object* v___x_2191_; 
lean_dec_ref(v_type_2174_);
v_val_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_val_2189_);
lean_dec_ref_known(v___x_2188_, 1);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v_val_2189_);
v___x_2191_ = v___x_2185_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_val_2189_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
else
{
lean_object* v___x_2193_; 
lean_dec(v___x_2188_);
lean_del_object(v___x_2185_);
lean_inc_ref(v_type_2174_);
v___x_2193_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(v_type_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc_n(v_a_2194_, 2);
lean_dec_ref_known(v___x_2193_, 1);
v___f_2195_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_classify_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2195_, 0, v_type_2174_);
lean_closure_set(v___f_2195_, 1, v_a_2194_);
v___x_2196_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2197_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2196_, v___f_2195_, v_a_2176_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; 
v_unused_2205_ = lean_ctor_get(v___x_2197_, 0);
lean_dec(v_unused_2205_);
v___x_2199_ = v___x_2197_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_dec(v___x_2197_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v_a_2194_);
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2194_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_a_2194_);
v_a_2206_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2197_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2197_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_dec_ref(v_type_2174_);
return v___x_2193_;
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec_ref(v_type_2174_);
v_a_2215_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2182_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2182_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___boxed(lean_object* v_type_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Meta_Sym_Arith_classify_x3f(v_type_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(lean_object* v_fn_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_Meta_Sym_canon(v_fn_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2242_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v___x_2242_ = l_Lean_Meta_Sym_shareCommon(v_a_2241_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
return v___x_2242_;
}
else
{
return v___x_2240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn___boxed(lean_object* v_fn_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(v_fn_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(lean_object* v_u_2257_, lean_object* v_type_2258_, lean_object* v_semiringInst_2259_, lean_object* v_leInst_2260_, lean_object* v_ltInst_2261_, lean_object* v_isPreorderInst_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2269_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_2270_ = lean_box(0);
v___x_2271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2271_, 0, v_u_2257_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = l_Lean_mkConst(v___x_2269_, v___x_2271_);
v___x_2273_ = l_Lean_mkApp5(v___x_2272_, v_type_2258_, v_semiringInst_2259_, v_leInst_2260_, v_ltInst_2261_, v_isPreorderInst_2262_);
v___x_2274_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2273_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_2275_, lean_object* v_type_2276_, lean_object* v_semiringInst_2277_, lean_object* v_leInst_2278_, lean_object* v_ltInst_2279_, lean_object* v_isPreorderInst_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_u_2275_, v_type_2276_, v_semiringInst_2277_, v_leInst_2278_, v_ltInst_2279_, v_isPreorderInst_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
lean_dec(v_a_2285_);
lean_dec_ref(v_a_2284_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
lean_dec(v_a_2281_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f(lean_object* v_u_2288_, lean_object* v_type_2289_, lean_object* v_semiringInst_2290_, lean_object* v_leInst_2291_, lean_object* v_ltInst_2292_, lean_object* v_isPreorderInst_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_u_2288_, v_type_2289_, v_semiringInst_2290_, v_leInst_2291_, v_ltInst_2292_, v_isPreorderInst_2293_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___boxed(lean_object* v_u_2302_, lean_object* v_type_2303_, lean_object* v_semiringInst_2304_, lean_object* v_leInst_2305_, lean_object* v_ltInst_2306_, lean_object* v_isPreorderInst_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f(v_u_2302_, v_type_2303_, v_semiringInst_2304_, v_leInst_2305_, v_ltInst_2306_, v_isPreorderInst_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f_spec__0(lean_object* v_msg_2316_){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = l_Lean_instInhabitedExpr;
v___x_2318_ = lean_panic_fn_borrowed(v___x_2317_, v_msg_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___lam__0(lean_object* v___x_2319_, lean_object* v_s_2320_){
_start:
{
lean_object* v_exp_2321_; lean_object* v_rings_2322_; lean_object* v_semirings_2323_; lean_object* v_ncRings_2324_; lean_object* v_ncSemirings_2325_; lean_object* v_typeClassify_2326_; lean_object* v_orders_2327_; lean_object* v_typeOrderClassify_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2336_; 
v_exp_2321_ = lean_ctor_get(v_s_2320_, 0);
v_rings_2322_ = lean_ctor_get(v_s_2320_, 1);
v_semirings_2323_ = lean_ctor_get(v_s_2320_, 2);
v_ncRings_2324_ = lean_ctor_get(v_s_2320_, 3);
v_ncSemirings_2325_ = lean_ctor_get(v_s_2320_, 4);
v_typeClassify_2326_ = lean_ctor_get(v_s_2320_, 5);
v_orders_2327_ = lean_ctor_get(v_s_2320_, 6);
v_typeOrderClassify_2328_ = lean_ctor_get(v_s_2320_, 7);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_s_2320_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2330_ = v_s_2320_;
v_isShared_2331_ = v_isSharedCheck_2336_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_typeOrderClassify_2328_);
lean_inc(v_orders_2327_);
lean_inc(v_typeClassify_2326_);
lean_inc(v_ncSemirings_2325_);
lean_inc(v_ncRings_2324_);
lean_inc(v_semirings_2323_);
lean_inc(v_rings_2322_);
lean_inc(v_exp_2321_);
lean_dec(v_s_2320_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2336_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2332_ = lean_array_push(v_orders_2327_, v___x_2319_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 6, v___x_2332_);
v___x_2334_ = v___x_2330_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_exp_2321_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_rings_2322_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_semirings_2323_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_ncRings_2324_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_ncSemirings_2325_);
lean_ctor_set(v_reuseFailAlloc_2335_, 5, v_typeClassify_2326_);
lean_ctor_set(v_reuseFailAlloc_2335_, 6, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2335_, 7, v_typeOrderClassify_2328_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(lean_object* v_type_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2359_ = l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default;
v___x_2360_ = l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
v___x_2361_ = l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default;
v___x_2362_ = l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
lean_inc_ref(v_type_2351_);
v___x_2363_ = l_Lean_Meta_getDecLevel_x3f(v_type_2351_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2703_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2703_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2703_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
if (lean_obj_tag(v_a_2364_) == 1)
{
lean_object* v_val_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2698_; 
lean_del_object(v___x_2366_);
v_val_2368_ = lean_ctor_get(v_a_2364_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_a_2364_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2370_ = v_a_2364_;
v_isShared_2371_ = v_isSharedCheck_2698_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_val_2368_);
lean_dec(v_a_2364_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2698_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2372_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1));
v___x_2373_ = lean_box(0);
lean_inc(v_val_2368_);
v___x_2374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2374_, 0, v_val_2368_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
lean_inc_ref(v___x_2374_);
v___x_2375_ = l_Lean_mkConst(v___x_2372_, v___x_2374_);
lean_inc_ref(v_type_2351_);
v___x_2376_ = l_Lean_Expr_app___override(v___x_2375_, v_type_2351_);
v___x_2377_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2376_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2689_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2689_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2689_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
if (lean_obj_tag(v_a_2378_) == 1)
{
lean_object* v_val_2382_; lean_object* v___x_2383_; 
lean_del_object(v___x_2380_);
v_val_2382_ = lean_ctor_get(v_a_2378_, 0);
lean_inc(v_val_2382_);
lean_inc_ref(v_a_2378_);
lean_inc_ref(v_type_2351_);
lean_inc(v_val_2368_);
v___x_2383_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_val_2368_, v_type_2351_, v_a_2378_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2676_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2676_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2676_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
if (lean_obj_tag(v_a_2384_) == 1)
{
lean_object* v_val_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2671_; 
lean_del_object(v___x_2386_);
v_val_2388_ = lean_ctor_get(v_a_2384_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_a_2384_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2390_ = v_a_2384_;
v_isShared_2391_ = v_isSharedCheck_2671_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_val_2388_);
lean_dec(v_a_2384_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2671_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; 
lean_inc_ref(v_a_2378_);
lean_inc_ref(v_type_2351_);
lean_inc(v_val_2368_);
v___x_2392_ = l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(v_val_2368_, v_type_2351_, v_a_2378_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2394_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
lean_inc_ref(v_a_2378_);
lean_inc_ref(v_type_2351_);
lean_inc(v_val_2368_);
v___x_2394_ = l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f(v_val_2368_, v_type_2351_, v_a_2378_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v___x_2396_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3));
lean_inc_ref(v___x_2374_);
v___x_2397_ = l_Lean_mkConst(v___x_2396_, v___x_2374_);
lean_inc_ref(v_type_2351_);
v___x_2398_ = l_Lean_Expr_app___override(v___x_2397_, v_type_2351_);
v___x_2399_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2398_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v___x_2401_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5));
lean_inc_ref(v___x_2374_);
v___x_2402_ = l_Lean_mkConst(v___x_2401_, v___x_2374_);
lean_inc(v_val_2382_);
lean_inc_ref(v_type_2351_);
v___x_2403_ = l_Lean_mkAppB(v___x_2402_, v_type_2351_, v_val_2382_);
v___x_2404_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(v___x_2403_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v_fst_2409_; lean_object* v_fst_2410_; uint8_t v_fst_2411_; lean_object* v_fst_2412_; lean_object* v_fst_2413_; uint8_t v_snd_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v_fst_2453_; lean_object* v_snd_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
if (lean_obj_tag(v_a_2400_) == 1)
{
lean_object* v_val_2460_; lean_object* v___x_2461_; 
v_val_2460_ = lean_ctor_get(v_a_2400_, 0);
lean_inc_ref(v_a_2400_);
lean_inc_ref(v_type_2351_);
lean_inc(v_val_2368_);
v___x_2461_ = l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(v_val_2368_, v_type_2351_, v_a_2400_, v_a_2378_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref_known(v___x_2461_, 1);
if (lean_obj_tag(v_a_2462_) == 0)
{
lean_dec_ref_known(v___x_2374_, 2);
lean_del_object(v___x_2370_);
v_fst_2453_ = v_a_2462_;
v_snd_2454_ = v_a_2462_;
v___y_2455_ = v_a_2353_;
v___y_2456_ = v_a_2356_;
goto v___jp_2452_;
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2463_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7));
v___x_2464_ = l_Lean_mkConst(v___x_2463_, v___x_2374_);
lean_inc(v_val_2460_);
lean_inc_ref(v_type_2351_);
v___x_2465_ = l_Lean_mkAppB(v___x_2464_, v_type_2351_, v_val_2460_);
v___x_2466_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(v___x_2465_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v_a_2467_);
v___x_2469_ = v___x_2370_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2467_);
v___x_2469_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
uint8_t v___x_2470_; uint8_t v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = 0;
v___x_2471_ = 1;
lean_inc_ref(v_type_2351_);
v___x_2472_ = l_Lean_Meta_Sym_Arith_classify_x3f(v_type_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2472_, 1);
switch(lean_obj_tag(v_a_2473_))
{
case 0:
{
lean_object* v_id_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2509_; 
v_id_2474_ = lean_ctor_get(v_a_2473_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_a_2473_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2476_ = v_a_2473_;
v_isShared_2477_ = v_isSharedCheck_2509_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_id_2474_);
lean_dec(v_a_2473_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2509_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2353_, v_a_2356_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v_rings_2480_; lean_object* v___x_2481_; lean_object* v_toRing_2482_; lean_object* v_ringInst_2483_; lean_object* v_semiringInst_2484_; lean_object* v___x_2485_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2478_, 1);
v_rings_2480_ = lean_ctor_get(v_a_2479_, 1);
lean_inc_ref(v_rings_2480_);
lean_dec(v_a_2479_);
v___x_2481_ = lean_array_get(v___x_2359_, v_rings_2480_, v_id_2474_);
lean_dec_ref(v_rings_2480_);
v_toRing_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc_ref(v_toRing_2482_);
lean_dec(v___x_2481_);
v_ringInst_2483_ = lean_ctor_get(v_toRing_2482_, 3);
lean_inc_ref(v_ringInst_2483_);
v_semiringInst_2484_ = lean_ctor_get(v_toRing_2482_, 4);
lean_inc_ref(v_semiringInst_2484_);
lean_dec_ref(v_toRing_2482_);
lean_inc(v_val_2388_);
lean_inc(v_val_2460_);
lean_inc(v_val_2382_);
lean_inc_ref(v_type_2351_);
lean_inc(v_val_2368_);
v___x_2485_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2368_, v_type_2351_, v_semiringInst_2484_, v_val_2382_, v_val_2460_, v_val_2388_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref_known(v___x_2485_, 1);
if (lean_obj_tag(v_a_2486_) == 1)
{
lean_object* v___x_2488_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set_tag(v___x_2476_, 1);
v___x_2488_ = v___x_2476_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_id_2474_);
v___x_2488_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_box(0);
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_ringInst_2483_);
v___y_2407_ = v___x_2469_;
v___y_2408_ = v_a_2462_;
v_fst_2409_ = v___x_2488_;
v_fst_2410_ = v___x_2489_;
v_fst_2411_ = v___x_2471_;
v_fst_2412_ = v___x_2490_;
v_fst_2413_ = v_a_2486_;
v_snd_2414_ = v___x_2471_;
v___y_2415_ = v_a_2353_;
v___y_2416_ = v_a_2356_;
goto v___jp_2406_;
}
}
else
{
lean_object* v___x_2492_; 
lean_dec(v_a_2486_);
lean_dec_ref(v_ringInst_2483_);
lean_del_object(v___x_2476_);
lean_dec(v_id_2474_);
v___x_2492_ = lean_box(0);
v___y_2407_ = v___x_2469_;
v___y_2408_ = v_a_2462_;
v_fst_2409_ = v___x_2492_;
v_fst_2410_ = v___x_2492_;
v_fst_2411_ = v___x_2471_;
v_fst_2412_ = v___x_2492_;
v_fst_2413_ = v___x_2492_;
v_snd_2414_ = v___x_2471_;
v___y_2415_ = v_a_2353_;
v___y_2416_ = v_a_2356_;
goto v___jp_2406_;
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec_ref(v_ringInst_2483_);
lean_del_object(v___x_2476_);
lean_dec(v_id_2474_);
lean_dec_ref(v___x_2469_);
lean_dec_ref_known(v_a_2462_, 1);
lean_dec_ref_known(v_a_2400_, 1);
lean_dec(v_a_2405_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2493_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2485_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2485_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_del_object(v___x_2476_);
lean_dec(v_id_2474_);
lean_dec_ref(v___x_2469_);
lean_dec_ref_known(v_a_2462_, 1);
lean_dec_ref_known(v_a_2400_, 1);
lean_dec(v_a_2405_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2501_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2478_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2478_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
case 1:
{
lean_object* v_id_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2544_; 
v_id_2510_ = lean_ctor_get(v_a_2473_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_a_2473_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2512_ = v_a_2473_;
v_isShared_2513_ = v_isSharedCheck_2544_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_id_2510_);
lean_dec(v_a_2473_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2544_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2353_, v_a_2356_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v_ncRings_2516_; lean_object* v___x_2517_; lean_object* v_ringInst_2518_; lean_object* v_semiringInst_2519_; lean_object* v___x_2520_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v_ncRings_2516_ = lean_ctor_get(v_a_2515_, 3);
lean_inc_ref(v_ncRings_2516_);
lean_dec(v_a_2515_);
v___x_2517_ = lean_array_get(v___x_2360_, v_ncRings_2516_, v_id_2510_);
lean_dec_ref(v_ncRings_2516_);
v_ringInst_2518_ = lean_ctor_get(v___x_2517_, 3);
lean_inc_ref(v_ringInst_2518_);
v_semiringInst_2519_ = lean_ctor_get(v___x_2517_, 4);
lean_inc_ref(v_semiringInst_2519_);
lean_dec(v___x_2517_);
lean_inc(v_val_2388_);
lean_inc(v_val_2460_);
lean_inc(v_val_2382_);
lean_inc_ref(v_type_2351_);
lean_inc(v_val_2368_);
v___x_2520_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2368_, v_type_2351_, v_semiringInst_2519_, v_val_2382_, v_val_2460_, v_val_2388_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
if (lean_obj_tag(v_a_2521_) == 1)
{
lean_object* v___x_2523_; 
if (v_isShared_2513_ == 0)
{
v___x_2523_ = v___x_2512_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_id_2510_);
v___x_2523_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = lean_box(0);
v___x_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_ringInst_2518_);
v___y_2407_ = v___x_2469_;
v___y_2408_ = v_a_2462_;
v_fst_2409_ = v___x_2523_;
v_fst_2410_ = v___x_2524_;
v_fst_2411_ = v___x_2471_;
v_fst_2412_ = v___x_2525_;
v_fst_2413_ = v_a_2521_;
v_snd_2414_ = v___x_2470_;
v___y_2415_ = v_a_2353_;
v___y_2416_ = v_a_2356_;
goto v___jp_2406_;
}
}
else
{
lean_object* v___x_2527_; 
lean_dec(v_a_2521_);
lean_dec_ref(v_ringInst_2518_);
lean_del_object(v___x_2512_);
lean_dec(v_id_2510_);
v___x_2527_ = lean_box(0);
v___y_2407_ = v___x_2469_;
v___y_2408_ = v_a_2462_;
v_fst_2409_ = v___x_2527_;
v_fst_2410_ = v___x_2527_;
v_fst_2411_ = v___x_2471_;
v_fst_2412_ = v___x_2527_;
v_fst_2413_ = v___x_2527_;
v_snd_2414_ = v___x_2470_;
v___y_2415_ = v_a_2353_;
v___y_2416_ = v_a_2356_;
goto v___jp_2406_;
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec_ref(v_ringInst_2518_);
lean_del_object(v___x_2512_);
lean_dec(v_id_2510_);
lean_dec_ref(v___x_2469_);
lean_dec_ref_known(v_a_2462_, 1);
lean_dec_ref_known(v_a_2400_, 1);
lean_dec(v_a_2405_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2528_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2520_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2520_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_del_object(v___x_2512_);
lean_dec(v_id_2510_);
lean_dec_ref(v___x_2469_);
lean_dec_ref_known(v_a_2462_, 1);
lean_dec_ref_known(v_a_2400_, 1);
lean_dec(v_a_2405_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2536_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2514_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2514_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
case 2:
{
lean_object* v_id_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2578_; 
v_id_2545_ = lean_ctor_get(v_a_2473_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_a_2473_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2547_ = v_a_2473_;
v_isShared_2548_ = v_isSharedCheck_2578_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_id_2545_);
lean_dec(v_a_2473_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2578_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2353_, v_a_2356_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v_semirings_2551_; lean_object* v___x_2552_; lean_object* v_toSemiring_2553_; lean_object* v_semiringInst_2554_; lean_object* v___x_2555_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
v_semirings_2551_ = lean_ctor_get(v_a_2550_, 2);
lean_inc_ref(v_semirings_2551_);
lean_dec(v_a_2550_);
v___x_2552_ = lean_array_get(v___x_2361_, v_semirings_2551_, v_id_2545_);
lean_dec_ref(v_semirings_2551_);
v_toSemiring_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc_ref(v_toSemiring_2553_);
lean_dec(v___x_2552_);
v_semiringInst_2554_ = lean_ctor_get(v_toSemiring_2553_, 3);
lean_inc_ref(v_semiringInst_2554_);
lean_dec_ref(v_toSemiring_2553_);
lean_inc(v_val_2388_);
lean_inc(v_val_2460_);
lean_inc(v_val_2382_);
lean_inc_ref(v_type_2351_);
lean_inc(v_val_2368_);
v___x_2555_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2368_, v_type_2351_, v_semiringInst_2554_, v_val_2382_, v_val_2460_, v_val_2388_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
if (lean_obj_tag(v_a_2556_) == 1)
{
lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2557_ = lean_box(0);
if (v_isShared_2548_ == 0)
{
lean_ctor_set_tag(v___x_2547_, 1);
v___x_2559_ = v___x_2547_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_id_2545_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
v___y_2407_ = v___x_2469_;
v___y_2408_ = v_a_2462_;
v_fst_2409_ = v___x_2557_;
v_fst_2410_ = v___x_2559_;
v_fst_2411_ = v___x_2471_;
v_fst_2412_ = v___x_2557_;
v_fst_2413_ = v_a_2556_;
v_snd_2414_ = v___x_2470_;
v___y_2415_ = v_a_2353_;
v___y_2416_ = v_a_2356_;
goto v___jp_2406_;
}
}
else
{
lean_object* v___x_2561_; 
lean_dec(v_a_2556_);
lean_del_object(v___x_2547_);
lean_dec(v_id_2545_);
v___x_2561_ = lean_box(0);
v___y_2407_ = v___x_2469_;
v___y_2408_ = v_a_2462_;
v_fst_2409_ = v___x_2561_;
v_fst_2410_ = v___x_2561_;
v_fst_2411_ = v___x_2471_;
v_fst_2412_ = v___x_2561_;
v_fst_2413_ = v___x_2561_;
v_snd_2414_ = v___x_2470_;
v___y_2415_ = v_a_2353_;
v___y_2416_ = v_a_2356_;
goto v___jp_2406_;
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_del_object(v___x_2547_);
lean_dec(v_id_2545_);
lean_dec_ref(v___x_2469_);
lean_dec_ref_known(v_a_2462_, 1);
lean_dec_ref_known(v_a_2400_, 1);
lean_dec(v_a_2405_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2562_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2555_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2555_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_del_object(v___x_2547_);
lean_dec(v_id_2545_);
lean_dec_ref(v___x_2469_);
lean_dec_ref_known(v_a_2462_, 1);
lean_dec_ref_known(v_a_2400_, 1);
lean_dec(v_a_2405_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2570_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2549_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2549_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
case 3:
{
lean_object* v_id_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2611_; 
v_id_2579_ = lean_ctor_get(v_a_2473_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_a_2473_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2581_ = v_a_2473_;
v_isShared_2582_ = v_isSharedCheck_2611_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_id_2579_);
lean_dec(v_a_2473_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2611_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2353_, v_a_2356_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v_ncSemirings_2585_; lean_object* v___x_2586_; lean_object* v_semiringInst_2587_; lean_object* v___x_2588_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v_ncSemirings_2585_ = lean_ctor_get(v_a_2584_, 4);
lean_inc_ref(v_ncSemirings_2585_);
lean_dec(v_a_2584_);
v___x_2586_ = lean_array_get(v___x_2362_, v_ncSemirings_2585_, v_id_2579_);
lean_dec_ref(v_ncSemirings_2585_);
v_semiringInst_2587_ = lean_ctor_get(v___x_2586_, 3);
lean_inc_ref(v_semiringInst_2587_);
lean_dec(v___x_2586_);
lean_inc(v_val_2388_);
lean_inc(v_val_2460_);
lean_inc(v_val_2382_);
lean_inc_ref(v_type_2351_);
lean_inc(v_val_2368_);
v___x_2588_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2368_, v_type_2351_, v_semiringInst_2587_, v_val_2382_, v_val_2460_, v_val_2388_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
if (lean_obj_tag(v_a_2589_) == 1)
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
v___x_2590_ = lean_box(0);
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 1);
v___x_2592_ = v___x_2581_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_id_2579_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
v___y_2407_ = v___x_2469_;
v___y_2408_ = v_a_2462_;
v_fst_2409_ = v___x_2590_;
v_fst_2410_ = v___x_2592_;
v_fst_2411_ = v___x_2470_;
v_fst_2412_ = v___x_2590_;
v_fst_2413_ = v_a_2589_;
v_snd_2414_ = v___x_2470_;
v___y_2415_ = v_a_2353_;
v___y_2416_ = v_a_2356_;
goto v___jp_2406_;
}
}
else
{
lean_object* v___x_2594_; 
lean_dec(v_a_2589_);
lean_del_object(v___x_2581_);
lean_dec(v_id_2579_);
v___x_2594_ = lean_box(0);
v___y_2407_ = v___x_2469_;
v___y_2408_ = v_a_2462_;
v_fst_2409_ = v___x_2594_;
v_fst_2410_ = v___x_2594_;
v_fst_2411_ = v___x_2471_;
v_fst_2412_ = v___x_2594_;
v_fst_2413_ = v___x_2594_;
v_snd_2414_ = v___x_2470_;
v___y_2415_ = v_a_2353_;
v___y_2416_ = v_a_2356_;
goto v___jp_2406_;
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_del_object(v___x_2581_);
lean_dec(v_id_2579_);
lean_dec_ref(v___x_2469_);
lean_dec_ref_known(v_a_2462_, 1);
lean_dec_ref_known(v_a_2400_, 1);
lean_dec(v_a_2405_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2595_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2588_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2588_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_del_object(v___x_2581_);
lean_dec(v_id_2579_);
lean_dec_ref(v___x_2469_);
lean_dec_ref_known(v_a_2462_, 1);
lean_dec_ref_known(v_a_2400_, 1);
lean_dec(v_a_2405_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2603_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2583_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2583_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
default: 
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_box(0);
v___y_2407_ = v___x_2469_;
v___y_2408_ = v_a_2462_;
v_fst_2409_ = v___x_2612_;
v_fst_2410_ = v___x_2612_;
v_fst_2411_ = v___x_2471_;
v_fst_2412_ = v___x_2612_;
v_fst_2413_ = v___x_2612_;
v_snd_2414_ = v___x_2470_;
v___y_2415_ = v_a_2353_;
v___y_2416_ = v_a_2356_;
goto v___jp_2406_;
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v___x_2469_);
lean_dec_ref_known(v_a_2462_, 1);
lean_dec_ref_known(v_a_2400_, 1);
lean_dec(v_a_2405_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2613_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2472_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2472_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec_ref_known(v_a_2462_, 1);
lean_dec_ref_known(v_a_2400_, 1);
lean_dec(v_a_2405_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_del_object(v___x_2370_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2622_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2466_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2466_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec_ref_known(v_a_2400_, 1);
lean_dec(v_a_2405_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec_ref_known(v___x_2374_, 2);
lean_del_object(v___x_2370_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2630_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2461_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2461_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_object* v___x_2638_; 
lean_dec_ref_known(v_a_2378_, 1);
lean_dec_ref_known(v___x_2374_, 2);
lean_del_object(v___x_2370_);
v___x_2638_ = lean_box(0);
v_fst_2453_ = v___x_2638_;
v_snd_2454_ = v___x_2638_;
v___y_2455_ = v_a_2353_;
v___y_2456_ = v_a_2356_;
goto v___jp_2452_;
}
v___jp_2406_:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v_orders_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___f_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v_orders_2419_ = lean_ctor_get(v_a_2418_, 6);
lean_inc_ref(v_orders_2419_);
lean_dec(v_a_2418_);
v___x_2420_ = lean_array_get_size(v_orders_2419_);
lean_dec_ref(v_orders_2419_);
v___x_2421_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
lean_ctor_set(v___x_2421_, 1, v_type_2351_);
lean_ctor_set(v___x_2421_, 2, v_val_2368_);
lean_ctor_set(v___x_2421_, 3, v_val_2388_);
lean_ctor_set(v___x_2421_, 4, v_val_2382_);
lean_ctor_set(v___x_2421_, 5, v_a_2400_);
lean_ctor_set(v___x_2421_, 6, v_a_2393_);
lean_ctor_set(v___x_2421_, 7, v_a_2395_);
lean_ctor_set(v___x_2421_, 8, v___y_2408_);
lean_ctor_set(v___x_2421_, 9, v_fst_2409_);
lean_ctor_set(v___x_2421_, 10, v_fst_2410_);
lean_ctor_set(v___x_2421_, 11, v_fst_2412_);
lean_ctor_set(v___x_2421_, 12, v_fst_2413_);
lean_ctor_set(v___x_2421_, 13, v_a_2405_);
lean_ctor_set(v___x_2421_, 14, v___y_2407_);
lean_ctor_set_uint8(v___x_2421_, sizeof(void*)*15, v_snd_2414_);
lean_ctor_set_uint8(v___x_2421_, sizeof(void*)*15 + 1, v_fst_2411_);
v___f_2422_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___lam__0), 2, 1);
lean_closure_set(v___f_2422_, 0, v___x_2421_);
v___x_2423_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2424_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2423_, v___f_2422_, v___y_2415_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2434_; 
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2434_ == 0)
{
lean_object* v_unused_2435_; 
v_unused_2435_ = lean_ctor_get(v___x_2424_, 0);
lean_dec(v_unused_2435_);
v___x_2426_ = v___x_2424_;
v_isShared_2427_ = v_isSharedCheck_2434_;
goto v_resetjp_2425_;
}
else
{
lean_dec(v___x_2424_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2434_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2420_);
v___x_2429_ = v___x_2390_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2420_);
v___x_2429_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2431_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2429_);
v___x_2431_ = v___x_2426_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_del_object(v___x_2390_);
v_a_2436_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2424_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2424_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v_fst_2413_);
lean_dec(v_fst_2412_);
lean_dec(v_fst_2410_);
lean_dec(v_fst_2409_);
lean_dec(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec(v_a_2405_);
lean_dec(v_a_2400_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2444_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2417_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2417_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
v___jp_2452_:
{
uint8_t v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2457_ = 1;
v___x_2458_ = lean_box(0);
v___x_2459_ = 0;
lean_inc_n(v_fst_2453_, 2);
v___y_2407_ = v_snd_2454_;
v___y_2408_ = v_fst_2453_;
v_fst_2409_ = v___x_2458_;
v_fst_2410_ = v___x_2458_;
v_fst_2411_ = v___x_2457_;
v_fst_2412_ = v_fst_2453_;
v_fst_2413_ = v_fst_2453_;
v_snd_2414_ = v___x_2459_;
v___y_2415_ = v___y_2455_;
v___y_2416_ = v___y_2456_;
goto v___jp_2406_;
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v_a_2400_);
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec_ref_known(v_a_2378_, 1);
lean_dec_ref_known(v___x_2374_, 2);
lean_del_object(v___x_2370_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2639_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2404_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2404_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec(v_a_2395_);
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec_ref_known(v_a_2378_, 1);
lean_dec_ref_known(v___x_2374_, 2);
lean_del_object(v___x_2370_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2647_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2399_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2399_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec(v_a_2393_);
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec_ref_known(v_a_2378_, 1);
lean_dec_ref_known(v___x_2374_, 2);
lean_del_object(v___x_2370_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2655_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2394_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2394_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_del_object(v___x_2390_);
lean_dec(v_val_2388_);
lean_dec(v_val_2382_);
lean_dec_ref_known(v_a_2378_, 1);
lean_dec_ref_known(v___x_2374_, 2);
lean_del_object(v___x_2370_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2663_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2392_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2392_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
else
{
lean_object* v___x_2672_; lean_object* v___x_2674_; 
lean_dec(v_a_2384_);
lean_dec(v_val_2382_);
lean_dec_ref_known(v_a_2378_, 1);
lean_dec_ref_known(v___x_2374_, 2);
lean_del_object(v___x_2370_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v___x_2672_ = lean_box(0);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2672_);
v___x_2674_ = v___x_2386_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec(v_val_2382_);
lean_dec_ref_known(v_a_2378_, 1);
lean_dec_ref_known(v___x_2374_, 2);
lean_del_object(v___x_2370_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2677_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2383_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2383_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2687_; 
lean_dec(v_a_2378_);
lean_dec_ref_known(v___x_2374_, 2);
lean_del_object(v___x_2370_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v___x_2685_ = lean_box(0);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2685_);
v___x_2687_ = v___x_2380_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec_ref_known(v___x_2374_, 2);
lean_del_object(v___x_2370_);
lean_dec(v_val_2368_);
lean_dec_ref(v_type_2351_);
v_a_2690_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2377_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2377_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_dec(v_a_2364_);
lean_dec_ref(v_type_2351_);
v___x_2699_ = lean_box(0);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2699_);
v___x_2701_ = v___x_2366_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v_type_2351_);
v_a_2704_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2363_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2363_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___boxed(lean_object* v_type_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(v_type_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___lam__0(lean_object* v_type_2721_, lean_object* v_a_2722_, lean_object* v_s_2723_){
_start:
{
lean_object* v_exp_2724_; lean_object* v_rings_2725_; lean_object* v_semirings_2726_; lean_object* v_ncRings_2727_; lean_object* v_ncSemirings_2728_; lean_object* v_typeClassify_2729_; lean_object* v_orders_2730_; lean_object* v_typeOrderClassify_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2739_; 
v_exp_2724_ = lean_ctor_get(v_s_2723_, 0);
v_rings_2725_ = lean_ctor_get(v_s_2723_, 1);
v_semirings_2726_ = lean_ctor_get(v_s_2723_, 2);
v_ncRings_2727_ = lean_ctor_get(v_s_2723_, 3);
v_ncSemirings_2728_ = lean_ctor_get(v_s_2723_, 4);
v_typeClassify_2729_ = lean_ctor_get(v_s_2723_, 5);
v_orders_2730_ = lean_ctor_get(v_s_2723_, 6);
v_typeOrderClassify_2731_ = lean_ctor_get(v_s_2723_, 7);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_s_2723_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2733_ = v_s_2723_;
v_isShared_2734_ = v_isSharedCheck_2739_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_typeOrderClassify_2731_);
lean_inc(v_orders_2730_);
lean_inc(v_typeClassify_2729_);
lean_inc(v_ncSemirings_2728_);
lean_inc(v_ncRings_2727_);
lean_inc(v_semirings_2726_);
lean_inc(v_rings_2725_);
lean_inc(v_exp_2724_);
lean_dec(v_s_2723_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2739_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2735_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeOrderClassify_2731_, v_type_2721_, v_a_2722_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 7, v___x_2735_);
v___x_2737_ = v___x_2733_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_exp_2724_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_rings_2725_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v_semirings_2726_);
lean_ctor_set(v_reuseFailAlloc_2738_, 3, v_ncRings_2727_);
lean_ctor_set(v_reuseFailAlloc_2738_, 4, v_ncSemirings_2728_);
lean_ctor_set(v_reuseFailAlloc_2738_, 5, v_typeClassify_2729_);
lean_ctor_set(v_reuseFailAlloc_2738_, 6, v_orders_2730_);
lean_ctor_set(v_reuseFailAlloc_2738_, 7, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f(lean_object* v_type_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2742_, v_a_2745_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2780_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2751_ = v___x_2748_;
v_isShared_2752_ = v_isSharedCheck_2780_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2780_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v_typeOrderClassify_2753_; lean_object* v___x_2754_; 
v_typeOrderClassify_2753_ = lean_ctor_get(v_a_2749_, 7);
lean_inc_ref(v_typeOrderClassify_2753_);
lean_dec(v_a_2749_);
v___x_2754_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeOrderClassify_2753_, v_type_2740_);
lean_dec_ref(v_typeOrderClassify_2753_);
if (lean_obj_tag(v___x_2754_) == 1)
{
lean_object* v_val_2755_; lean_object* v___x_2757_; 
lean_dec_ref(v_type_2740_);
v_val_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_val_2755_);
lean_dec_ref_known(v___x_2754_, 1);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v_val_2755_);
v___x_2757_ = v___x_2751_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_val_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
else
{
lean_object* v___x_2759_; 
lean_dec(v___x_2754_);
lean_del_object(v___x_2751_);
lean_inc_ref(v_type_2740_);
v___x_2759_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(v_type_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___f_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc_n(v_a_2760_, 2);
lean_dec_ref_known(v___x_2759_, 1);
v___f_2761_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_classifyOrder_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2761_, 0, v_type_2740_);
lean_closure_set(v___f_2761_, 1, v_a_2760_);
v___x_2762_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2763_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2762_, v___f_2761_, v_a_2742_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2770_ == 0)
{
lean_object* v_unused_2771_; 
v_unused_2771_ = lean_ctor_get(v___x_2763_, 0);
lean_dec(v_unused_2771_);
v___x_2765_ = v___x_2763_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_dec(v___x_2763_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v_a_2760_);
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2760_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v_a_2760_);
v_a_2772_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2763_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2763_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
else
{
lean_dec_ref(v_type_2740_);
return v___x_2759_;
}
}
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec_ref(v_type_2740_);
v_a_2781_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2748_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2748_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___boxed(lean_object* v_type_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_Meta_Sym_Arith_classifyOrder_x3f(v_type_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
return v_res_2797_;
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
